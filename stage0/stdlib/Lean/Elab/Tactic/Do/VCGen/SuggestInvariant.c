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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_collectForwardDeps(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkOr(lean_object*, lean_object*);
lean_object* l_Lean_mkAnd(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg(lean_object* v_type_49_, lean_object* v_a_50_){
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
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_49_ = stack[0].m_obj;
lean_object* v_a_50_ = stack[1].m_obj;
lean_object* v_res_110_;
v_res_110_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg(v_type_49_, v_a_50_);
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___boxed(lean_object* v_type_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg(v_type_111_, v_a_112_);
lean_dec_ref(v_a_112_);
return v_res_114_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget(lean_object* v_type_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg(v_type_115_, v_a_116_);
return v___x_121_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_115_ = stack[0].m_obj;
lean_object* v_a_116_ = stack[1].m_obj;
lean_object* v_a_117_ = stack[2].m_obj;
lean_object* v_a_118_ = stack[3].m_obj;
lean_object* v_a_119_ = stack[4].m_obj;
lean_object* v_res_122_;
v_res_122_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget(v_type_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_);
stack->m_obj
 = v_res_122_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed(lean_object* v_type_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget(v_type_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorIdx___impl(lean_object* v_x_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = lean_obj_tag_nat(v_x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorIdx___impl___boxed(lean_object* v_x_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorIdx___impl(v_x_132_);
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
v___x_296_ = lean_array_get_borrowed(v___x_294_, v___x_290_, v___x_295_);
lean_inc(v___x_296_);
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
lean_inc_ref(v_fst_285_);
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
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(lean_object* v_mvarId_366_, lean_object* v_x_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
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
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_366_ = stack[0].m_obj;
lean_object* v_x_367_ = stack[1].m_obj;
lean_object* v___y_368_ = stack[2].m_obj;
lean_object* v___y_369_ = stack[3].m_obj;
lean_object* v___y_370_ = stack[4].m_obj;
lean_object* v___y_371_ = stack[5].m_obj;
lean_object* v_res_390_;
v_res_390_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_mvarId_366_, v_x_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg___boxed(lean_object* v_mvarId_391_, lean_object* v_x_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_mvarId_391_, v_x_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
return v_res_398_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0(lean_object* v_00_u03b1_399_, lean_object* v_mvarId_400_, lean_object* v_x_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_mvarId_400_, v_x_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
return v___x_407_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_400_ = stack[1].m_obj;
lean_object* v_x_401_ = stack[2].m_obj;
lean_object* v___y_402_ = stack[3].m_obj;
lean_object* v___y_403_ = stack[4].m_obj;
lean_object* v___y_404_ = stack[5].m_obj;
lean_object* v___y_405_ = stack[6].m_obj;
lean_object* v_res_408_;
v_res_408_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0(lean_box(0), v_mvarId_400_, v_x_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
stack->m_obj
 = v_res_408_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___boxed(lean_object* v_00_u03b1_409_, lean_object* v_mvarId_410_, lean_object* v_x_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0(v_00_u03b1_409_, v_mvarId_410_, v_x_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
return v_res_417_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(lean_object* v_e_418_, lean_object* v___y_419_){
_start:
{
uint8_t v___x_421_; 
v___x_421_ = l_Lean_Expr_hasMVar(v_e_418_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; 
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v_e_418_);
return v___x_422_;
}
else
{
lean_object* v___x_423_; lean_object* v_mctx_424_; lean_object* v___x_425_; lean_object* v_fst_426_; lean_object* v_snd_427_; lean_object* v___x_428_; lean_object* v_cache_429_; lean_object* v_zetaDeltaFVarIds_430_; lean_object* v_postponed_431_; lean_object* v_diag_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_441_; 
v___x_423_ = lean_st_ref_get(v___y_419_);
v_mctx_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc_ref(v_mctx_424_);
lean_dec(v___x_423_);
v___x_425_ = l_Lean_instantiateMVarsCore(v_mctx_424_, v_e_418_);
v_fst_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_fst_426_);
v_snd_427_ = lean_ctor_get(v___x_425_, 1);
lean_inc(v_snd_427_);
lean_dec_ref(v___x_425_);
v___x_428_ = lean_st_ref_take(v___y_419_);
v_cache_429_ = lean_ctor_get(v___x_428_, 1);
v_zetaDeltaFVarIds_430_ = lean_ctor_get(v___x_428_, 2);
v_postponed_431_ = lean_ctor_get(v___x_428_, 3);
v_diag_432_ = lean_ctor_get(v___x_428_, 4);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_441_ == 0)
{
lean_object* v_unused_442_; 
v_unused_442_ = lean_ctor_get(v___x_428_, 0);
lean_dec(v_unused_442_);
v___x_434_ = v___x_428_;
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_diag_432_);
lean_inc(v_postponed_431_);
lean_inc(v_zetaDeltaFVarIds_430_);
lean_inc(v_cache_429_);
lean_dec(v___x_428_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v_snd_427_);
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_snd_427_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_cache_429_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_zetaDeltaFVarIds_430_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v_postponed_431_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v_diag_432_);
v___x_437_ = v_reuseFailAlloc_440_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_st_ref_put(v___y_419_, v___x_437_);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v_fst_426_);
return v___x_439_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_418_ = stack[0].m_obj;
lean_object* v___y_419_ = stack[1].m_obj;
lean_object* v_res_443_;
v_res_443_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_e_418_, v___y_419_);
stack->m_obj
 = v_res_443_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg___boxed(lean_object* v_e_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_e_444_, v___y_445_);
lean_dec(v___y_445_);
return v_res_447_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1(lean_object* v_e_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_e_448_, v___y_450_);
return v___x_454_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_448_ = stack[0].m_obj;
lean_object* v___y_449_ = stack[1].m_obj;
lean_object* v___y_450_ = stack[2].m_obj;
lean_object* v___y_451_ = stack[3].m_obj;
lean_object* v___y_452_ = stack[4].m_obj;
lean_object* v_res_455_;
v_res_455_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1(v_e_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
stack->m_obj
 = v_res_455_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(lean_object* v_inv_480_, uint8_t v___x_481_, lean_object* v_as_482_, size_t v_sz_483_, size_t v_i_484_, lean_object* v_b_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_a_492_; uint8_t v___x_496_; 
v___x_496_ = lean_usize_dec_lt(v_i_484_, v_sz_483_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; 
lean_dec(v_inv_480_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v_b_485_);
return v___x_497_;
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v_a_500_; lean_object* v_a_502_; lean_object* v___x_539_; 
lean_dec_ref(v_b_485_);
v___x_498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__0));
v___x_499_ = l_Lean_instInhabitedExpr;
v_a_500_ = lean_array_uget_borrowed(v_as_482_, v_i_484_);
lean_inc(v_a_500_);
v___x_539_ = l_Lean_MVarId_getType(v_a_500_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_541_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref_known(v___x_539_, 1);
v___x_541_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_a_540_, v___y_487_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_543_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref_known(v___x_541_, 1);
v___x_543_ = l_Lean_Expr_consumeMData(v_a_542_);
lean_dec(v_a_542_);
v_a_502_ = v___x_543_;
goto v___jp_501_;
}
else
{
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_544_; 
v_a_544_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_544_);
lean_dec_ref_known(v___x_541_, 1);
v_a_502_ = v_a_544_;
goto v___jp_501_;
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec(v_inv_480_);
v_a_545_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_541_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_541_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec(v_inv_480_);
v_a_553_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_539_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_539_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
v___jp_501_:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed), 6, 1);
lean_closure_set(v___x_503_, 0, v_a_502_);
lean_inc(v_a_500_);
v___x_504_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_500_, v___x_503_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_530_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_530_ == 0)
{
v___x_507_ = v___x_504_;
v_isShared_508_ = v_isSharedCheck_530_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_504_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_530_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
if (lean_obj_tag(v_a_505_) == 1)
{
lean_object* v_val_509_; lean_object* v_snd_510_; lean_object* v_snd_511_; lean_object* v___x_512_; 
v_val_509_ = lean_ctor_get(v_a_505_, 0);
lean_inc(v_val_509_);
lean_dec_ref_known(v_a_505_, 1);
v_snd_510_ = lean_ctor_get(v_val_509_, 1);
lean_inc(v_snd_510_);
lean_dec(v_val_509_);
v_snd_511_ = lean_ctor_get(v_snd_510_, 1);
lean_inc(v_snd_511_);
lean_dec(v_snd_510_);
lean_inc(v_inv_480_);
v___x_512_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_snd_511_, v_inv_480_);
lean_dec(v_snd_511_);
switch(lean_obj_tag(v___x_512_))
{
case 0:
{
lean_object* v_invariantUse_513_; lean_object* v_cursorSuffix_514_; lean_object* v_letMuts_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v_invariantUse_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc_ref(v_invariantUse_513_);
lean_dec_ref_known(v___x_512_, 1);
v_cursorSuffix_514_ = lean_ctor_get(v_invariantUse_513_, 2);
lean_inc_ref(v_cursorSuffix_514_);
v_letMuts_515_ = lean_ctor_get(v_invariantUse_513_, 3);
lean_inc_ref(v_letMuts_515_);
lean_dec_ref(v_invariantUse_513_);
v___x_516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2));
v___x_517_ = l_Lean_Expr_isAppOf(v_cursorSuffix_514_, v___x_516_);
lean_dec_ref(v_cursorSuffix_514_);
if (v___x_517_ == 0)
{
if (v___x_481_ == 0)
{
lean_dec_ref(v_letMuts_515_);
lean_del_object(v___x_507_);
v_a_492_ = v___x_498_;
goto v___jp_491_;
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_518_ = lean_unsigned_to_nat(0u);
v___x_519_ = lean_array_get(v___x_499_, v_letMuts_515_, v___x_518_);
lean_dec_ref(v_letMuts_515_);
v___x_520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5));
v___x_521_ = l_Lean_Expr_isAppOf(v___x_519_, v___x_520_);
lean_dec(v___x_519_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_524_; 
lean_dec(v_inv_480_);
v___x_522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7));
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_522_);
v___x_524_ = v___x_507_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
else
{
lean_del_object(v___x_507_);
v_a_492_ = v___x_498_;
goto v___jp_491_;
}
}
}
else
{
lean_dec_ref(v_letMuts_515_);
lean_del_object(v___x_507_);
v_a_492_ = v___x_498_;
goto v___jp_491_;
}
}
case 1:
{
lean_del_object(v___x_507_);
v_a_492_ = v___x_498_;
goto v___jp_491_;
}
default: 
{
lean_object* v___x_526_; lean_object* v___x_528_; 
lean_dec(v_inv_480_);
v___x_526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7));
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_526_);
v___x_528_ = v___x_507_;
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
lean_del_object(v___x_507_);
lean_dec(v_a_505_);
v_a_492_ = v___x_498_;
goto v___jp_491_;
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec(v_inv_480_);
v_a_531_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_504_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_504_);
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
v___jp_491_:
{
size_t v___x_493_; size_t v___x_494_; 
v___x_493_ = ((size_t)1ULL);
v___x_494_ = lean_usize_add(v_i_484_, v___x_493_);
lean_inc_ref(v_a_492_);
v_i_484_ = v___x_494_;
v_b_485_ = v_a_492_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_inv_480_ = stack[0].m_obj;
uint8_t v___x_481_ = stack[1].m_num;
lean_object* v_as_482_ = stack[2].m_obj;
size_t v_sz_483_ = stack[3].m_num;
size_t v_i_484_ = stack[4].m_num;
lean_object* v_b_485_ = stack[5].m_obj;
lean_object* v___y_486_ = stack[6].m_obj;
lean_object* v___y_487_ = stack[7].m_obj;
lean_object* v___y_488_ = stack[8].m_obj;
lean_object* v___y_489_ = stack[9].m_obj;
lean_object* v_res_561_;
v_res_561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(v_inv_480_, v___x_481_, v_as_482_, v_sz_483_, v_i_484_, v_b_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
stack->m_obj
 = v_res_561_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___boxed(lean_object* v_inv_562_, lean_object* v___x_563_, lean_object* v_as_564_, lean_object* v_sz_565_, lean_object* v_i_566_, lean_object* v_b_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
uint8_t v___x_4534__boxed_573_; size_t v_sz_boxed_574_; size_t v_i_boxed_575_; lean_object* v_res_576_; 
v___x_4534__boxed_573_ = lean_unbox(v___x_563_);
v_sz_boxed_574_ = lean_unbox_usize(v_sz_565_);
lean_dec(v_sz_565_);
v_i_boxed_575_ = lean_unbox_usize(v_i_566_);
lean_dec(v_i_566_);
v_res_576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(v_inv_562_, v___x_4534__boxed_573_, v_as_564_, v_sz_boxed_574_, v_i_boxed_575_, v_b_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec_ref(v_as_564_);
return v_res_576_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(lean_object* v_vcs_581_, lean_object* v_inv_582_, lean_object* v_letMutsTy_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0));
v___x_596_ = l_Lean_Expr_isAppOf(v_letMutsTy_583_, v___x_595_);
if (v___x_596_ == 0)
{
lean_dec(v_inv_582_);
goto v___jp_589_;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_597_ = l_Lean_Expr_getAppNumArgs(v_letMutsTy_583_);
v___x_598_ = lean_unsigned_to_nat(2u);
v___x_599_ = lean_nat_dec_lt(v___x_597_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = lean_nat_sub(v___x_597_, v___x_600_);
lean_dec(v___x_597_);
lean_inc(v___x_601_);
v___x_602_ = l_Lean_Expr_getRevArg_x21(v_letMutsTy_583_, v___x_601_);
v___x_603_ = l_Lean_Expr_cleanupAnnotations(v___x_602_);
v___x_604_ = l_Lean_Expr_isApp(v___x_603_);
if (v___x_604_ == 0)
{
lean_dec_ref(v___x_603_);
lean_dec(v___x_601_);
lean_dec(v_inv_582_);
goto v___jp_592_;
}
else
{
lean_object* v_arg_605_; lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v_arg_605_ = lean_ctor_get(v___x_603_, 1);
lean_inc_ref(v_arg_605_);
v___x_606_ = l_Lean_Expr_appFnCleanup___redArg(v___x_603_);
v___x_607_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1));
v___x_608_ = l_Lean_Expr_isConstOf(v___x_606_, v___x_607_);
lean_dec_ref(v___x_606_);
if (v___x_608_ == 0)
{
lean_dec_ref(v_arg_605_);
lean_dec(v___x_601_);
lean_dec(v_inv_582_);
goto v___jp_592_;
}
else
{
lean_object* v___x_609_; lean_object* v_00_u03c3_610_; lean_object* v___x_611_; size_t v_sz_612_; size_t v___x_613_; lean_object* v___x_614_; 
v___x_609_ = lean_nat_sub(v___x_601_, v___x_600_);
lean_dec(v___x_601_);
v_00_u03c3_610_ = l_Lean_Expr_getRevArg_x21(v_letMutsTy_583_, v___x_609_);
v___x_611_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__0));
v_sz_612_ = lean_array_size(v_vcs_581_);
v___x_613_ = ((size_t)0ULL);
v___x_614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(v_inv_582_, v___x_608_, v_vcs_581_, v_sz_612_, v___x_613_, v___x_611_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_636_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_636_ == 0)
{
v___x_617_ = v___x_614_;
v_isShared_618_ = v_isSharedCheck_636_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_636_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v_fst_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_634_; 
v_fst_619_ = lean_ctor_get(v_a_615_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v_a_615_);
if (v_isSharedCheck_634_ == 0)
{
lean_object* v_unused_635_; 
v_unused_635_ = lean_ctor_get(v_a_615_, 1);
lean_dec(v_unused_635_);
v___x_621_ = v_a_615_;
v_isShared_622_ = v_isSharedCheck_634_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_fst_619_);
lean_dec(v_a_615_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_634_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
if (lean_obj_tag(v_fst_619_) == 0)
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v_00_u03c3_610_);
lean_ctor_set(v___x_621_, 0, v_arg_605_);
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_arg_605_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_00_u03c3_610_);
v___x_624_ = v_reuseFailAlloc_629_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_625_);
v___x_627_ = v___x_617_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
else
{
lean_object* v_val_630_; lean_object* v___x_632_; 
lean_del_object(v___x_621_);
lean_dec_ref(v_00_u03c3_610_);
lean_dec_ref(v_arg_605_);
v_val_630_ = lean_ctor_get(v_fst_619_, 0);
lean_inc(v_val_630_);
lean_dec_ref_known(v_fst_619_, 1);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v_val_630_);
v___x_632_ = v___x_617_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_val_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec_ref(v_00_u03c3_610_);
lean_dec_ref(v_arg_605_);
v_a_637_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_614_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_614_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
}
else
{
lean_dec(v___x_597_);
lean_dec(v_inv_582_);
goto v___jp_589_;
}
}
v___jp_589_:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_box(0);
v___x_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
return v___x_591_;
}
v___jp_592_:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = lean_box(0);
v___x_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
return v___x_594_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_0interp(lean_interpreter_value* stack)
{
lean_object* v_vcs_581_ = stack[0].m_obj;
lean_object* v_inv_582_ = stack[1].m_obj;
lean_object* v_letMutsTy_583_ = stack[2].m_obj;
lean_object* v_a_584_ = stack[3].m_obj;
lean_object* v_a_585_ = stack[4].m_obj;
lean_object* v_a_586_ = stack[5].m_obj;
lean_object* v_a_587_ = stack[6].m_obj;
lean_object* v_res_645_;
v_res_645_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(v_vcs_581_, v_inv_582_, v_letMutsTy_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
stack->m_obj
 = v_res_645_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___boxed(lean_object* v_vcs_646_, lean_object* v_inv_647_, lean_object* v_letMutsTy_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(v_vcs_646_, v_inv_647_, v_letMutsTy_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec_ref(v_letMutsTy_648_);
lean_dec_ref(v_vcs_646_);
return v_res_654_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(lean_object* v_dontRevert_655_, lean_object* v_as_656_, size_t v_i_657_, size_t v_stop_658_, lean_object* v_b_659_){
_start:
{
lean_object* v___y_661_; uint8_t v___x_665_; 
v___x_665_ = lean_usize_dec_eq(v_i_657_, v_stop_658_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_666_ = lean_array_uget_borrowed(v_as_656_, v_i_657_);
lean_inc_ref(v_dontRevert_655_);
lean_inc(v___x_666_);
v___x_667_ = lean_apply_1(v_dontRevert_655_, v___x_666_);
v___x_668_ = lean_unbox(v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
lean_inc(v___x_666_);
v___x_669_ = lean_array_push(v_b_659_, v___x_666_);
v___y_661_ = v___x_669_;
goto v___jp_660_;
}
else
{
v___y_661_ = v_b_659_;
goto v___jp_660_;
}
}
else
{
lean_dec_ref(v_dontRevert_655_);
return v_b_659_;
}
v___jp_660_:
{
size_t v___x_662_; size_t v___x_663_; 
v___x_662_ = ((size_t)1ULL);
v___x_663_ = lean_usize_add(v_i_657_, v___x_662_);
v_i_657_ = v___x_663_;
v_b_659_ = v___y_661_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_dontRevert_655_ = stack[0].m_obj;
lean_object* v_as_656_ = stack[1].m_obj;
size_t v_i_657_ = stack[2].m_num;
size_t v_stop_658_ = stack[3].m_num;
lean_object* v_b_659_ = stack[4].m_obj;
lean_object* v_res_670_;
v_res_670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_655_, v_as_656_, v_i_657_, v_stop_658_, v_b_659_);
stack->m_obj
 = v_res_670_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2___boxed(lean_object* v_dontRevert_671_, lean_object* v_as_672_, lean_object* v_i_673_, lean_object* v_stop_674_, lean_object* v_b_675_){
_start:
{
size_t v_i_boxed_676_; size_t v_stop_boxed_677_; lean_object* v_res_678_; 
v_i_boxed_676_ = lean_unbox_usize(v_i_673_);
lean_dec(v_i_673_);
v_stop_boxed_677_ = lean_unbox_usize(v_stop_674_);
lean_dec(v_stop_674_);
v_res_678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_671_, v_as_672_, v_i_boxed_676_, v_stop_boxed_677_, v_b_675_);
lean_dec_ref(v_as_672_);
return v_res_678_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(size_t v_sz_679_, size_t v_i_680_, lean_object* v_bs_681_){
_start:
{
uint8_t v___x_682_; 
v___x_682_ = lean_usize_dec_lt(v_i_680_, v_sz_679_);
if (v___x_682_ == 0)
{
return v_bs_681_;
}
else
{
lean_object* v_v_683_; lean_object* v___x_684_; lean_object* v_bs_x27_685_; lean_object* v___x_686_; size_t v___x_687_; size_t v___x_688_; lean_object* v___x_689_; 
v_v_683_ = lean_array_uget(v_bs_681_, v_i_680_);
v___x_684_ = lean_unsigned_to_nat(0u);
v_bs_x27_685_ = lean_array_uset(v_bs_681_, v_i_680_, v___x_684_);
v___x_686_ = l_Lean_mkFVar(v_v_683_);
v___x_687_ = ((size_t)1ULL);
v___x_688_ = lean_usize_add(v_i_680_, v___x_687_);
v___x_689_ = lean_array_uset(v_bs_x27_685_, v_i_680_, v___x_686_);
v_i_680_ = v___x_688_;
v_bs_681_ = v___x_689_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_679_ = stack[0].m_num;
size_t v_i_680_ = stack[1].m_num;
lean_object* v_bs_681_ = stack[2].m_obj;
lean_object* v_res_691_;
v_res_691_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_679_, v_i_680_, v_bs_681_);
stack->m_obj
 = v_res_691_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1___boxed(lean_object* v_sz_692_, lean_object* v_i_693_, lean_object* v_bs_694_){
_start:
{
size_t v_sz_boxed_695_; size_t v_i_boxed_696_; lean_object* v_res_697_; 
v_sz_boxed_695_ = lean_unbox_usize(v_sz_692_);
lean_dec(v_sz_692_);
v_i_boxed_696_ = lean_unbox_usize(v_i_693_);
lean_dec(v_i_693_);
v_res_697_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_boxed_695_, v_i_boxed_696_, v_bs_694_);
return v_res_697_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(size_t v_sz_698_, size_t v_i_699_, lean_object* v_bs_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
uint8_t v___x_706_; 
v___x_706_ = lean_usize_dec_lt(v_i_699_, v_sz_698_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; 
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v_bs_700_);
return v___x_707_;
}
else
{
lean_object* v_v_708_; lean_object* v___x_709_; lean_object* v_bs_x27_710_; lean_object* v___x_711_; 
v_v_708_ = lean_array_uget(v_bs_700_, v_i_699_);
v___x_709_ = lean_unsigned_to_nat(0u);
v_bs_x27_710_ = lean_array_uset(v_bs_700_, v_i_699_, v___x_709_);
lean_inc(v___y_704_);
lean_inc_ref(v___y_703_);
lean_inc(v___y_702_);
lean_inc_ref(v___y_701_);
v___x_711_ = lean_infer_type(v_v_708_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; size_t v___x_713_; size_t v___x_714_; lean_object* v___x_715_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v___x_711_, 1);
v___x_713_ = ((size_t)1ULL);
v___x_714_ = lean_usize_add(v_i_699_, v___x_713_);
v___x_715_ = lean_array_uset(v_bs_x27_710_, v_i_699_, v_a_712_);
v_i_699_ = v___x_714_;
v_bs_700_ = v___x_715_;
goto _start;
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec_ref(v_bs_x27_710_);
v_a_717_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_711_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_711_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_698_ = stack[0].m_num;
size_t v_i_699_ = stack[1].m_num;
lean_object* v_bs_700_ = stack[2].m_obj;
lean_object* v___y_701_ = stack[3].m_obj;
lean_object* v___y_702_ = stack[4].m_obj;
lean_object* v___y_703_ = stack[5].m_obj;
lean_object* v___y_704_ = stack[6].m_obj;
lean_object* v_res_725_;
v_res_725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(v_sz_698_, v_i_699_, v_bs_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
stack->m_obj
 = v_res_725_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0___boxed(lean_object* v_sz_726_, lean_object* v_i_727_, lean_object* v_bs_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
size_t v_sz_boxed_734_; size_t v_i_boxed_735_; lean_object* v_res_736_; 
v_sz_boxed_734_ = lean_unbox_usize(v_sz_726_);
lean_dec(v_sz_726_);
v_i_boxed_735_ = lean_unbox_usize(v_i_727_);
lean_dec(v_i_727_);
v_res_736_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(v_sz_boxed_734_, v_i_boxed_735_, v_bs_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_736_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(lean_object* v_dontRevert_737_, lean_object* v_as_738_, size_t v_i_739_, size_t v_stop_740_, lean_object* v_b_741_){
_start:
{
lean_object* v___y_743_; uint8_t v___x_747_; 
v___x_747_ = lean_usize_dec_eq(v_i_739_, v_stop_740_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_748_ = lean_array_uget_borrowed(v_as_738_, v_i_739_);
v___x_749_ = l_Lean_Expr_fvarId_x21(v___x_748_);
lean_inc_ref(v_dontRevert_737_);
v___x_750_ = lean_apply_1(v_dontRevert_737_, v___x_749_);
v___x_751_ = lean_unbox(v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; 
lean_inc(v___x_748_);
v___x_752_ = lean_array_push(v_b_741_, v___x_748_);
v___y_743_ = v___x_752_;
goto v___jp_742_;
}
else
{
v___y_743_ = v_b_741_;
goto v___jp_742_;
}
}
else
{
lean_dec_ref(v_dontRevert_737_);
return v_b_741_;
}
v___jp_742_:
{
size_t v___x_744_; size_t v___x_745_; 
v___x_744_ = ((size_t)1ULL);
v___x_745_ = lean_usize_add(v_i_739_, v___x_744_);
v_i_739_ = v___x_745_;
v_b_741_ = v___y_743_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_dontRevert_737_ = stack[0].m_obj;
lean_object* v_as_738_ = stack[1].m_obj;
size_t v_i_739_ = stack[2].m_num;
size_t v_stop_740_ = stack[3].m_num;
lean_object* v_b_741_ = stack[4].m_obj;
lean_object* v_res_753_;
v_res_753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_737_, v_as_738_, v_i_739_, v_stop_740_, v_b_741_);
stack->m_obj
 = v_res_753_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5___boxed(lean_object* v_dontRevert_754_, lean_object* v_as_755_, lean_object* v_i_756_, lean_object* v_stop_757_, lean_object* v_b_758_){
_start:
{
size_t v_i_boxed_759_; size_t v_stop_boxed_760_; lean_object* v_res_761_; 
v_i_boxed_759_ = lean_unbox_usize(v_i_756_);
lean_dec(v_i_756_);
v_stop_boxed_760_ = lean_unbox_usize(v_stop_757_);
lean_dec(v_stop_757_);
v_res_761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_754_, v_as_755_, v_i_boxed_759_, v_stop_boxed_760_, v_b_758_);
lean_dec_ref(v_as_755_);
return v_res_761_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(lean_object* v_a_762_, lean_object* v_x_763_){
_start:
{
if (lean_obj_tag(v_x_763_) == 0)
{
uint8_t v___x_764_; 
v___x_764_ = 0;
return v___x_764_;
}
else
{
lean_object* v_key_765_; lean_object* v_tail_766_; uint8_t v___x_767_; 
v_key_765_ = lean_ctor_get(v_x_763_, 0);
v_tail_766_ = lean_ctor_get(v_x_763_, 2);
v___x_767_ = lean_expr_eqv(v_key_765_, v_a_762_);
if (v___x_767_ == 0)
{
v_x_763_ = v_tail_766_;
goto _start;
}
else
{
return v___x_767_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_762_ = stack[0].m_obj;
lean_object* v_x_763_ = stack[1].m_obj;
uint8_t v_res_769_;
v_res_769_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_762_, v_x_763_);
stack->m_num = v_res_769_;
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
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v_nbuckets_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_815_ = lean_array_get_size(v_data_814_);
v___x_816_ = lean_unsigned_to_nat(2u);
v_nbuckets_817_ = lean_nat_mul(v___x_815_, v___x_816_);
v___x_818_ = lean_unsigned_to_nat(0u);
v___x_819_ = lean_box(0);
v___x_820_ = lean_mk_array(v_nbuckets_817_, v___x_819_);
v___x_821_ = lean_array_propagate_mark(v_data_814_, v___x_820_);
v___x_822_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(v___x_818_, v_data_814_, v___x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(lean_object* v_m_823_, lean_object* v_a_824_, lean_object* v_b_825_){
_start:
{
lean_object* v_size_826_; lean_object* v_buckets_827_; lean_object* v___x_828_; uint64_t v___x_829_; uint64_t v___x_830_; uint64_t v___x_831_; uint64_t v_fold_832_; uint64_t v___x_833_; uint64_t v___x_834_; uint64_t v___x_835_; size_t v___x_836_; size_t v___x_837_; size_t v___x_838_; size_t v___x_839_; size_t v___x_840_; lean_object* v_bkt_841_; uint8_t v___x_842_; 
v_size_826_ = lean_ctor_get(v_m_823_, 0);
v_buckets_827_ = lean_ctor_get(v_m_823_, 1);
v___x_828_ = lean_array_get_size(v_buckets_827_);
v___x_829_ = l_Lean_Expr_hash(v_a_824_);
v___x_830_ = 32ULL;
v___x_831_ = lean_uint64_shift_right(v___x_829_, v___x_830_);
v_fold_832_ = lean_uint64_xor(v___x_829_, v___x_831_);
v___x_833_ = 16ULL;
v___x_834_ = lean_uint64_shift_right(v_fold_832_, v___x_833_);
v___x_835_ = lean_uint64_xor(v_fold_832_, v___x_834_);
v___x_836_ = lean_uint64_to_usize(v___x_835_);
v___x_837_ = lean_usize_of_nat(v___x_828_);
v___x_838_ = ((size_t)1ULL);
v___x_839_ = lean_usize_sub(v___x_837_, v___x_838_);
v___x_840_ = lean_usize_land(v___x_836_, v___x_839_);
v_bkt_841_ = lean_array_uget_borrowed(v_buckets_827_, v___x_840_);
v___x_842_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_824_, v_bkt_841_);
if (v___x_842_ == 0)
{
lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_863_; 
lean_inc_ref(v_buckets_827_);
lean_inc(v_size_826_);
v_isSharedCheck_863_ = !lean_is_exclusive(v_m_823_);
if (v_isSharedCheck_863_ == 0)
{
lean_object* v_unused_864_; lean_object* v_unused_865_; 
v_unused_864_ = lean_ctor_get(v_m_823_, 1);
lean_dec(v_unused_864_);
v_unused_865_ = lean_ctor_get(v_m_823_, 0);
lean_dec(v_unused_865_);
v___x_844_ = v_m_823_;
v_isShared_845_ = v_isSharedCheck_863_;
goto v_resetjp_843_;
}
else
{
lean_dec(v_m_823_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_863_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v_size_x27_847_; lean_object* v___x_848_; lean_object* v_buckets_x27_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_846_ = lean_unsigned_to_nat(1u);
v_size_x27_847_ = lean_nat_add(v_size_826_, v___x_846_);
lean_dec(v_size_826_);
lean_inc(v_bkt_841_);
v___x_848_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_848_, 0, v_a_824_);
lean_ctor_set(v___x_848_, 1, v_b_825_);
lean_ctor_set(v___x_848_, 2, v_bkt_841_);
v_buckets_x27_849_ = lean_array_uset(v_buckets_827_, v___x_840_, v___x_848_);
v___x_850_ = lean_unsigned_to_nat(4u);
v___x_851_ = lean_nat_mul(v_size_x27_847_, v___x_850_);
v___x_852_ = lean_unsigned_to_nat(3u);
v___x_853_ = lean_nat_div(v___x_851_, v___x_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_array_get_size(v_buckets_x27_849_);
v___x_855_ = lean_nat_dec_le(v___x_853_, v___x_854_);
lean_dec(v___x_853_);
if (v___x_855_ == 0)
{
lean_object* v_val_856_; lean_object* v___x_858_; 
v_val_856_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(v_buckets_x27_849_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v_val_856_);
lean_ctor_set(v___x_844_, 0, v_size_x27_847_);
v___x_858_ = v___x_844_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_size_x27_847_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_val_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
else
{
lean_object* v___x_861_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v_buckets_x27_849_);
lean_ctor_set(v___x_844_, 0, v_size_x27_847_);
v___x_861_ = v___x_844_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_size_x27_847_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_buckets_x27_849_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
else
{
lean_dec(v_b_825_);
lean_dec_ref(v_a_824_);
return v_m_823_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(lean_object* v_as_866_, size_t v_sz_867_, size_t v_i_868_, lean_object* v_b_869_){
_start:
{
uint8_t v___x_870_; 
v___x_870_ = lean_usize_dec_lt(v_i_868_, v_sz_867_);
if (v___x_870_ == 0)
{
return v_b_869_;
}
else
{
lean_object* v_a_871_; lean_object* v___x_872_; lean_object* v_r_873_; size_t v___x_874_; size_t v___x_875_; 
v_a_871_ = lean_array_uget_borrowed(v_as_866_, v_i_868_);
v___x_872_ = lean_box(0);
lean_inc(v_a_871_);
v_r_873_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v_b_869_, v_a_871_, v___x_872_);
v___x_874_ = ((size_t)1ULL);
v___x_875_ = lean_usize_add(v_i_868_, v___x_874_);
v_i_868_ = v___x_875_;
v_b_869_ = v_r_873_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_866_ = stack[0].m_obj;
size_t v_sz_867_ = stack[1].m_num;
size_t v_i_868_ = stack[2].m_num;
lean_object* v_b_869_ = stack[3].m_obj;
lean_object* v_res_877_;
v_res_877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(v_as_866_, v_sz_867_, v_i_868_, v_b_869_);
stack->m_obj
 = v_res_877_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4___boxed(lean_object* v_as_878_, lean_object* v_sz_879_, lean_object* v_i_880_, lean_object* v_b_881_){
_start:
{
size_t v_sz_boxed_882_; size_t v_i_boxed_883_; lean_object* v_res_884_; 
v_sz_boxed_882_ = lean_unbox_usize(v_sz_879_);
lean_dec(v_sz_879_);
v_i_boxed_883_ = lean_unbox_usize(v_i_880_);
lean_dec(v_i_880_);
v_res_884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(v_as_878_, v_sz_boxed_882_, v_i_boxed_883_, v_b_881_);
lean_dec_ref(v_as_878_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(lean_object* v_m_885_, lean_object* v_l_886_){
_start:
{
size_t v_sz_887_; size_t v___x_888_; lean_object* v___x_889_; 
v_sz_887_ = lean_array_size(v_l_886_);
v___x_888_ = ((size_t)0ULL);
v___x_889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(v_l_886_, v_sz_887_, v___x_888_, v_m_885_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3___boxed(lean_object* v_m_890_, lean_object* v_l_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(v_m_890_, v_l_891_);
lean_dec_ref(v_l_891_);
return v_res_892_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(lean_object* v_as_893_, size_t v_i_894_, size_t v_stop_895_, lean_object* v_b_896_){
_start:
{
uint8_t v___x_897_; 
v___x_897_ = lean_usize_dec_eq(v_i_894_, v_stop_895_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; size_t v___x_900_; size_t v___x_901_; 
v___x_898_ = lean_array_uget_borrowed(v_as_893_, v_i_894_);
lean_inc(v___x_898_);
v___x_899_ = l_Lean_collectFVars(v_b_896_, v___x_898_);
v___x_900_ = ((size_t)1ULL);
v___x_901_ = lean_usize_add(v_i_894_, v___x_900_);
v_i_894_ = v___x_901_;
v_b_896_ = v___x_899_;
goto _start;
}
else
{
return v_b_896_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_893_ = stack[0].m_obj;
size_t v_i_894_ = stack[1].m_num;
size_t v_stop_895_ = stack[2].m_num;
lean_object* v_b_896_ = stack[3].m_obj;
lean_object* v_res_903_;
v_res_903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_as_893_, v_i_894_, v_stop_895_, v_b_896_);
stack->m_obj
 = v_res_903_;
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
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(lean_object* v_dontRevert_919_, lean_object* v_a_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; lean_object* v___y_928_; size_t v___y_929_; lean_object* v___y_930_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___y_941_; size_t v___y_942_; lean_object* v_fvarIds_943_; lean_object* v___y_952_; size_t v___y_953_; lean_object* v___y_954_; uint8_t v___x_956_; uint8_t v___x_957_; lean_object* v___x_958_; 
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_938_ = lean_box(1);
v___x_939_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_956_ = 0;
v___x_957_ = 1;
lean_inc_ref(v_a_920_);
v___x_958_ = l_Lean_Meta_collectForwardDeps(v_a_920_, v___x_956_, v___x_957_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_1002_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_1002_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_1002_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___y_964_; lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_993_ = lean_array_get_size(v_a_959_);
v___x_994_ = lean_nat_dec_lt(v___x_926_, v___x_993_);
if (v___x_994_ == 0)
{
lean_dec(v_a_959_);
v___y_964_ = v___x_939_;
goto v___jp_963_;
}
else
{
uint8_t v___x_995_; 
v___x_995_ = lean_nat_dec_le(v___x_993_, v___x_993_);
if (v___x_995_ == 0)
{
if (v___x_994_ == 0)
{
lean_dec(v_a_959_);
v___y_964_ = v___x_939_;
goto v___jp_963_;
}
else
{
size_t v___x_996_; size_t v___x_997_; lean_object* v___x_998_; 
v___x_996_ = ((size_t)0ULL);
v___x_997_ = lean_usize_of_nat(v___x_993_);
lean_inc_ref(v_dontRevert_919_);
v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_919_, v_a_959_, v___x_996_, v___x_997_, v___x_939_);
lean_dec(v_a_959_);
v___y_964_ = v___x_998_;
goto v___jp_963_;
}
}
else
{
size_t v___x_999_; size_t v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = ((size_t)0ULL);
v___x_1000_ = lean_usize_of_nat(v___x_993_);
lean_inc_ref(v_dontRevert_919_);
v___x_1001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_919_, v_a_959_, v___x_999_, v___x_1000_, v___x_939_);
lean_dec(v_a_959_);
v___y_964_ = v___x_1001_;
goto v___jp_963_;
}
}
v___jp_963_:
{
lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_965_ = lean_array_get_size(v___y_964_);
v___x_966_ = lean_array_get_size(v_a_920_);
lean_dec_ref(v_a_920_);
v___x_967_ = lean_nat_dec_eq(v___x_965_, v___x_966_);
if (v___x_967_ == 0)
{
size_t v_sz_968_; size_t v___x_969_; lean_object* v___x_970_; 
lean_del_object(v___x_961_);
v_sz_968_ = lean_array_size(v___y_964_);
v___x_969_ = ((size_t)0ULL);
lean_inc_ref(v___y_964_);
v___x_970_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(v_sz_968_, v___x_969_, v___y_964_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
lean_dec_ref_known(v___x_970_, 1);
v___x_972_ = lean_array_get_size(v_a_971_);
v___x_973_ = lean_nat_dec_lt(v___x_926_, v___x_972_);
if (v___x_973_ == 0)
{
lean_dec(v_a_971_);
v___y_941_ = v___y_964_;
v___y_942_ = v___x_969_;
v_fvarIds_943_ = v___x_939_;
goto v___jp_940_;
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_974_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2);
v___x_975_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(v___x_974_, v___y_964_);
v___x_976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set(v___x_976_, 1, v___x_938_);
lean_ctor_set(v___x_976_, 2, v___x_939_);
v___x_977_ = lean_nat_dec_le(v___x_972_, v___x_972_);
if (v___x_977_ == 0)
{
if (v___x_973_ == 0)
{
lean_dec_ref_known(v___x_976_, 3);
lean_dec(v_a_971_);
v___y_941_ = v___y_964_;
v___y_942_ = v___x_969_;
v_fvarIds_943_ = v___x_939_;
goto v___jp_940_;
}
else
{
size_t v___x_978_; lean_object* v___x_979_; 
v___x_978_ = lean_usize_of_nat(v___x_972_);
v___x_979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_a_971_, v___x_969_, v___x_978_, v___x_976_);
lean_dec(v_a_971_);
v___y_952_ = v___y_964_;
v___y_953_ = v___x_969_;
v___y_954_ = v___x_979_;
goto v___jp_951_;
}
}
else
{
size_t v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_usize_of_nat(v___x_972_);
v___x_981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_a_971_, v___x_969_, v___x_980_, v___x_976_);
lean_dec(v_a_971_);
v___y_952_ = v___y_964_;
v___y_953_ = v___x_969_;
v___y_954_ = v___x_981_;
goto v___jp_951_;
}
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_dec_ref(v___y_964_);
lean_dec_ref(v_dontRevert_919_);
v_a_982_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_970_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_970_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
else
{
lean_object* v___x_991_; 
lean_dec_ref(v_dontRevert_919_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___y_964_);
v___x_991_ = v___x_961_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___y_964_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_920_);
lean_dec_ref(v_dontRevert_919_);
return v___x_958_;
}
v___jp_927_:
{
size_t v_sz_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v_sz_931_ = lean_array_size(v___y_930_);
lean_inc_ref(v___y_930_);
v___x_932_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_931_, v___y_929_, v___y_930_);
v___x_933_ = l_Array_append___redArg(v___y_928_, v___x_932_);
lean_dec_ref(v___x_932_);
v___x_934_ = lean_array_get_size(v___y_930_);
lean_dec_ref(v___y_930_);
v___x_935_ = lean_nat_dec_eq(v___x_934_, v___x_926_);
if (v___x_935_ == 0)
{
v_a_920_ = v___x_933_;
goto _start;
}
else
{
lean_object* v___x_937_; 
lean_dec_ref(v_dontRevert_919_);
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_933_);
return v___x_937_;
}
}
v___jp_940_:
{
lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_944_ = lean_array_get_size(v_fvarIds_943_);
v___x_945_ = lean_nat_dec_lt(v___x_926_, v___x_944_);
if (v___x_945_ == 0)
{
lean_dec_ref(v_fvarIds_943_);
v___y_928_ = v___y_941_;
v___y_929_ = v___y_942_;
v___y_930_ = v___x_939_;
goto v___jp_927_;
}
else
{
uint8_t v___x_946_; 
v___x_946_ = lean_nat_dec_le(v___x_944_, v___x_944_);
if (v___x_946_ == 0)
{
if (v___x_945_ == 0)
{
lean_dec_ref(v_fvarIds_943_);
v___y_928_ = v___y_941_;
v___y_929_ = v___y_942_;
v___y_930_ = v___x_939_;
goto v___jp_927_;
}
else
{
size_t v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_usize_of_nat(v___x_944_);
lean_inc_ref(v_dontRevert_919_);
v___x_948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_919_, v_fvarIds_943_, v___y_942_, v___x_947_, v___x_939_);
lean_dec_ref(v_fvarIds_943_);
v___y_928_ = v___y_941_;
v___y_929_ = v___y_942_;
v___y_930_ = v___x_948_;
goto v___jp_927_;
}
}
else
{
size_t v___x_949_; lean_object* v___x_950_; 
v___x_949_ = lean_usize_of_nat(v___x_944_);
lean_inc_ref(v_dontRevert_919_);
v___x_950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_919_, v_fvarIds_943_, v___y_942_, v___x_949_, v___x_939_);
lean_dec_ref(v_fvarIds_943_);
v___y_928_ = v___y_941_;
v___y_929_ = v___y_942_;
v___y_930_ = v___x_950_;
goto v___jp_927_;
}
}
}
v___jp_951_:
{
lean_object* v_fvarIds_955_; 
v_fvarIds_955_ = lean_ctor_get(v___y_954_, 2);
lean_inc_ref(v_fvarIds_955_);
lean_dec_ref(v___y_954_);
v___y_941_ = v___y_952_;
v___y_942_ = v___y_953_;
v_fvarIds_943_ = v_fvarIds_955_;
goto v___jp_940_;
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_dontRevert_919_ = stack[0].m_obj;
lean_object* v_a_920_ = stack[1].m_obj;
lean_object* v___y_921_ = stack[2].m_obj;
lean_object* v___y_922_ = stack[3].m_obj;
lean_object* v___y_923_ = stack[4].m_obj;
lean_object* v___y_924_ = stack[5].m_obj;
lean_object* v_res_1003_;
v_res_1003_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_919_, v_a_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
stack->m_obj
 = v_res_1003_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___boxed(lean_object* v_dontRevert_1004_, lean_object* v_a_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_1004_, v_a_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
return v_res_1011_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1012_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_1013_ = lean_box(1);
v___x_1014_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2);
v___x_1015_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
lean_ctor_set(v___x_1015_, 1, v___x_1013_);
lean_ctor_set(v___x_1015_, 2, v___x_1012_);
return v___x_1015_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(lean_object* v_e_1016_, lean_object* v_dontRevert_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v___y_1024_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v_fvarIds_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1029_ = lean_unsigned_to_nat(0u);
v___x_1030_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_1031_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0);
v___x_1032_ = l_Lean_collectFVars(v___x_1031_, v_e_1016_);
v_fvarIds_1033_ = lean_ctor_get(v___x_1032_, 2);
lean_inc_ref(v_fvarIds_1033_);
lean_dec_ref(v___x_1032_);
v___x_1034_ = lean_array_get_size(v_fvarIds_1033_);
v___x_1035_ = lean_nat_dec_lt(v___x_1029_, v___x_1034_);
if (v___x_1035_ == 0)
{
lean_dec_ref(v_fvarIds_1033_);
v___y_1024_ = v___x_1030_;
goto v___jp_1023_;
}
else
{
uint8_t v___x_1036_; 
v___x_1036_ = lean_nat_dec_le(v___x_1034_, v___x_1034_);
if (v___x_1036_ == 0)
{
if (v___x_1035_ == 0)
{
lean_dec_ref(v_fvarIds_1033_);
v___y_1024_ = v___x_1030_;
goto v___jp_1023_;
}
else
{
size_t v___x_1037_; size_t v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = ((size_t)0ULL);
v___x_1038_ = lean_usize_of_nat(v___x_1034_);
lean_inc_ref(v_dontRevert_1017_);
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_1017_, v_fvarIds_1033_, v___x_1037_, v___x_1038_, v___x_1030_);
lean_dec_ref(v_fvarIds_1033_);
v___y_1024_ = v___x_1039_;
goto v___jp_1023_;
}
}
else
{
size_t v___x_1040_; size_t v___x_1041_; lean_object* v___x_1042_; 
v___x_1040_ = ((size_t)0ULL);
v___x_1041_ = lean_usize_of_nat(v___x_1034_);
lean_inc_ref(v_dontRevert_1017_);
v___x_1042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_1017_, v_fvarIds_1033_, v___x_1040_, v___x_1041_, v___x_1030_);
lean_dec_ref(v_fvarIds_1033_);
v___y_1024_ = v___x_1042_;
goto v___jp_1023_;
}
}
v___jp_1023_:
{
size_t v_sz_1025_; size_t v___x_1026_; lean_object* v_xs_1027_; lean_object* v___x_1028_; 
v_sz_1025_ = lean_array_size(v___y_1024_);
v___x_1026_ = ((size_t)0ULL);
v_xs_1027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_1025_, v___x_1026_, v___y_1024_);
v___x_1028_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_1017_, v_xs_1027_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1028_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1016_ = stack[0].m_obj;
lean_object* v_dontRevert_1017_ = stack[1].m_obj;
lean_object* v_a_1018_ = stack[2].m_obj;
lean_object* v_a_1019_ = stack[3].m_obj;
lean_object* v_a_1020_ = stack[4].m_obj;
lean_object* v_a_1021_ = stack[5].m_obj;
lean_object* v_res_1043_;
v_res_1043_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1016_, v_dontRevert_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
stack->m_obj
 = v_res_1043_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___boxed(lean_object* v_e_1044_, lean_object* v_dontRevert_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1044_, v_dontRevert_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
return v_res_1051_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(lean_object* v_dontRevert_1052_, lean_object* v_inst_1053_, lean_object* v_a_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_1052_, v_a_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
return v___x_1060_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_dontRevert_1052_ = stack[0].m_obj;
lean_object* v_a_1054_ = stack[2].m_obj;
lean_object* v___y_1055_ = stack[3].m_obj;
lean_object* v___y_1056_ = stack[4].m_obj;
lean_object* v___y_1057_ = stack[5].m_obj;
lean_object* v___y_1058_ = stack[6].m_obj;
lean_object* v_res_1061_;
v_res_1061_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(v_dontRevert_1052_, lean_box(0), v_a_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
stack->m_obj
 = v_res_1061_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___boxed(lean_object* v_dontRevert_1062_, lean_object* v_inst_1063_, lean_object* v_a_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(v_dontRevert_1062_, v_inst_1063_, v_a_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3(lean_object* v_00_u03b2_1071_, lean_object* v_m_1072_, lean_object* v_a_1073_, lean_object* v_b_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v_m_1072_, v_a_1073_, v_b_1074_);
return v___x_1075_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_1076_, lean_object* v_a_1077_, lean_object* v_x_1078_){
_start:
{
uint8_t v___x_1079_; 
v___x_1079_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_1077_, v_x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1077_ = stack[1].m_obj;
lean_object* v_x_1078_ = stack[2].m_obj;
uint8_t v_res_1080_;
v_res_1080_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(lean_box(0), v_a_1077_, v_x_1078_);
stack->m_num = v_res_1080_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1081_, lean_object* v_a_1082_, lean_object* v_x_1083_){
_start:
{
uint8_t v_res_1084_; lean_object* v_r_1085_; 
v_res_1084_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(v_00_u03b2_1081_, v_a_1082_, v_x_1083_);
lean_dec(v_x_1083_);
lean_dec_ref(v_a_1082_);
v_r_1085_ = lean_box(v_res_1084_);
return v_r_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5(lean_object* v_00_u03b2_1086_, lean_object* v_data_1087_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(v_data_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_1089_, lean_object* v_i_1090_, lean_object* v_source_1091_, lean_object* v_target_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(v_i_1090_, v_source_1091_, v_target_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11(lean_object* v_00_u03b2_1094_, lean_object* v_x_1095_, lean_object* v_x_1096_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(v_x_1095_, v_x_1096_);
return v___x_1097_;
}
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(lean_object* v_a_1104_, lean_object* v___x_1105_, lean_object* v___x_1106_, lean_object* v_i_1107_, lean_object* v_a_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_zero_1114_; uint8_t v_isZero_1115_; 
v_zero_1114_ = lean_unsigned_to_nat(0u);
v_isZero_1115_ = lean_nat_dec_eq(v_i_1107_, v_zero_1114_);
if (v_isZero_1115_ == 1)
{
lean_object* v___x_1116_; 
lean_dec(v_i_1107_);
lean_dec(v___x_1106_);
lean_dec_ref(v___x_1105_);
v___x_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1116_, 0, v_a_1108_);
return v___x_1116_;
}
else
{
lean_object* v_one_1117_; lean_object* v_n_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v_one_1117_ = lean_unsigned_to_nat(1u);
v_n_1118_ = lean_nat_sub(v_i_1107_, v_one_1117_);
lean_dec(v_i_1107_);
v___x_1119_ = lean_array_fget_borrowed(v_a_1104_, v_n_1118_);
lean_inc_ref(v___x_1105_);
v___x_1120_ = l_Lean_LocalContext_getFVar_x21(v___x_1105_, v___x_1119_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_userName_1121_; lean_object* v_type_1122_; uint8_t v_bi_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v_userName_1121_ = lean_ctor_get(v___x_1120_, 2);
lean_inc(v_userName_1121_);
v_type_1122_ = lean_ctor_get(v___x_1120_, 3);
lean_inc_ref(v_type_1122_);
v_bi_1123_ = lean_ctor_get_uint8(v___x_1120_, sizeof(void*)*4);
lean_dec_ref_known(v___x_1120_, 4);
v___x_1124_ = l_Lean_Expr_headBeta(v_type_1122_);
v___x_1125_ = lean_expr_abstract_range(v___x_1124_, v_n_1118_, v_a_1104_);
lean_dec_ref(v___x_1124_);
lean_inc_ref(v___x_1125_);
v___x_1126_ = l_Lean_Meta_getLevel(v___x_1125_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref_known(v___x_1126_, 1);
v___x_1128_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_1129_ = lean_box(0);
lean_inc_n(v___x_1106_, 2);
v___x_1130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1106_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1131_, 0, v_a_1127_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = l_Lean_mkConst(v___x_1128_, v___x_1131_);
v___x_1133_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v___x_1106_);
lean_inc_ref(v___x_1125_);
v___x_1134_ = l_Lean_mkLambda(v_userName_1121_, v_bi_1123_, v___x_1125_, v_a_1108_);
v___x_1135_ = l_Lean_mkApp3(v___x_1132_, v___x_1125_, v___x_1133_, v___x_1134_);
v_i_1107_ = v_n_1118_;
v_a_1108_ = v___x_1135_;
goto _start;
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec_ref(v___x_1125_);
lean_dec(v_userName_1121_);
lean_dec(v_n_1118_);
lean_dec_ref(v_a_1108_);
lean_dec(v___x_1106_);
lean_dec_ref(v___x_1105_);
v_a_1137_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1126_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1126_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
else
{
uint8_t v_nondep_1145_; 
v_nondep_1145_ = lean_ctor_get_uint8(v___x_1120_, sizeof(void*)*5);
if (v_nondep_1145_ == 0)
{
lean_object* v_userName_1146_; lean_object* v_type_1147_; lean_object* v_value_1148_; uint8_t v___x_1149_; 
v_userName_1146_ = lean_ctor_get(v___x_1120_, 2);
lean_inc(v_userName_1146_);
v_type_1147_ = lean_ctor_get(v___x_1120_, 3);
lean_inc_ref(v_type_1147_);
v_value_1148_ = lean_ctor_get(v___x_1120_, 4);
lean_inc_ref(v_value_1148_);
lean_dec_ref_known(v___x_1120_, 5);
v___x_1149_ = lean_expr_has_loose_bvar(v_a_1108_, v_zero_1114_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; 
lean_dec_ref(v_value_1148_);
lean_dec_ref(v_type_1147_);
lean_dec(v_userName_1146_);
v___x_1150_ = lean_expr_lower_loose_bvars(v_a_1108_, v_one_1117_, v_one_1117_);
lean_dec_ref(v_a_1108_);
v_i_1107_ = v_n_1118_;
v_a_1108_ = v___x_1150_;
goto _start;
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1152_ = l_Lean_Expr_headBeta(v_type_1147_);
v___x_1153_ = lean_expr_abstract_range(v___x_1152_, v_n_1118_, v_a_1104_);
lean_dec_ref(v___x_1152_);
v___x_1154_ = lean_expr_abstract_range(v_value_1148_, v_n_1118_, v_a_1104_);
lean_dec_ref(v_value_1148_);
v___x_1155_ = l_Lean_Expr_letE___override(v_userName_1146_, v___x_1153_, v___x_1154_, v_a_1108_, v_nondep_1145_);
v_i_1107_ = v_n_1118_;
v_a_1108_ = v___x_1155_;
goto _start;
}
}
else
{
lean_object* v_userName_1157_; lean_object* v_type_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v_userName_1157_ = lean_ctor_get(v___x_1120_, 2);
lean_inc(v_userName_1157_);
v_type_1158_ = lean_ctor_get(v___x_1120_, 3);
lean_inc_ref(v_type_1158_);
lean_dec_ref_known(v___x_1120_, 5);
v___x_1159_ = l_Lean_Expr_headBeta(v_type_1158_);
v___x_1160_ = lean_expr_abstract_range(v___x_1159_, v_n_1118_, v_a_1104_);
lean_dec_ref(v___x_1159_);
lean_inc_ref(v___x_1160_);
v___x_1161_ = l_Lean_Meta_getLevel(v___x_1160_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref_known(v___x_1161_, 1);
v___x_1163_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_1164_ = lean_box(0);
lean_inc_n(v___x_1106_, 2);
v___x_1165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1106_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1166_, 0, v_a_1162_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
v___x_1167_ = l_Lean_mkConst(v___x_1163_, v___x_1166_);
v___x_1168_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v___x_1106_);
v___x_1169_ = 0;
lean_inc_ref(v___x_1160_);
v___x_1170_ = l_Lean_mkLambda(v_userName_1157_, v___x_1169_, v___x_1160_, v_a_1108_);
v___x_1171_ = l_Lean_mkApp3(v___x_1167_, v___x_1160_, v___x_1168_, v___x_1170_);
v_i_1107_ = v_n_1118_;
v_a_1108_ = v___x_1171_;
goto _start;
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec_ref(v___x_1160_);
lean_dec(v_userName_1157_);
lean_dec(v_n_1118_);
lean_dec_ref(v_a_1108_);
lean_dec(v___x_1106_);
lean_dec_ref(v___x_1105_);
v_a_1173_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1161_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1161_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1104_ = stack[0].m_obj;
lean_object* v___x_1105_ = stack[1].m_obj;
lean_object* v___x_1106_ = stack[2].m_obj;
lean_object* v_i_1107_ = stack[3].m_obj;
lean_object* v_a_1108_ = stack[4].m_obj;
lean_object* v___y_1109_ = stack[5].m_obj;
lean_object* v___y_1110_ = stack[6].m_obj;
lean_object* v___y_1111_ = stack[7].m_obj;
lean_object* v___y_1112_ = stack[8].m_obj;
lean_object* v_res_1181_;
v_res_1181_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1104_, v___x_1105_, v___x_1106_, v_i_1107_, v_a_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
stack->m_obj
 = v_res_1181_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___boxed(lean_object* v_a_1182_, lean_object* v___x_1183_, lean_object* v___x_1184_, lean_object* v_i_1185_, lean_object* v_a_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1182_, v___x_1183_, v___x_1184_, v_i_1185_, v_a_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec_ref(v_a_1182_);
return v_res_1192_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(lean_object* v_e_1197_, lean_object* v_dontRevert_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_box(0);
lean_inc_ref(v_e_1197_);
v___x_1205_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1197_, v_dontRevert_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v_lctx_1207_; lean_object* v___x_1208_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1206_);
lean_dec_ref_known(v___x_1205_, 1);
v_lctx_1207_ = lean_ctor_get(v_a_1199_, 2);
lean_inc(v_a_1202_);
lean_inc_ref(v_a_1201_);
lean_inc(v_a_1200_);
lean_inc_ref(v_a_1199_);
lean_inc_ref(v_e_1197_);
v___x_1208_ = lean_infer_type(v_e_1197_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1230_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1211_ = v___x_1208_;
v_isShared_1212_ = v_isSharedCheck_1230_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1208_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1230_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = l_Lean_Expr_cleanupAnnotations(v_a_1209_);
v___x_1214_ = l_Lean_Expr_isApp(v___x_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1216_; 
lean_dec_ref(v___x_1213_);
lean_dec(v_a_1206_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v_e_1197_);
v___x_1216_ = v___x_1211_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_e_1197_);
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
lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1218_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1213_);
v___x_1219_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___closed__0));
v___x_1220_ = l_Lean_Expr_isConstOf(v___x_1218_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1222_; 
lean_dec_ref(v___x_1218_);
lean_dec(v_a_1206_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v_e_1197_);
v___x_1222_ = v___x_1211_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_e_1197_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
else
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_del_object(v___x_1211_);
v___x_1224_ = l_Lean_Expr_constLevels_x21(v___x_1218_);
lean_dec_ref(v___x_1218_);
v___x_1225_ = lean_unsigned_to_nat(0u);
v___x_1226_ = l_List_get_x21Internal___redArg(v___x_1204_, v___x_1224_, v___x_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_array_get_size(v_a_1206_);
v___x_1228_ = lean_expr_abstract(v_e_1197_, v_a_1206_);
lean_dec_ref(v_e_1197_);
lean_inc_ref(v_lctx_1207_);
v___x_1229_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1206_, v_lctx_1207_, v___x_1226_, v___x_1227_, v___x_1228_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
lean_dec(v_a_1206_);
return v___x_1229_;
}
}
}
}
else
{
lean_dec(v_a_1206_);
lean_dec_ref(v_e_1197_);
return v___x_1208_;
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec_ref(v_e_1197_);
v_a_1231_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1205_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1205_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1197_ = stack[0].m_obj;
lean_object* v_dontRevert_1198_ = stack[1].m_obj;
lean_object* v_a_1199_ = stack[2].m_obj;
lean_object* v_a_1200_ = stack[3].m_obj;
lean_object* v_a_1201_ = stack[4].m_obj;
lean_object* v_a_1202_ = stack[5].m_obj;
lean_object* v_res_1239_;
v_res_1239_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(v_e_1197_, v_dontRevert_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
stack->m_obj
 = v_res_1239_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed(lean_object* v_e_1240_, lean_object* v_dontRevert_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(v_e_1240_, v_dontRevert_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
return v_res_1247_;
}
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(lean_object* v_a_1248_, lean_object* v___x_1249_, lean_object* v___x_1250_, lean_object* v_n_1251_, lean_object* v_i_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1248_, v___x_1249_, v___x_1250_, v_i_1252_, v_a_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1260_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1248_ = stack[0].m_obj;
lean_object* v___x_1249_ = stack[1].m_obj;
lean_object* v___x_1250_ = stack[2].m_obj;
lean_object* v_n_1251_ = stack[3].m_obj;
lean_object* v_i_1252_ = stack[4].m_obj;
lean_object* v_a_1254_ = stack[6].m_obj;
lean_object* v___y_1255_ = stack[7].m_obj;
lean_object* v___y_1256_ = stack[8].m_obj;
lean_object* v___y_1257_ = stack[9].m_obj;
lean_object* v___y_1258_ = stack[10].m_obj;
lean_object* v_res_1261_;
v_res_1261_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(v_a_1248_, v___x_1249_, v___x_1250_, v_n_1251_, v_i_1252_, lean_box(0), v_a_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
stack->m_obj
 = v_res_1261_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___boxed(lean_object* v_a_1262_, lean_object* v___x_1263_, lean_object* v___x_1264_, lean_object* v_n_1265_, lean_object* v_i_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(v_a_1262_, v___x_1263_, v___x_1264_, v_n_1265_, v_i_1266_, v_a_1267_, v_a_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v_n_1265_);
lean_dec_ref(v_a_1262_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(lean_object* v_lvl_1281_, lean_object* v_lhs_1282_, lean_object* v_rhs_1283_){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1284_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
v___x_1285_ = lean_box(0);
lean_inc(v_lvl_1281_);
v___x_1286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1286_, 0, v_lvl_1281_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = l_Lean_mkConst(v___x_1284_, v___x_1286_);
v___x_1288_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_lvl_1281_);
v___x_1289_ = l_Lean_mkApp3(v___x_1287_, v___x_1288_, v_lhs_1282_, v_rhs_1283_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(lean_object* v_lvl_1296_, lean_object* v_lhs_1297_, lean_object* v_rhs_1298_){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1299_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
v___x_1300_ = lean_box(0);
lean_inc(v_lvl_1296_);
v___x_1301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1301_, 0, v_lvl_1296_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = l_Lean_mkConst(v___x_1299_, v___x_1301_);
v___x_1303_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_lvl_1296_);
v___x_1304_ = l_Lean_mkApp3(v___x_1302_, v___x_1303_, v_lhs_1297_, v_rhs_1298_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(lean_object* v_p_1305_){
_start:
{
lean_object* v_lvl_1306_; lean_object* v_cursorPred_1307_; lean_object* v_letMutsPred_1308_; lean_object* v___x_1309_; 
v_lvl_1306_ = lean_ctor_get(v_p_1305_, 0);
lean_inc(v_lvl_1306_);
v_cursorPred_1307_ = lean_ctor_get(v_p_1305_, 1);
lean_inc_ref(v_cursorPred_1307_);
v_letMutsPred_1308_ = lean_ctor_get(v_p_1305_, 2);
lean_inc_ref(v_letMutsPred_1308_);
lean_dec_ref(v_p_1305_);
v___x_1309_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v_lvl_1306_, v_cursorPred_1307_, v_letMutsPred_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___impl(lean_object* v_x_1310_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_obj_tag_nat(v_x_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___impl___boxed(lean_object* v_x_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___impl(v_x_1312_);
lean_dec(v_x_1312_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(lean_object* v_t_1314_, lean_object* v_k_1315_){
_start:
{
if (lean_obj_tag(v_t_1314_) == 3)
{
lean_object* v_e_1316_; lean_object* v___x_1317_; 
v_e_1316_ = lean_ctor_get(v_t_1314_, 0);
lean_inc_ref(v_e_1316_);
lean_dec_ref_known(v_t_1314_, 1);
v___x_1317_ = lean_apply_1(v_k_1315_, v_e_1316_);
return v___x_1317_;
}
else
{
lean_dec(v_t_1314_);
return v_k_1315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(lean_object* v_motive_1318_, lean_object* v_ctorIdx_1319_, lean_object* v_t_1320_, lean_object* v_h_1321_, lean_object* v_k_1322_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1320_, v_k_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___boxed(lean_object* v_motive_1324_, lean_object* v_ctorIdx_1325_, lean_object* v_t_1326_, lean_object* v_h_1327_, lean_object* v_k_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(v_motive_1324_, v_ctorIdx_1325_, v_t_1326_, v_h_1327_, v_k_1328_);
lean_dec(v_ctorIdx_1325_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim___redArg(lean_object* v_t_1330_, lean_object* v_punit_1331_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1330_, v_punit_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim(lean_object* v_motive_1333_, lean_object* v_t_1334_, lean_object* v_h_1335_, lean_object* v_punit_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1334_, v_punit_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim___redArg(lean_object* v_t_1338_, lean_object* v_false_1339_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1338_, v_false_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim(lean_object* v_motive_1341_, lean_object* v_t_1342_, lean_object* v_h_1343_, lean_object* v_false_1344_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1342_, v_false_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim___redArg(lean_object* v_t_1346_, lean_object* v_true_1347_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1346_, v_true_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim(lean_object* v_motive_1349_, lean_object* v_t_1350_, lean_object* v_h_1351_, lean_object* v_true_1352_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1350_, v_true_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim___redArg(lean_object* v_t_1354_, lean_object* v_other_1355_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1354_, v_other_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim(lean_object* v_motive_1357_, lean_object* v_t_1358_, lean_object* v_h_1359_, lean_object* v_other_1360_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1358_, v_other_1360_);
return v___x_1361_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(lean_object* v_a_1362_){
_start:
{
lean_object* v_snd_1364_; lean_object* v_fst_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1404_; 
v_snd_1364_ = lean_ctor_get(v_a_1362_, 1);
v_fst_1365_ = lean_ctor_get(v_a_1362_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_a_1362_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1367_ = v_a_1362_;
v_isShared_1368_ = v_isSharedCheck_1404_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_snd_1364_);
lean_inc(v_fst_1365_);
lean_dec(v_a_1362_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1404_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v_fst_1369_; lean_object* v_snd_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1403_; 
v_fst_1369_ = lean_ctor_get(v_snd_1364_, 0);
v_snd_1370_ = lean_ctor_get(v_snd_1364_, 1);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_snd_1364_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1372_ = v_snd_1364_;
v_isShared_1373_ = v_isSharedCheck_1403_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_snd_1370_);
lean_inc(v_fst_1369_);
lean_dec(v_snd_1364_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1403_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1374_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_1375_ = lean_unsigned_to_nat(4u);
v___x_1376_ = l_Lean_Expr_isAppOfArity(v_fst_1369_, v___x_1374_, v___x_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1378_; 
if (v_isShared_1373_ == 0)
{
v___x_1378_ = v___x_1372_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_fst_1369_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_snd_1370_);
v___x_1378_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
lean_object* v___x_1380_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 1, v___x_1378_);
v___x_1380_ = v___x_1367_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_fst_1365_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
return v___x_1381_;
}
}
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1384_ = lean_unsigned_to_nat(3u);
v___x_1385_ = lean_unsigned_to_nat(2u);
v___x_1386_ = l_Lean_Expr_getAppNumArgs(v_fst_1369_);
v___x_1387_ = lean_nat_sub(v___x_1386_, v___x_1385_);
v___x_1388_ = lean_unsigned_to_nat(1u);
v___x_1389_ = lean_nat_sub(v___x_1387_, v___x_1388_);
lean_dec(v___x_1387_);
v___x_1390_ = l_Lean_Expr_getRevArg_x21(v_fst_1369_, v___x_1389_);
v___x_1391_ = lean_array_push(v_snd_1370_, v___x_1390_);
v___x_1392_ = lean_nat_add(v_fst_1365_, v___x_1388_);
lean_dec(v_fst_1365_);
v___x_1393_ = lean_nat_sub(v___x_1386_, v___x_1384_);
lean_dec(v___x_1386_);
v___x_1394_ = lean_nat_sub(v___x_1393_, v___x_1388_);
lean_dec(v___x_1393_);
v___x_1395_ = l_Lean_Expr_getRevArg_x21(v_fst_1369_, v___x_1394_);
lean_dec(v_fst_1369_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 1, v___x_1391_);
lean_ctor_set(v___x_1372_, 0, v___x_1395_);
v___x_1397_ = v___x_1372_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v___x_1391_);
v___x_1397_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1399_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 1, v___x_1397_);
lean_ctor_set(v___x_1367_, 0, v___x_1392_);
v___x_1399_ = v___x_1367_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
v_a_1362_ = v___x_1399_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1362_ = stack[0].m_obj;
lean_object* v_res_1405_;
v_res_1405_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_a_1362_);
stack->m_obj
 = v_res_1405_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg___boxed(lean_object* v_a_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_a_1406_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(lean_object* v_fst_1409_, lean_object* v_p_1410_){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
lean_inc(v_fst_1409_);
v___x_1411_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_1409_);
v___x_1412_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_1409_, v___x_1411_, v_p_1410_);
return v___x_1412_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(lean_object* v_letMutsTuple_1413_, lean_object* v___x_1414_, uint8_t v___x_1415_, lean_object* v_fvarId_1416_){
_start:
{
lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1417_ = l_Lean_Expr_fvarId_x21(v_letMutsTuple_1413_);
v___x_1418_ = l_Lean_instBEqFVarId_beq(v_fvarId_1416_, v___x_1417_);
lean_dec(v___x_1417_);
if (v___x_1418_ == 0)
{
uint8_t v___x_1419_; 
v___x_1419_ = l_Lean_LocalContext_contains(v___x_1414_, v_fvarId_1416_);
return v___x_1419_;
}
else
{
return v___x_1415_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_letMutsTuple_1413_ = stack[0].m_obj;
lean_object* v___x_1414_ = stack[1].m_obj;
uint8_t v___x_1415_ = stack[2].m_num;
lean_object* v_fvarId_1416_ = stack[3].m_obj;
uint8_t v_res_1420_;
v_res_1420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(v_letMutsTuple_1413_, v___x_1414_, v___x_1415_, v_fvarId_1416_);
stack->m_num = v_res_1420_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0___boxed(lean_object* v_letMutsTuple_1421_, lean_object* v___x_1422_, lean_object* v___x_1423_, lean_object* v_fvarId_1424_){
_start:
{
uint8_t v___x_9702__boxed_1425_; uint8_t v_res_1426_; lean_object* v_r_1427_; 
v___x_9702__boxed_1425_ = lean_unbox(v___x_1423_);
v_res_1426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(v_letMutsTuple_1421_, v___x_1422_, v___x_9702__boxed_1425_, v_fvarId_1424_);
lean_dec(v_fvarId_1424_);
lean_dec_ref(v___x_1422_);
lean_dec_ref(v_letMutsTuple_1421_);
v_r_1427_ = lean_box(v_res_1426_);
return v_r_1427_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(lean_object* v_inv_1447_, lean_object* v___x_1448_, lean_object* v_xs_1449_, lean_object* v_letMuts_1450_, lean_object* v_as_1451_, size_t v_sz_1452_, size_t v_i_1453_, lean_object* v_b_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_a_1461_; uint8_t v___x_1465_; 
v___x_1465_ = lean_usize_dec_lt(v_i_1453_, v_sz_1452_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; 
lean_dec_ref(v_letMuts_1450_);
lean_dec_ref(v_xs_1449_);
lean_dec_ref(v___x_1448_);
lean_dec(v_inv_1447_);
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v_b_1454_);
return v___x_1466_;
}
else
{
lean_object* v_snd_1467_; lean_object* v_fst_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1813_; 
v_snd_1467_ = lean_ctor_get(v_b_1454_, 1);
v_fst_1468_ = lean_ctor_get(v_b_1454_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_b_1454_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1470_ = v_b_1454_;
v_isShared_1471_ = v_isSharedCheck_1813_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_snd_1467_);
lean_inc(v_fst_1468_);
lean_dec(v_b_1454_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1813_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v_fst_1472_; lean_object* v_snd_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1812_; 
v_fst_1472_ = lean_ctor_get(v_snd_1467_, 0);
v_snd_1473_ = lean_ctor_get(v_snd_1467_, 1);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_snd_1467_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1475_ = v_snd_1467_;
v_isShared_1476_ = v_isSharedCheck_1812_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_snd_1473_);
lean_inc(v_fst_1472_);
lean_dec(v_snd_1467_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1812_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; uint8_t v___y_1491_; lean_object* v___y_1591_; lean_object* v_prefixPoint_x3f_1592_; lean_object* v_suffixPoint_x3f_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v_a_1619_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v_prefixPoint_x3f_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v_a_1712_; lean_object* v_a_1717_; lean_object* v___x_1790_; 
v___x_1477_ = lean_unsigned_to_nat(0u);
v___x_1478_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5));
v___x_1479_ = lean_box(0);
v_a_1619_ = lean_array_uget_borrowed(v_as_1451_, v_i_1453_);
lean_inc(v_a_1619_);
v___x_1790_ = l_Lean_MVarId_getType(v_a_1619_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1792_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1790_, 1);
v___x_1792_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_a_1791_, v___y_1456_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v___x_1794_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref_known(v___x_1792_, 1);
v___x_1794_ = l_Lean_Expr_consumeMData(v_a_1793_);
lean_dec(v_a_1793_);
v_a_1717_ = v___x_1794_;
goto v___jp_1716_;
}
else
{
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1795_; 
v_a_1795_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1795_);
lean_dec_ref_known(v___x_1792_, 1);
v_a_1717_ = v_a_1795_;
goto v___jp_1716_;
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_del_object(v___x_1475_);
lean_dec(v_snd_1473_);
lean_dec(v_fst_1472_);
lean_del_object(v___x_1470_);
lean_dec(v_fst_1468_);
lean_dec_ref(v_letMuts_1450_);
lean_dec_ref(v_xs_1449_);
lean_dec_ref(v___x_1448_);
lean_dec(v_inv_1447_);
v_a_1796_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1792_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1792_);
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
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
lean_del_object(v___x_1475_);
lean_dec(v_snd_1473_);
lean_dec(v_fst_1472_);
lean_del_object(v___x_1470_);
lean_dec(v_fst_1468_);
lean_dec_ref(v_letMuts_1450_);
lean_dec_ref(v_xs_1449_);
lean_dec_ref(v___x_1448_);
lean_dec(v_inv_1447_);
v_a_1804_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1790_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1790_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
v___jp_1480_:
{
if (v___y_1491_ == 0)
{
lean_object* v___x_1493_; 
lean_dec_ref(v___y_1490_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v___y_1484_);
v___x_1493_ = v___x_1475_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___y_1484_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_snd_1473_);
v___x_1493_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1495_; 
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 1, v___x_1493_);
lean_ctor_set(v___x_1470_, 0, v___y_1488_);
v___x_1495_ = v___x_1470_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___y_1488_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
v_a_1461_ = v___x_1495_;
goto v___jp_1460_;
}
}
}
else
{
lean_object* v___x_1499_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v___x_1478_);
lean_ctor_set(v___x_1475_, 0, v___y_1490_);
v___x_1499_ = v___x_1475_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___y_1490_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v___x_1478_);
v___x_1499_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1501_; 
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 1, v___x_1499_);
lean_ctor_set(v___x_1470_, 0, v___x_1477_);
v___x_1501_ = v___x_1470_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1502_; 
v___x_1502_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v___x_1501_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v_snd_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1578_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1503_);
lean_dec_ref_known(v___x_1502_, 1);
v_snd_1504_ = lean_ctor_get(v_a_1503_, 1);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_a_1503_);
if (v_isSharedCheck_1578_ == 0)
{
lean_object* v_unused_1579_; 
v_unused_1579_ = lean_ctor_get(v_a_1503_, 0);
lean_dec(v_unused_1579_);
v___x_1506_ = v_a_1503_;
v_isShared_1507_ = v_isSharedCheck_1578_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_snd_1504_);
lean_dec(v_a_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1578_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v_fst_1508_; lean_object* v_snd_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1577_; 
v_fst_1508_ = lean_ctor_get(v_snd_1504_, 0);
v_snd_1509_ = lean_ctor_get(v_snd_1504_, 1);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_snd_1504_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1511_ = v_snd_1504_;
v_isShared_1512_ = v_isSharedCheck_1577_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_snd_1509_);
lean_inc(v_fst_1508_);
lean_dec(v_snd_1504_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1577_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v_points_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; uint8_t v___x_1516_; 
v_points_1513_ = lean_ctor_get(v_snd_1473_, 0);
v___x_1514_ = lean_array_get_size(v_points_1513_);
v___x_1515_ = lean_array_get_size(v_snd_1509_);
v___x_1516_ = lean_nat_dec_lt(v___x_1514_, v___x_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1518_; 
lean_dec(v_snd_1509_);
lean_dec(v_fst_1508_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 1, v_snd_1473_);
lean_ctor_set(v___x_1511_, 0, v___y_1484_);
v___x_1518_ = v___x_1511_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___y_1484_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_snd_1473_);
v___x_1518_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1520_; 
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 1, v___x_1518_);
lean_ctor_set(v___x_1506_, 0, v___y_1488_);
v___x_1520_ = v___x_1506_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___y_1488_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
v_a_1461_ = v___x_1520_;
goto v___jp_1460_;
}
}
}
else
{
lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1574_; 
v_isSharedCheck_1574_ = !lean_is_exclusive(v_snd_1473_);
if (v_isSharedCheck_1574_ == 0)
{
lean_object* v_unused_1575_; lean_object* v_unused_1576_; 
v_unused_1575_ = lean_ctor_get(v_snd_1473_, 1);
lean_dec(v_unused_1575_);
v_unused_1576_ = lean_ctor_get(v_snd_1473_, 0);
lean_dec(v_unused_1576_);
v___x_1524_ = v_snd_1473_;
v_isShared_1525_ = v_isSharedCheck_1574_;
goto v_resetjp_1523_;
}
else
{
lean_dec(v_snd_1473_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1574_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1526_; uint8_t v___x_1527_; 
v___x_1526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__2));
v___x_1527_ = l_Lean_Expr_isConstOf(v_fst_1508_, v___x_1526_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__3));
lean_inc_ref(v___y_1486_);
lean_inc_ref(v___y_1482_);
lean_inc_ref(v___y_1481_);
v___x_1529_ = l_Lean_Name_mkStr4(v___y_1481_, v___y_1482_, v___y_1486_, v___x_1528_);
v___x_1530_ = lean_unsigned_to_nat(1u);
v___x_1531_ = l_Lean_Expr_isAppOfArity(v_fst_1508_, v___x_1529_, v___x_1530_);
lean_dec(v___x_1529_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1532_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4));
lean_inc_ref(v___y_1486_);
lean_inc_ref(v___y_1482_);
lean_inc_ref(v___y_1481_);
v___x_1533_ = l_Lean_Name_mkStr4(v___y_1481_, v___y_1482_, v___y_1486_, v___x_1532_);
v___x_1534_ = l_Lean_Expr_isAppOfArity(v_fst_1508_, v___x_1533_, v___x_1530_);
lean_dec(v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1537_; 
v___x_1535_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1535_, 0, v_fst_1508_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 1, v___x_1535_);
lean_ctor_set(v___x_1524_, 0, v_snd_1509_);
v___x_1537_ = v___x_1524_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_snd_1509_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_object* v___x_1539_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 1, v___x_1537_);
lean_ctor_set(v___x_1511_, 0, v___y_1484_);
v___x_1539_ = v___x_1511_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___y_1484_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
lean_object* v___x_1541_; 
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 1, v___x_1539_);
lean_ctor_set(v___x_1506_, 0, v___y_1488_);
v___x_1541_ = v___x_1506_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___y_1488_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
v_a_1461_ = v___x_1541_;
goto v___jp_1460_;
}
}
}
}
else
{
lean_object* v___x_1545_; lean_object* v___x_1547_; 
lean_dec(v_fst_1508_);
v___x_1545_ = lean_box(2);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 1, v___x_1545_);
lean_ctor_set(v___x_1524_, 0, v_snd_1509_);
v___x_1547_ = v___x_1524_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_snd_1509_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
lean_object* v___x_1549_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 1, v___x_1547_);
lean_ctor_set(v___x_1511_, 0, v___y_1484_);
v___x_1549_ = v___x_1511_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___y_1484_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1551_; 
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 1, v___x_1549_);
lean_ctor_set(v___x_1506_, 0, v___y_1488_);
v___x_1551_ = v___x_1506_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___y_1488_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
v_a_1461_ = v___x_1551_;
goto v___jp_1460_;
}
}
}
}
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1557_; 
lean_dec(v_fst_1508_);
v___x_1555_ = lean_box(1);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 1, v___x_1555_);
lean_ctor_set(v___x_1524_, 0, v_snd_1509_);
v___x_1557_ = v___x_1524_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_snd_1509_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1559_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 1, v___x_1557_);
lean_ctor_set(v___x_1511_, 0, v___y_1484_);
v___x_1559_ = v___x_1511_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___y_1484_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
lean_object* v___x_1561_; 
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 1, v___x_1559_);
lean_ctor_set(v___x_1506_, 0, v___y_1488_);
v___x_1561_ = v___x_1506_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___y_1488_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
v_a_1461_ = v___x_1561_;
goto v___jp_1460_;
}
}
}
}
}
else
{
lean_object* v___x_1566_; 
lean_dec(v_fst_1508_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 1, v___x_1479_);
lean_ctor_set(v___x_1524_, 0, v_snd_1509_);
v___x_1566_ = v___x_1524_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_snd_1509_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v___x_1479_);
v___x_1566_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1568_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 1, v___x_1566_);
lean_ctor_set(v___x_1511_, 0, v___y_1484_);
v___x_1568_ = v___x_1511_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___y_1484_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v___x_1566_);
v___x_1568_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1570_; 
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 1, v___x_1568_);
lean_ctor_set(v___x_1506_, 0, v___y_1488_);
v___x_1570_ = v___x_1506_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___y_1488_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
v_a_1461_ = v___x_1570_;
goto v___jp_1460_;
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
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec(v___y_1488_);
lean_dec(v___y_1484_);
lean_dec(v_snd_1473_);
lean_dec_ref(v_letMuts_1450_);
lean_dec_ref(v_xs_1449_);
lean_dec_ref(v___x_1448_);
lean_dec(v_inv_1447_);
v_a_1580_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1502_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1502_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
}
}
v___jp_1590_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1598_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1));
v___x_1599_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3));
v___x_1600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5));
v___x_1601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6));
v___x_1602_ = lean_unsigned_to_nat(3u);
v___x_1603_ = l_Lean_Expr_isAppOfArity(v___y_1591_, v___x_1601_, v___x_1602_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
lean_dec_ref(v___y_1591_);
lean_del_object(v___x_1475_);
lean_del_object(v___x_1470_);
v___x_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1604_, 0, v_suffixPoint_x3f_1593_);
lean_ctor_set(v___x_1604_, 1, v_snd_1473_);
v___x_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1605_, 0, v_prefixPoint_x3f_1592_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v_a_1461_ = v___x_1605_;
goto v___jp_1460_;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1606_ = l_Lean_Expr_appFn_x21(v___y_1591_);
v___x_1607_ = l_Lean_Expr_appArg_x21(v___x_1606_);
lean_dec_ref(v___x_1606_);
v___x_1608_ = l_Lean_Expr_appArg_x21(v___y_1591_);
lean_dec_ref(v___y_1591_);
v___x_1609_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__1));
v___x_1610_ = l_Lean_Expr_isAppOfArity(v___x_1607_, v___x_1609_, v___x_1602_);
if (v___x_1610_ == 0)
{
lean_dec_ref(v___x_1607_);
v___y_1481_ = v___x_1598_;
v___y_1482_ = v___x_1599_;
v___y_1483_ = v___y_1594_;
v___y_1484_ = v_suffixPoint_x3f_1593_;
v___y_1485_ = v___y_1596_;
v___y_1486_ = v___x_1600_;
v___y_1487_ = v___y_1595_;
v___y_1488_ = v_prefixPoint_x3f_1592_;
v___y_1489_ = v___y_1597_;
v___y_1490_ = v___x_1608_;
v___y_1491_ = v___x_1610_;
goto v___jp_1480_;
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1611_ = lean_unsigned_to_nat(2u);
v___x_1612_ = l_Lean_Expr_getAppNumArgs(v___x_1607_);
v___x_1613_ = lean_nat_sub(v___x_1612_, v___x_1611_);
lean_dec(v___x_1612_);
v___x_1614_ = lean_unsigned_to_nat(1u);
v___x_1615_ = lean_nat_sub(v___x_1613_, v___x_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = l_Lean_Expr_getRevArg_x21(v___x_1607_, v___x_1615_);
lean_dec_ref(v___x_1607_);
lean_inc(v_inv_1447_);
v___x_1617_ = l_Lean_mkMVar(v_inv_1447_);
v___x_1618_ = lean_expr_eqv(v___x_1616_, v___x_1617_);
lean_dec_ref(v___x_1617_);
lean_dec_ref(v___x_1616_);
v___y_1481_ = v___x_1598_;
v___y_1482_ = v___x_1599_;
v___y_1483_ = v___y_1594_;
v___y_1484_ = v_suffixPoint_x3f_1593_;
v___y_1485_ = v___y_1596_;
v___y_1486_ = v___x_1600_;
v___y_1487_ = v___y_1595_;
v___y_1488_ = v_prefixPoint_x3f_1592_;
v___y_1489_ = v___y_1597_;
v___y_1490_ = v___x_1608_;
v___y_1491_ = v___x_1618_;
goto v___jp_1480_;
}
}
}
v___jp_1620_:
{
lean_object* v___x_1631_; 
lean_inc(v_inv_1447_);
v___x_1631_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v___y_1625_, v_inv_1447_);
lean_dec_ref(v___y_1625_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_invariantUse_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1704_; 
v_invariantUse_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1704_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_invariantUse_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1704_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v_conditionIdx_1636_; lean_object* v_cursorSuffix_1637_; lean_object* v_letMutsTuple_1638_; uint8_t v___x_1639_; 
v_conditionIdx_1636_ = lean_ctor_get(v_invariantUse_1632_, 0);
lean_inc(v_conditionIdx_1636_);
v_cursorSuffix_1637_ = lean_ctor_get(v_invariantUse_1632_, 2);
lean_inc_ref(v_cursorSuffix_1637_);
v_letMutsTuple_1638_ = lean_ctor_get(v_invariantUse_1632_, 4);
lean_inc_ref(v_letMutsTuple_1638_);
lean_dec_ref(v_invariantUse_1632_);
v___x_1639_ = lean_nat_dec_eq(v_conditionIdx_1636_, v___x_1477_);
lean_dec(v_conditionIdx_1636_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_dec_ref(v_letMutsTuple_1638_);
lean_dec_ref(v_cursorSuffix_1637_);
lean_del_object(v___x_1634_);
lean_dec_ref(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_del_object(v___x_1475_);
lean_del_object(v___x_1470_);
v___x_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1640_, 0, v_fst_1472_);
lean_ctor_set(v___x_1640_, 1, v_snd_1473_);
v___x_1641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1641_, 0, v_prefixPoint_x3f_1626_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v_a_1461_ = v___x_1641_;
goto v___jp_1460_;
}
else
{
lean_object* v___x_1642_; uint8_t v___x_1643_; 
v___x_1642_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2));
v___x_1643_ = l_Lean_Expr_isAppOf(v_cursorSuffix_1637_, v___x_1642_);
if (v___x_1643_ == 0)
{
lean_dec_ref(v_letMutsTuple_1638_);
lean_dec_ref(v_cursorSuffix_1637_);
lean_del_object(v___x_1634_);
lean_dec_ref(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1621_);
v___y_1591_ = v___y_1622_;
v_prefixPoint_x3f_1592_ = v_prefixPoint_x3f_1626_;
v_suffixPoint_x3f_1593_ = v_fst_1472_;
v___y_1594_ = v___y_1627_;
v___y_1595_ = v___y_1628_;
v___y_1596_ = v___y_1629_;
v___y_1597_ = v___y_1630_;
goto v___jp_1590_;
}
else
{
uint8_t v___x_1644_; 
v___x_1644_ = l_Lean_Expr_isFVar(v_letMutsTuple_1638_);
if (v___x_1644_ == 0)
{
lean_dec_ref(v_letMutsTuple_1638_);
lean_dec_ref(v_cursorSuffix_1637_);
lean_del_object(v___x_1634_);
lean_dec_ref(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1621_);
v___y_1591_ = v___y_1622_;
v_prefixPoint_x3f_1592_ = v_prefixPoint_x3f_1626_;
v_suffixPoint_x3f_1593_ = v_fst_1472_;
v___y_1594_ = v___y_1627_;
v___y_1595_ = v___y_1628_;
v___y_1596_ = v___y_1629_;
v___y_1597_ = v___y_1630_;
goto v___jp_1590_;
}
else
{
lean_object* v___x_1645_; lean_object* v___f_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1645_ = lean_box(v___x_1639_);
lean_inc_ref(v___x_1448_);
lean_inc_ref(v_letMutsTuple_1638_);
v___f_1646_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1646_, 0, v_letMutsTuple_1638_);
lean_closure_set(v___f_1646_, 1, v___x_1448_);
lean_closure_set(v___f_1646_, 2, v___x_1645_);
v___x_1647_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8));
lean_inc_ref(v_xs_1449_);
v___x_1648_ = l_Lean_Meta_mkProjection(v_xs_1449_, v___x_1647_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1650_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 1);
v___x_1650_ = l_Lean_Meta_mkEq(v_a_1649_, v_cursorSuffix_1637_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1650_, 1);
v___x_1652_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed), 7, 2);
lean_closure_set(v___x_1652_, 0, v___y_1623_);
lean_closure_set(v___x_1652_, 1, v___f_1646_);
lean_inc(v_a_1619_);
v___x_1653_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_1619_, v___x_1652_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1655_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v___x_1653_, 1);
v___x_1655_ = l_Lean_Expr_replaceFVar(v_a_1654_, v_letMutsTuple_1638_, v_letMuts_1450_);
lean_dec(v_a_1654_);
if (lean_obj_tag(v_fst_1472_) == 1)
{
lean_object* v_val_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1674_; 
lean_dec(v_a_1651_);
lean_del_object(v___x_1634_);
lean_dec_ref(v___y_1624_);
v_val_1656_ = lean_ctor_get(v_fst_1472_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_fst_1472_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1658_ = v_fst_1472_;
v_isShared_1659_ = v_isSharedCheck_1674_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_val_1656_);
lean_dec(v_fst_1472_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1674_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v_lvl_1660_; lean_object* v_cursorPred_1661_; lean_object* v_letMutsPred_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1673_; 
v_lvl_1660_ = lean_ctor_get(v_val_1656_, 0);
v_cursorPred_1661_ = lean_ctor_get(v_val_1656_, 1);
v_letMutsPred_1662_ = lean_ctor_get(v_val_1656_, 2);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_val_1656_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1664_ = v_val_1656_;
v_isShared_1665_ = v_isSharedCheck_1673_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_letMutsPred_1662_);
lean_inc(v_cursorPred_1661_);
lean_inc(v_lvl_1660_);
lean_dec(v_val_1656_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1673_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1666_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v___y_1621_, v_letMutsPred_1662_, v___x_1655_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 2, v___x_1666_);
v___x_1668_ = v___x_1664_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_lvl_1660_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_cursorPred_1661_);
lean_ctor_set(v_reuseFailAlloc_1672_, 2, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
lean_object* v___x_1670_; 
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1668_);
v___x_1670_ = v___x_1658_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
v___y_1591_ = v___y_1622_;
v_prefixPoint_x3f_1592_ = v_prefixPoint_x3f_1626_;
v_suffixPoint_x3f_1593_ = v___x_1670_;
v___y_1594_ = v___y_1627_;
v___y_1595_ = v___y_1628_;
v___y_1596_ = v___y_1629_;
v___y_1597_ = v___y_1630_;
goto v___jp_1590_;
}
}
}
}
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1678_; 
lean_dec(v_fst_1472_);
v___x_1675_ = lean_apply_1(v___y_1624_, v_a_1651_);
v___x_1676_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1676_, 0, v___y_1621_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
lean_ctor_set(v___x_1676_, 2, v___x_1655_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set_tag(v___x_1634_, 1);
lean_ctor_set(v___x_1634_, 0, v___x_1676_);
v___x_1678_ = v___x_1634_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
v___y_1591_ = v___y_1622_;
v_prefixPoint_x3f_1592_ = v_prefixPoint_x3f_1626_;
v_suffixPoint_x3f_1593_ = v___x_1678_;
v___y_1594_ = v___y_1627_;
v___y_1595_ = v___y_1628_;
v___y_1596_ = v___y_1629_;
v___y_1597_ = v___y_1630_;
goto v___jp_1590_;
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_dec(v_a_1651_);
lean_dec_ref(v_letMutsTuple_1638_);
lean_del_object(v___x_1634_);
lean_dec(v_prefixPoint_x3f_1626_);
lean_dec_ref(v___y_1624_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_del_object(v___x_1475_);
lean_dec(v_snd_1473_);
lean_dec(v_fst_1472_);
lean_del_object(v___x_1470_);
lean_dec_ref(v_letMuts_1450_);
lean_dec_ref(v_xs_1449_);
lean_dec_ref(v___x_1448_);
lean_dec(v_inv_1447_);
v_a_1680_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1653_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1653_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_dec_ref(v___f_1646_);
lean_dec_ref(v_letMutsTuple_1638_);
lean_del_object(v___x_1634_);
lean_dec(v_prefixPoint_x3f_1626_);
lean_dec_ref(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_del_object(v___x_1475_);
lean_dec(v_snd_1473_);
lean_dec(v_fst_1472_);
lean_del_object(v___x_1470_);
lean_dec_ref(v_letMuts_1450_);
lean_dec_ref(v_xs_1449_);
lean_dec_ref(v___x_1448_);
lean_dec(v_inv_1447_);
v_a_1688_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1650_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1650_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec_ref(v___f_1646_);
lean_dec_ref(v_letMutsTuple_1638_);
lean_dec_ref(v_cursorSuffix_1637_);
lean_del_object(v___x_1634_);
lean_dec(v_prefixPoint_x3f_1626_);
lean_dec_ref(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_del_object(v___x_1475_);
lean_dec(v_snd_1473_);
lean_dec(v_fst_1472_);
lean_del_object(v___x_1470_);
lean_dec_ref(v_letMuts_1450_);
lean_dec_ref(v_xs_1449_);
lean_dec_ref(v___x_1448_);
lean_dec(v_inv_1447_);
v_a_1696_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1648_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1648_);
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
}
else
{
lean_dec(v___x_1631_);
lean_dec_ref(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1621_);
v___y_1591_ = v___y_1622_;
v_prefixPoint_x3f_1592_ = v_prefixPoint_x3f_1626_;
v_suffixPoint_x3f_1593_ = v_fst_1472_;
v___y_1594_ = v___y_1627_;
v___y_1595_ = v___y_1628_;
v___y_1596_ = v___y_1629_;
v___y_1597_ = v___y_1630_;
goto v___jp_1590_;
}
}
v___jp_1705_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_inc_ref(v___y_1710_);
v___x_1713_ = lean_apply_1(v___y_1710_, v___y_1708_);
lean_inc(v___y_1706_);
v___x_1714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1714_, 0, v___y_1706_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
lean_ctor_set(v___x_1714_, 2, v_a_1712_);
v___x_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
v___y_1621_ = v___y_1706_;
v___y_1622_ = v___y_1707_;
v___y_1623_ = v___y_1709_;
v___y_1624_ = v___y_1710_;
v___y_1625_ = v___y_1711_;
v_prefixPoint_x3f_1626_ = v___x_1715_;
v___y_1627_ = v___y_1455_;
v___y_1628_ = v___y_1456_;
v___y_1629_ = v___y_1457_;
v___y_1630_ = v___y_1458_;
goto v___jp_1620_;
}
v___jp_1716_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_inc_ref(v_a_1717_);
v___x_1718_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed), 6, 1);
lean_closure_set(v___x_1718_, 0, v_a_1717_);
lean_inc(v_a_1619_);
v___x_1719_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_1619_, v___x_1718_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 1);
if (lean_obj_tag(v_a_1720_) == 1)
{
lean_object* v_val_1721_; lean_object* v_snd_1722_; lean_object* v_fst_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1781_; 
v_val_1721_ = lean_ctor_get(v_a_1720_, 0);
lean_inc(v_val_1721_);
lean_dec_ref_known(v_a_1720_, 1);
v_snd_1722_ = lean_ctor_get(v_val_1721_, 1);
v_fst_1723_ = lean_ctor_get(v_val_1721_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v_val_1721_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1725_ = v_val_1721_;
v_isShared_1726_ = v_isSharedCheck_1781_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_snd_1722_);
lean_inc(v_fst_1723_);
lean_dec(v_val_1721_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1781_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v_fst_1727_; lean_object* v_snd_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1780_; 
v_fst_1727_ = lean_ctor_get(v_snd_1722_, 0);
v_snd_1728_ = lean_ctor_get(v_snd_1722_, 1);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_snd_1722_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1730_ = v_snd_1722_;
v_isShared_1731_ = v_isSharedCheck_1780_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_snd_1728_);
lean_inc(v_fst_1727_);
lean_dec(v_snd_1722_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1780_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___f_1732_; lean_object* v___x_1733_; 
lean_inc(v_fst_1723_);
v___f_1732_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1), 2, 1);
lean_closure_set(v___f_1732_, 0, v_fst_1723_);
lean_inc(v_inv_1447_);
v___x_1733_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_snd_1728_, v_inv_1447_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_invariantUse_1734_; lean_object* v_conditionIdx_1735_; lean_object* v_cursorPrefix_1736_; lean_object* v_letMutsTuple_1737_; uint8_t v___x_1738_; 
v_invariantUse_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc_ref(v_invariantUse_1734_);
lean_dec_ref_known(v___x_1733_, 1);
v_conditionIdx_1735_ = lean_ctor_get(v_invariantUse_1734_, 0);
lean_inc(v_conditionIdx_1735_);
v_cursorPrefix_1736_ = lean_ctor_get(v_invariantUse_1734_, 1);
lean_inc_ref(v_cursorPrefix_1736_);
v_letMutsTuple_1737_ = lean_ctor_get(v_invariantUse_1734_, 4);
lean_inc_ref(v_letMutsTuple_1737_);
lean_dec_ref(v_invariantUse_1734_);
v___x_1738_ = lean_nat_dec_eq(v_conditionIdx_1735_, v___x_1477_);
lean_dec(v_conditionIdx_1735_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1740_; 
lean_dec_ref(v_letMutsTuple_1737_);
lean_dec_ref(v_cursorPrefix_1736_);
lean_dec_ref(v___f_1732_);
lean_dec(v_snd_1728_);
lean_dec(v_fst_1727_);
lean_dec(v_fst_1723_);
lean_dec_ref(v_a_1717_);
lean_del_object(v___x_1475_);
lean_del_object(v___x_1470_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 1, v_snd_1473_);
lean_ctor_set(v___x_1730_, 0, v_fst_1472_);
v___x_1740_ = v___x_1730_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_fst_1472_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_snd_1473_);
v___x_1740_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1742_; 
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 1, v___x_1740_);
lean_ctor_set(v___x_1725_, 0, v_fst_1468_);
v___x_1742_ = v___x_1725_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_fst_1468_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
v_a_1461_ = v___x_1742_;
goto v___jp_1460_;
}
}
}
else
{
lean_object* v___x_1745_; uint8_t v___x_1746_; 
lean_del_object(v___x_1730_);
lean_del_object(v___x_1725_);
v___x_1745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2));
v___x_1746_ = l_Lean_Expr_isAppOf(v_cursorPrefix_1736_, v___x_1745_);
if (v___x_1746_ == 0)
{
lean_dec_ref(v_letMutsTuple_1737_);
lean_dec_ref(v_cursorPrefix_1736_);
v___y_1621_ = v_fst_1723_;
v___y_1622_ = v_a_1717_;
v___y_1623_ = v_snd_1728_;
v___y_1624_ = v___f_1732_;
v___y_1625_ = v_fst_1727_;
v_prefixPoint_x3f_1626_ = v_fst_1468_;
v___y_1627_ = v___y_1455_;
v___y_1628_ = v___y_1456_;
v___y_1629_ = v___y_1457_;
v___y_1630_ = v___y_1458_;
goto v___jp_1620_;
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_dec(v_fst_1468_);
v___x_1747_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__10));
lean_inc_ref(v_xs_1449_);
v___x_1748_ = l_Lean_Meta_mkProjection(v_xs_1449_, v___x_1747_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1750_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref_known(v___x_1748_, 1);
v___x_1750_ = l_Lean_Meta_mkEq(v_a_1749_, v_cursorPrefix_1736_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1752_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref_known(v___x_1750_, 1);
lean_inc_ref(v_letMuts_1450_);
v___x_1752_ = l_Lean_Meta_mkEq(v_letMuts_1450_, v_letMutsTuple_1737_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1754_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 1);
lean_inc(v_fst_1723_);
v___x_1754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(v_fst_1723_, v_a_1753_);
v___y_1706_ = v_fst_1723_;
v___y_1707_ = v_a_1717_;
v___y_1708_ = v_a_1751_;
v___y_1709_ = v_snd_1728_;
v___y_1710_ = v___f_1732_;
v___y_1711_ = v_fst_1727_;
v_a_1712_ = v___x_1754_;
goto v___jp_1705_;
}
else
{
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1755_; 
v_a_1755_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1752_, 1);
v___y_1706_ = v_fst_1723_;
v___y_1707_ = v_a_1717_;
v___y_1708_ = v_a_1751_;
v___y_1709_ = v_snd_1728_;
v___y_1710_ = v___f_1732_;
v___y_1711_ = v_fst_1727_;
v_a_1712_ = v_a_1755_;
goto v___jp_1705_;
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec(v_a_1751_);
lean_dec_ref(v___f_1732_);
lean_dec(v_snd_1728_);
lean_dec(v_fst_1727_);
lean_dec(v_fst_1723_);
lean_dec_ref(v_a_1717_);
lean_del_object(v___x_1475_);
lean_dec(v_snd_1473_);
lean_dec(v_fst_1472_);
lean_del_object(v___x_1470_);
lean_dec_ref(v_letMuts_1450_);
lean_dec_ref(v_xs_1449_);
lean_dec_ref(v___x_1448_);
lean_dec(v_inv_1447_);
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
lean_dec_ref(v_letMutsTuple_1737_);
lean_dec_ref(v___f_1732_);
lean_dec(v_snd_1728_);
lean_dec(v_fst_1727_);
lean_dec(v_fst_1723_);
lean_dec_ref(v_a_1717_);
lean_del_object(v___x_1475_);
lean_dec(v_snd_1473_);
lean_dec(v_fst_1472_);
lean_del_object(v___x_1470_);
lean_dec_ref(v_letMuts_1450_);
lean_dec_ref(v_xs_1449_);
lean_dec_ref(v___x_1448_);
lean_dec(v_inv_1447_);
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
lean_dec_ref(v_letMutsTuple_1737_);
lean_dec_ref(v_cursorPrefix_1736_);
lean_dec_ref(v___f_1732_);
lean_dec(v_snd_1728_);
lean_dec(v_fst_1727_);
lean_dec(v_fst_1723_);
lean_dec_ref(v_a_1717_);
lean_del_object(v___x_1475_);
lean_dec(v_snd_1473_);
lean_dec(v_fst_1472_);
lean_del_object(v___x_1470_);
lean_dec_ref(v_letMuts_1450_);
lean_dec_ref(v_xs_1449_);
lean_dec_ref(v___x_1448_);
lean_dec(v_inv_1447_);
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
}
else
{
lean_dec(v___x_1733_);
lean_del_object(v___x_1730_);
lean_del_object(v___x_1725_);
v___y_1621_ = v_fst_1723_;
v___y_1622_ = v_a_1717_;
v___y_1623_ = v_snd_1728_;
v___y_1624_ = v___f_1732_;
v___y_1625_ = v_fst_1727_;
v_prefixPoint_x3f_1626_ = v_fst_1468_;
v___y_1627_ = v___y_1455_;
v___y_1628_ = v___y_1456_;
v___y_1629_ = v___y_1457_;
v___y_1630_ = v___y_1458_;
goto v___jp_1620_;
}
}
}
}
else
{
lean_dec(v_a_1720_);
v___y_1591_ = v_a_1717_;
v_prefixPoint_x3f_1592_ = v_fst_1468_;
v_suffixPoint_x3f_1593_ = v_fst_1472_;
v___y_1594_ = v___y_1455_;
v___y_1595_ = v___y_1456_;
v___y_1596_ = v___y_1457_;
v___y_1597_ = v___y_1458_;
goto v___jp_1590_;
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec_ref(v_a_1717_);
lean_del_object(v___x_1475_);
lean_dec(v_snd_1473_);
lean_dec(v_fst_1472_);
lean_del_object(v___x_1470_);
lean_dec(v_fst_1468_);
lean_dec_ref(v_letMuts_1450_);
lean_dec_ref(v_xs_1449_);
lean_dec_ref(v___x_1448_);
lean_dec(v_inv_1447_);
v_a_1782_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1719_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1719_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
}
}
v___jp_1460_:
{
size_t v___x_1462_; size_t v___x_1463_; 
v___x_1462_ = ((size_t)1ULL);
v___x_1463_ = lean_usize_add(v_i_1453_, v___x_1462_);
v_i_1453_ = v___x_1463_;
v_b_1454_ = v_a_1461_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inv_1447_ = stack[0].m_obj;
lean_object* v___x_1448_ = stack[1].m_obj;
lean_object* v_xs_1449_ = stack[2].m_obj;
lean_object* v_letMuts_1450_ = stack[3].m_obj;
lean_object* v_as_1451_ = stack[4].m_obj;
size_t v_sz_1452_ = stack[5].m_num;
size_t v_i_1453_ = stack[6].m_num;
lean_object* v_b_1454_ = stack[7].m_obj;
lean_object* v___y_1455_ = stack[8].m_obj;
lean_object* v___y_1456_ = stack[9].m_obj;
lean_object* v___y_1457_ = stack[10].m_obj;
lean_object* v___y_1458_ = stack[11].m_obj;
lean_object* v_res_1814_;
v_res_1814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1447_, v___x_1448_, v_xs_1449_, v_letMuts_1450_, v_as_1451_, v_sz_1452_, v_i_1453_, v_b_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
stack->m_obj
 = v_res_1814_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___boxed(lean_object* v_inv_1815_, lean_object* v___x_1816_, lean_object* v_xs_1817_, lean_object* v_letMuts_1818_, lean_object* v_as_1819_, lean_object* v_sz_1820_, lean_object* v_i_1821_, lean_object* v_b_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
size_t v_sz_boxed_1828_; size_t v_i_boxed_1829_; lean_object* v_res_1830_; 
v_sz_boxed_1828_ = lean_unbox_usize(v_sz_1820_);
lean_dec(v_sz_1820_);
v_i_boxed_1829_ = lean_unbox_usize(v_i_1821_);
lean_dec(v_i_1821_);
v_res_1830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1815_, v___x_1816_, v_xs_1817_, v_letMuts_1818_, v_as_1819_, v_sz_boxed_1828_, v_i_boxed_1829_, v_b_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec_ref(v_as_1819_);
return v_res_1830_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(lean_object* v_vcs_1840_, lean_object* v_inv_1841_, lean_object* v_xs_1842_, lean_object* v_letMuts_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v_lctx_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; size_t v_sz_1852_; size_t v___x_1853_; lean_object* v___x_1854_; 
v_lctx_1849_ = lean_ctor_get(v_a_1844_, 2);
v___x_1850_ = lean_box(0);
v___x_1851_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__2));
v_sz_1852_ = lean_array_size(v_vcs_1840_);
v___x_1853_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1849_);
v___x_1854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1841_, v_lctx_1849_, v_xs_1842_, v_letMuts_1843_, v_vcs_1840_, v_sz_1852_, v___x_1853_, v___x_1851_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1898_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1857_ = v___x_1854_;
v_isShared_1858_ = v_isSharedCheck_1898_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1854_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1898_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v_snd_1863_; lean_object* v_fst_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1897_; 
v_snd_1863_ = lean_ctor_get(v_a_1855_, 1);
v_fst_1864_ = lean_ctor_get(v_a_1855_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_a_1855_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1866_ = v_a_1855_;
v_isShared_1867_ = v_isSharedCheck_1897_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_snd_1863_);
lean_inc(v_fst_1864_);
lean_dec(v_a_1855_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1897_;
goto v_resetjp_1865_;
}
v___jp_1859_:
{
lean_object* v___x_1861_; 
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 0, v___x_1850_);
v___x_1861_ = v___x_1857_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1850_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
v_resetjp_1865_:
{
if (lean_obj_tag(v_fst_1864_) == 0)
{
lean_del_object(v___x_1866_);
lean_dec(v_snd_1863_);
goto v___jp_1859_;
}
else
{
lean_object* v_fst_1868_; 
v_fst_1868_ = lean_ctor_get(v_snd_1863_, 0);
lean_inc(v_fst_1868_);
if (lean_obj_tag(v_fst_1868_) == 0)
{
lean_dec_ref_known(v_fst_1864_, 1);
lean_del_object(v___x_1866_);
lean_dec(v_snd_1863_);
goto v___jp_1859_;
}
else
{
lean_object* v_snd_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1895_; 
lean_del_object(v___x_1857_);
v_snd_1869_ = lean_ctor_get(v_snd_1863_, 1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_snd_1863_);
if (v_isSharedCheck_1895_ == 0)
{
lean_object* v_unused_1896_; 
v_unused_1896_ = lean_ctor_get(v_snd_1863_, 0);
lean_dec(v_unused_1896_);
v___x_1871_ = v_snd_1863_;
v_isShared_1872_ = v_isSharedCheck_1895_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_snd_1869_);
lean_dec(v_snd_1863_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1895_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v_val_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1894_; 
v_val_1873_ = lean_ctor_get(v_fst_1864_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v_fst_1864_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1875_ = v_fst_1864_;
v_isShared_1876_ = v_isSharedCheck_1894_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_val_1873_);
lean_dec(v_fst_1864_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1894_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v_val_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1893_; 
v_val_1877_ = lean_ctor_get(v_fst_1868_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_fst_1868_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1879_ = v_fst_1868_;
v_isShared_1880_ = v_isSharedCheck_1893_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_val_1877_);
lean_dec(v_fst_1868_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1893_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v_val_1877_);
v___x_1882_ = v___x_1871_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_val_1877_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_snd_1869_);
v___x_1882_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1884_; 
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 1, v___x_1882_);
lean_ctor_set(v___x_1866_, 0, v_val_1873_);
v___x_1884_ = v___x_1866_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_val_1873_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1886_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1884_);
v___x_1886_ = v___x_1879_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1888_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set_tag(v___x_1875_, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1886_);
v___x_1888_ = v___x_1875_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
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
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
v_a_1899_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1854_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1854_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_0interp(lean_interpreter_value* stack)
{
lean_object* v_vcs_1840_ = stack[0].m_obj;
lean_object* v_inv_1841_ = stack[1].m_obj;
lean_object* v_xs_1842_ = stack[2].m_obj;
lean_object* v_letMuts_1843_ = stack[3].m_obj;
lean_object* v_a_1844_ = stack[4].m_obj;
lean_object* v_a_1845_ = stack[5].m_obj;
lean_object* v_a_1846_ = stack[6].m_obj;
lean_object* v_a_1847_ = stack[7].m_obj;
lean_object* v_res_1907_;
v_res_1907_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_vcs_1840_, v_inv_1841_, v_xs_1842_, v_letMuts_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_);
stack->m_obj
 = v_res_1907_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___boxed(lean_object* v_vcs_1908_, lean_object* v_inv_1909_, lean_object* v_xs_1910_, lean_object* v_letMuts_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_vcs_1908_, v_inv_1909_, v_xs_1910_, v_letMuts_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
lean_dec(v_a_1915_);
lean_dec_ref(v_a_1914_);
lean_dec(v_a_1913_);
lean_dec_ref(v_a_1912_);
lean_dec_ref(v_vcs_1908_);
return v_res_1917_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(lean_object* v_inst_1918_, lean_object* v_a_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_a_1919_);
return v___x_1925_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1919_ = stack[1].m_obj;
lean_object* v___y_1920_ = stack[2].m_obj;
lean_object* v___y_1921_ = stack[3].m_obj;
lean_object* v___y_1922_ = stack[4].m_obj;
lean_object* v___y_1923_ = stack[5].m_obj;
lean_object* v_res_1926_;
v_res_1926_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(lean_box(0), v_a_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
stack->m_obj
 = v_res_1926_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___boxed(lean_object* v_inst_1927_, lean_object* v_a_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(v_inst_1927_, v_a_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
return v_res_1934_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(lean_object* v_m_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Lean_MVarId_getDecl(v_m_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v_userName_1943_; lean_object* v_lctx_1944_; lean_object* v_type_1945_; lean_object* v_localInstances_1946_; uint8_t v_kind_1947_; lean_object* v_numScopeArgs_1948_; lean_object* v___x_1949_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1941_, 1);
v_userName_1943_ = lean_ctor_get(v_a_1942_, 0);
lean_inc(v_userName_1943_);
v_lctx_1944_ = lean_ctor_get(v_a_1942_, 1);
lean_inc_ref(v_lctx_1944_);
v_type_1945_ = lean_ctor_get(v_a_1942_, 2);
lean_inc_ref(v_type_1945_);
v_localInstances_1946_ = lean_ctor_get(v_a_1942_, 4);
lean_inc_ref(v_localInstances_1946_);
v_kind_1947_ = lean_ctor_get_uint8(v_a_1942_, sizeof(void*)*7);
v_numScopeArgs_1948_ = lean_ctor_get(v_a_1942_, 5);
lean_inc(v_numScopeArgs_1948_);
lean_dec(v_a_1942_);
v___x_1949_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_1944_, v_localInstances_1946_, v_type_1945_, v_kind_1947_, v_userName_1943_, v_numScopeArgs_1948_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1958_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1952_ = v___x_1949_;
v_isShared_1953_ = v_isSharedCheck_1958_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1949_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1958_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; lean_object* v___x_1956_; 
v___x_1954_ = l_Lean_Expr_mvarId_x21(v_a_1950_);
lean_dec(v_a_1950_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v___x_1954_);
v___x_1956_ = v___x_1952_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1954_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
v_a_1959_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1949_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1949_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
v_a_1967_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1941_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1941_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1935_ = stack[0].m_obj;
lean_object* v_a_1936_ = stack[1].m_obj;
lean_object* v_a_1937_ = stack[2].m_obj;
lean_object* v_a_1938_ = stack[3].m_obj;
lean_object* v_a_1939_ = stack[4].m_obj;
lean_object* v_res_1975_;
v_res_1975_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v_m_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
stack->m_obj
 = v_res_1975_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar___boxed(lean_object* v_m_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v_m_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_);
lean_dec(v_a_1980_);
lean_dec_ref(v_a_1979_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__1(lean_object* v_msg_1983_){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = l_String_instInhabitedSlice;
v___x_1985_ = lean_panic_fn_borrowed(v___x_1984_, v_msg_1983_);
return v___x_1985_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(lean_object* v_s_1986_, lean_object* v_a_1987_, uint8_t v_b_1988_){
_start:
{
lean_object* v_str_1989_; lean_object* v_startInclusive_1990_; lean_object* v_endExclusive_1991_; lean_object* v___x_1992_; uint8_t v_decide_1993_; 
v_str_1989_ = lean_ctor_get(v_s_1986_, 0);
v_startInclusive_1990_ = lean_ctor_get(v_s_1986_, 1);
v_endExclusive_1991_ = lean_ctor_get(v_s_1986_, 2);
v___x_1992_ = lean_nat_sub(v_endExclusive_1991_, v_startInclusive_1990_);
v_decide_1993_ = lean_nat_dec_eq(v_a_1987_, v___x_1992_);
lean_dec(v___x_1992_);
if (v_decide_1993_ == 0)
{
uint32_t v___x_1994_; lean_object* v___x_1995_; uint32_t v___x_1996_; uint8_t v___x_1997_; 
v___x_1994_ = 64;
v___x_1995_ = lean_nat_add(v_startInclusive_1990_, v_a_1987_);
lean_dec(v_a_1987_);
v___x_1996_ = lean_string_utf8_get_fast(v_str_1989_, v___x_1995_);
v___x_1997_ = lean_uint32_dec_eq(v___x_1996_, v___x_1994_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = lean_string_utf8_next_fast(v_str_1989_, v___x_1995_);
lean_dec(v___x_1995_);
v___x_1999_ = lean_nat_sub(v___x_1998_, v_startInclusive_1990_);
v_a_1987_ = v___x_1999_;
v_b_1988_ = v___x_1997_;
goto _start;
}
else
{
lean_dec(v___x_1995_);
return v___x_1997_;
}
}
else
{
lean_dec(v_a_1987_);
return v_b_1988_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1986_ = stack[0].m_obj;
lean_object* v_a_1987_ = stack[1].m_obj;
uint8_t v_b_1988_ = stack[2].m_num;
uint8_t v_res_2001_;
v_res_2001_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_1986_, v_a_1987_, v_b_1988_);
stack->m_num = v_res_2001_;
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
uint8_t l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(lean_object* v_s_2008_){
_start:
{
lean_object* v_searcher_2009_; uint8_t v___x_2010_; uint8_t v___x_2011_; 
v_searcher_2009_ = lean_unsigned_to_nat(0u);
v___x_2010_ = 0;
v___x_2011_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_2008_, v_searcher_2009_, v___x_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT void l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2008_ = stack[0].m_obj;
uint8_t v_res_2012_;
v_res_2012_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v_s_2008_);
stack->m_num = v_res_2012_;
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2___boxed(lean_object* v_s_2013_){
_start:
{
uint8_t v_res_2014_; lean_object* v_r_2015_; 
v_res_2014_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v_s_2013_);
lean_dec_ref(v_s_2013_);
v_r_2015_ = lean_box(v_res_2014_);
return v_r_2015_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2019_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__2));
v___x_2020_ = lean_unsigned_to_nat(14u);
v___x_2021_ = lean_unsigned_to_nat(22u);
v___x_2022_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__1));
v___x_2023_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__0));
v___x_2024_ = l_mkPanicMessageWithDecl(v___x_2023_, v___x_2022_, v___x_2021_, v___x_2020_, v___x_2019_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(lean_object* v_x_2025_){
_start:
{
switch(lean_obj_tag(v_x_2025_))
{
case 1:
{
lean_object* v_info_2026_; lean_object* v_kind_2027_; lean_object* v_args_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2038_; 
v_info_2026_ = lean_ctor_get(v_x_2025_, 0);
v_kind_2027_ = lean_ctor_get(v_x_2025_, 1);
v_args_2028_ = lean_ctor_get(v_x_2025_, 2);
v_isSharedCheck_2038_ = !lean_is_exclusive(v_x_2025_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2030_ = v_x_2025_;
v_isShared_2031_ = v_isSharedCheck_2038_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_args_2028_);
lean_inc(v_kind_2027_);
lean_inc(v_info_2026_);
lean_dec(v_x_2025_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2038_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
size_t v_sz_2032_; size_t v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2036_; 
v_sz_2032_ = lean_array_size(v_args_2028_);
v___x_2033_ = ((size_t)0ULL);
v___x_2034_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(v_sz_2032_, v___x_2033_, v_args_2028_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 2, v___x_2034_);
v___x_2036_ = v___x_2030_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_info_2026_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_kind_2027_);
lean_ctor_set(v_reuseFailAlloc_2037_, 2, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
case 3:
{
lean_object* v_info_2039_; lean_object* v_rawVal_2040_; lean_object* v_val_2041_; lean_object* v_preresolved_2042_; uint8_t v___y_2044_; lean_object* v_str_2057_; lean_object* v_startPos_2058_; lean_object* v_stopPos_2059_; uint8_t v___y_2061_; uint8_t v___x_2067_; 
v_info_2039_ = lean_ctor_get(v_x_2025_, 0);
v_rawVal_2040_ = lean_ctor_get(v_x_2025_, 1);
v_val_2041_ = lean_ctor_get(v_x_2025_, 2);
v_preresolved_2042_ = lean_ctor_get(v_x_2025_, 3);
v_str_2057_ = lean_ctor_get(v_rawVal_2040_, 0);
v_startPos_2058_ = lean_ctor_get(v_rawVal_2040_, 1);
v_stopPos_2059_ = lean_ctor_get(v_rawVal_2040_, 2);
v___x_2067_ = lean_string_is_valid_pos(v_str_2057_, v_startPos_2058_);
if (v___x_2067_ == 0)
{
v___y_2061_ = v___x_2067_;
goto v___jp_2060_;
}
else
{
uint8_t v___x_2068_; 
v___x_2068_ = lean_string_is_valid_pos(v_str_2057_, v_stopPos_2059_);
if (v___x_2068_ == 0)
{
v___y_2061_ = v___x_2068_;
goto v___jp_2060_;
}
else
{
uint8_t v___x_2069_; 
v___x_2069_ = lean_nat_dec_le(v_startPos_2058_, v_stopPos_2059_);
v___y_2061_ = v___x_2069_;
goto v___jp_2060_;
}
}
v___jp_2043_:
{
if (v___y_2044_ == 0)
{
lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2052_; 
lean_inc(v_preresolved_2042_);
lean_inc(v_val_2041_);
lean_inc_ref(v_rawVal_2040_);
lean_inc(v_info_2039_);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_x_2025_);
if (v_isSharedCheck_2052_ == 0)
{
lean_object* v_unused_2053_; lean_object* v_unused_2054_; lean_object* v_unused_2055_; lean_object* v_unused_2056_; 
v_unused_2053_ = lean_ctor_get(v_x_2025_, 3);
lean_dec(v_unused_2053_);
v_unused_2054_ = lean_ctor_get(v_x_2025_, 2);
lean_dec(v_unused_2054_);
v_unused_2055_ = lean_ctor_get(v_x_2025_, 1);
lean_dec(v_unused_2055_);
v_unused_2056_ = lean_ctor_get(v_x_2025_, 0);
lean_dec(v_unused_2056_);
v___x_2046_ = v_x_2025_;
v_isShared_2047_ = v_isSharedCheck_2052_;
goto v_resetjp_2045_;
}
else
{
lean_dec(v_x_2025_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2052_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2048_ = l_Lean_Name_eraseMacroScopes(v_val_2041_);
lean_dec(v_val_2041_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 2, v___x_2048_);
v___x_2050_ = v___x_2046_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_info_2039_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_rawVal_2040_);
lean_ctor_set(v_reuseFailAlloc_2051_, 2, v___x_2048_);
lean_ctor_set(v_reuseFailAlloc_2051_, 3, v_preresolved_2042_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
else
{
return v_x_2025_;
}
}
v___jp_2060_:
{
if (v___y_2061_ == 0)
{
lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2062_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3);
v___x_2063_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__1(v___x_2062_);
v___x_2064_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v___x_2063_);
lean_dec_ref(v___x_2063_);
v___y_2044_ = v___x_2064_;
goto v___jp_2043_;
}
else
{
lean_object* v___x_2065_; uint8_t v___x_2066_; 
lean_inc(v_stopPos_2059_);
lean_inc(v_startPos_2058_);
lean_inc_ref(v_str_2057_);
v___x_2065_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2065_, 0, v_str_2057_);
lean_ctor_set(v___x_2065_, 1, v_startPos_2058_);
lean_ctor_set(v___x_2065_, 2, v_stopPos_2059_);
v___x_2066_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v___x_2065_);
lean_dec_ref_known(v___x_2065_, 3);
v___y_2044_ = v___x_2066_;
goto v___jp_2043_;
}
}
}
default: 
{
return v_x_2025_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(size_t v_sz_2070_, size_t v_i_2071_, lean_object* v_bs_2072_){
_start:
{
uint8_t v___x_2073_; 
v___x_2073_ = lean_usize_dec_lt(v_i_2071_, v_sz_2070_);
if (v___x_2073_ == 0)
{
return v_bs_2072_;
}
else
{
lean_object* v_v_2074_; lean_object* v___x_2075_; lean_object* v_bs_x27_2076_; lean_object* v___x_2077_; size_t v___x_2078_; size_t v___x_2079_; lean_object* v___x_2080_; 
v_v_2074_ = lean_array_uget(v_bs_2072_, v_i_2071_);
v___x_2075_ = lean_unsigned_to_nat(0u);
v_bs_x27_2076_ = lean_array_uset(v_bs_2072_, v_i_2071_, v___x_2075_);
v___x_2077_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_v_2074_);
v___x_2078_ = ((size_t)1ULL);
v___x_2079_ = lean_usize_add(v_i_2071_, v___x_2078_);
v___x_2080_ = lean_array_uset(v_bs_x27_2076_, v_i_2071_, v___x_2077_);
v_i_2071_ = v___x_2079_;
v_bs_2072_ = v___x_2080_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2070_ = stack[0].m_num;
size_t v_i_2071_ = stack[1].m_num;
lean_object* v_bs_2072_ = stack[2].m_obj;
lean_object* v_res_2082_;
v_res_2082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(v_sz_2070_, v_i_2071_, v_bs_2072_);
stack->m_obj
 = v_res_2082_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0___boxed(lean_object* v_sz_2083_, lean_object* v_i_2084_, lean_object* v_bs_2085_){
_start:
{
size_t v_sz_boxed_2086_; size_t v_i_boxed_2087_; lean_object* v_res_2088_; 
v_sz_boxed_2086_ = lean_unbox_usize(v_sz_2083_);
lean_dec(v_sz_2083_);
v_i_boxed_2087_ = lean_unbox_usize(v_i_2084_);
lean_dec(v_i_2084_);
v_res_2088_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(v_sz_boxed_2086_, v_i_boxed_2087_, v_bs_2085_);
return v_res_2088_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2(lean_object* v_s_2089_, lean_object* v_inst_2090_, lean_object* v_R_2091_, lean_object* v_a_2092_, uint8_t v_b_2093_, lean_object* v_c_2094_){
_start:
{
uint8_t v___x_2095_; 
v___x_2095_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_2089_, v_a_2092_, v_b_2093_);
return v___x_2095_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2089_ = stack[0].m_obj;
lean_object* v_a_2092_ = stack[3].m_obj;
uint8_t v_b_2093_ = stack[4].m_num;
uint8_t v_res_2096_;
v_res_2096_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2(v_s_2089_, lean_box(0), lean_box(0), v_a_2092_, v_b_2093_, lean_box(0));
stack->m_num = v_res_2096_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___boxed(lean_object* v_s_2097_, lean_object* v_inst_2098_, lean_object* v_R_2099_, lean_object* v_a_2100_, lean_object* v_b_2101_, lean_object* v_c_2102_){
_start:
{
uint8_t v_b_boxed_2103_; uint8_t v_res_2104_; lean_object* v_r_2105_; 
v_b_boxed_2103_ = lean_unbox(v_b_2101_);
v_res_2104_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2(v_s_2097_, v_inst_2098_, v_R_2099_, v_a_2100_, v_b_boxed_2103_, v_c_2102_);
lean_dec_ref(v_s_2097_);
v_r_2105_ = lean_box(v_res_2104_);
return v_r_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter___redArg(lean_object* v_x_2106_, lean_object* v_h__1_2107_, lean_object* v_h__2_2108_, lean_object* v_h__3_2109_, lean_object* v_h__4_2110_){
_start:
{
switch(lean_obj_tag(v_x_2106_))
{
case 0:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
lean_dec(v_h__3_2109_);
lean_dec(v_h__2_2108_);
lean_dec(v_h__1_2107_);
v___x_2111_ = lean_box(0);
v___x_2112_ = lean_apply_1(v_h__4_2110_, v___x_2111_);
return v___x_2112_;
}
case 1:
{
lean_object* v_info_2113_; lean_object* v_kind_2114_; lean_object* v_args_2115_; lean_object* v___x_2116_; 
lean_dec(v_h__4_2110_);
lean_dec(v_h__3_2109_);
lean_dec(v_h__1_2107_);
v_info_2113_ = lean_ctor_get(v_x_2106_, 0);
lean_inc(v_info_2113_);
v_kind_2114_ = lean_ctor_get(v_x_2106_, 1);
lean_inc(v_kind_2114_);
v_args_2115_ = lean_ctor_get(v_x_2106_, 2);
lean_inc_ref(v_args_2115_);
lean_dec_ref_known(v_x_2106_, 3);
v___x_2116_ = lean_apply_3(v_h__2_2108_, v_info_2113_, v_kind_2114_, v_args_2115_);
return v___x_2116_;
}
case 2:
{
lean_object* v_info_2117_; lean_object* v_val_2118_; lean_object* v___x_2119_; 
lean_dec(v_h__4_2110_);
lean_dec(v_h__2_2108_);
lean_dec(v_h__1_2107_);
v_info_2117_ = lean_ctor_get(v_x_2106_, 0);
lean_inc(v_info_2117_);
v_val_2118_ = lean_ctor_get(v_x_2106_, 1);
lean_inc_ref(v_val_2118_);
lean_dec_ref_known(v_x_2106_, 2);
v___x_2119_ = lean_apply_2(v_h__3_2109_, v_info_2117_, v_val_2118_);
return v___x_2119_;
}
default: 
{
lean_object* v_info_2120_; lean_object* v_rawVal_2121_; lean_object* v_val_2122_; lean_object* v_preresolved_2123_; lean_object* v___x_2124_; 
lean_dec(v_h__4_2110_);
lean_dec(v_h__3_2109_);
lean_dec(v_h__2_2108_);
v_info_2120_ = lean_ctor_get(v_x_2106_, 0);
lean_inc(v_info_2120_);
v_rawVal_2121_ = lean_ctor_get(v_x_2106_, 1);
lean_inc_ref(v_rawVal_2121_);
v_val_2122_ = lean_ctor_get(v_x_2106_, 2);
lean_inc(v_val_2122_);
v_preresolved_2123_ = lean_ctor_get(v_x_2106_, 3);
lean_inc(v_preresolved_2123_);
lean_dec_ref_known(v_x_2106_, 4);
v___x_2124_ = lean_apply_4(v_h__1_2107_, v_info_2120_, v_rawVal_2121_, v_val_2122_, v_preresolved_2123_);
return v___x_2124_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter(lean_object* v_motive_2125_, lean_object* v_x_2126_, lean_object* v_h__1_2127_, lean_object* v_h__2_2128_, lean_object* v_h__3_2129_, lean_object* v_h__4_2130_){
_start:
{
switch(lean_obj_tag(v_x_2126_))
{
case 0:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
lean_dec(v_h__3_2129_);
lean_dec(v_h__2_2128_);
lean_dec(v_h__1_2127_);
v___x_2131_ = lean_box(0);
v___x_2132_ = lean_apply_1(v_h__4_2130_, v___x_2131_);
return v___x_2132_;
}
case 1:
{
lean_object* v_info_2133_; lean_object* v_kind_2134_; lean_object* v_args_2135_; lean_object* v___x_2136_; 
lean_dec(v_h__4_2130_);
lean_dec(v_h__3_2129_);
lean_dec(v_h__1_2127_);
v_info_2133_ = lean_ctor_get(v_x_2126_, 0);
lean_inc(v_info_2133_);
v_kind_2134_ = lean_ctor_get(v_x_2126_, 1);
lean_inc(v_kind_2134_);
v_args_2135_ = lean_ctor_get(v_x_2126_, 2);
lean_inc_ref(v_args_2135_);
lean_dec_ref_known(v_x_2126_, 3);
v___x_2136_ = lean_apply_3(v_h__2_2128_, v_info_2133_, v_kind_2134_, v_args_2135_);
return v___x_2136_;
}
case 2:
{
lean_object* v_info_2137_; lean_object* v_val_2138_; lean_object* v___x_2139_; 
lean_dec(v_h__4_2130_);
lean_dec(v_h__2_2128_);
lean_dec(v_h__1_2127_);
v_info_2137_ = lean_ctor_get(v_x_2126_, 0);
lean_inc(v_info_2137_);
v_val_2138_ = lean_ctor_get(v_x_2126_, 1);
lean_inc_ref(v_val_2138_);
lean_dec_ref_known(v_x_2126_, 2);
v___x_2139_ = lean_apply_2(v_h__3_2129_, v_info_2137_, v_val_2138_);
return v___x_2139_;
}
default: 
{
lean_object* v_info_2140_; lean_object* v_rawVal_2141_; lean_object* v_val_2142_; lean_object* v_preresolved_2143_; lean_object* v___x_2144_; 
lean_dec(v_h__4_2130_);
lean_dec(v_h__3_2129_);
lean_dec(v_h__2_2128_);
v_info_2140_ = lean_ctor_get(v_x_2126_, 0);
lean_inc(v_info_2140_);
v_rawVal_2141_ = lean_ctor_get(v_x_2126_, 1);
lean_inc_ref(v_rawVal_2141_);
v_val_2142_ = lean_ctor_get(v_x_2126_, 2);
lean_inc(v_val_2142_);
v_preresolved_2143_ = lean_ctor_get(v_x_2126_, 3);
lean_inc(v_preresolved_2143_);
lean_dec_ref_known(v_x_2126_, 4);
v___x_2144_ = lean_apply_4(v_h__1_2127_, v_info_2140_, v_rawVal_2141_, v_val_2142_, v_preresolved_2143_);
return v___x_2144_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_2145_, lean_object* v_h__1_2146_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = lean_apply_2(v_h__1_2146_, v_x_2145_, lean_box(0));
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_2148_, lean_object* v_P_2149_, lean_object* v_motive_2150_, lean_object* v_x_2151_, lean_object* v_h__1_2152_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = lean_apply_2(v_h__1_2152_, v_x_2151_, lean_box(0));
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___redArg(lean_object* v_syn_2154_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_syn_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(lean_object* v_name_2156_, lean_object* v_syn_2157_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_syn_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___boxed(lean_object* v_name_2159_, lean_object* v_syn_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(v_name_2159_, v_syn_2160_);
lean_dec(v_name_2159_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(lean_object* v_e_2168_){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2195_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__1));
v___x_2196_ = lean_unsigned_to_nat(2u);
v___x_2197_ = l_Lean_Expr_isAppOfArity(v_e_2168_, v___x_2195_, v___x_2196_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
v___x_2198_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
v___x_2199_ = lean_unsigned_to_nat(3u);
v___x_2200_ = l_Lean_Expr_isAppOfArity(v_e_2168_, v___x_2198_, v___x_2199_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; uint8_t v___x_2202_; 
v___x_2201_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
v___x_2202_ = l_Lean_Expr_isAppOfArity(v_e_2168_, v___x_2201_, v___x_2199_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2203_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_2204_ = l_Lean_Expr_isAppOfArity(v_e_2168_, v___x_2203_, v___x_2199_);
if (v___x_2204_ == 0)
{
goto v___jp_2169_;
}
else
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Lean_Expr_appArg_x21(v_e_2168_);
if (lean_obj_tag(v___x_2205_) == 6)
{
lean_object* v_binderName_2206_; lean_object* v_binderType_2207_; lean_object* v_body_2208_; uint8_t v_binderInfo_2209_; lean_object* v___x_2210_; 
lean_dec_ref(v_e_2168_);
v_binderName_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_binderName_2206_);
v_binderType_2207_ = lean_ctor_get(v___x_2205_, 1);
lean_inc_ref(v_binderType_2207_);
v_body_2208_ = lean_ctor_get(v___x_2205_, 2);
lean_inc_ref(v_body_2208_);
v_binderInfo_2209_ = lean_ctor_get_uint8(v___x_2205_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_2205_, 3);
v___x_2210_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_2208_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_dec_ref(v_binderType_2207_);
lean_dec(v_binderName_2206_);
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
v___x_2220_ = l_Lean_mkForall(v_binderName_2206_, v_binderInfo_2209_, v_binderType_2207_, v_snd_2216_);
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
else
{
lean_dec_ref(v___x_2205_);
goto v___jp_2169_;
}
}
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2229_ = l_Lean_Expr_appFn_x21(v_e_2168_);
v___x_2230_ = l_Lean_Expr_appArg_x21(v___x_2229_);
lean_dec_ref(v___x_2229_);
v___x_2231_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2230_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_dec_ref(v_e_2168_);
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
v___x_2234_ = l_Lean_Expr_appArg_x21(v_e_2168_);
lean_dec_ref(v_e_2168_);
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
v___x_2245_ = l_Lean_mkOr(v_snd_2233_, v_snd_2241_);
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
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2254_ = l_Lean_Expr_appFn_x21(v_e_2168_);
v___x_2255_ = l_Lean_Expr_appArg_x21(v___x_2254_);
lean_dec_ref(v___x_2254_);
v___x_2256_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2255_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_dec_ref(v_e_2168_);
return v___x_2256_;
}
else
{
lean_object* v_val_2257_; lean_object* v_snd_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v_val_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_val_2257_);
lean_dec_ref_known(v___x_2256_, 1);
v_snd_2258_ = lean_ctor_get(v_val_2257_, 1);
lean_inc(v_snd_2258_);
lean_dec(v_val_2257_);
v___x_2259_ = l_Lean_Expr_appArg_x21(v_e_2168_);
lean_dec_ref(v_e_2168_);
v___x_2260_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2259_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_dec(v_snd_2258_);
return v___x_2260_;
}
else
{
lean_object* v_val_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2278_; 
v_val_2261_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2263_ = v___x_2260_;
v_isShared_2264_ = v_isSharedCheck_2278_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_val_2261_);
lean_dec(v___x_2260_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2278_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v_fst_2265_; lean_object* v_snd_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2277_; 
v_fst_2265_ = lean_ctor_get(v_val_2261_, 0);
v_snd_2266_ = lean_ctor_get(v_val_2261_, 1);
v_isSharedCheck_2277_ = !lean_is_exclusive(v_val_2261_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2268_ = v_val_2261_;
v_isShared_2269_ = v_isSharedCheck_2277_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_snd_2266_);
lean_inc(v_fst_2265_);
lean_dec(v_val_2261_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2277_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; lean_object* v___x_2272_; 
v___x_2270_ = l_Lean_mkAnd(v_snd_2258_, v_snd_2266_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 1, v___x_2270_);
v___x_2272_ = v___x_2268_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_fst_2265_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
lean_object* v___x_2274_; 
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 0, v___x_2272_);
v___x_2274_ = v___x_2263_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
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
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2279_ = lean_box(0);
v___x_2280_ = l_Lean_Expr_getAppFn(v_e_2168_);
v___x_2281_ = l_Lean_Expr_constLevels_x21(v___x_2280_);
lean_dec_ref(v___x_2280_);
v___x_2282_ = lean_unsigned_to_nat(0u);
v___x_2283_ = l_List_get_x21Internal___redArg(v___x_2279_, v___x_2281_, v___x_2282_);
lean_dec(v___x_2281_);
v___x_2284_ = lean_unsigned_to_nat(1u);
v___x_2285_ = l_Lean_Expr_getAppNumArgs(v_e_2168_);
v___x_2286_ = lean_nat_sub(v___x_2285_, v___x_2284_);
lean_dec(v___x_2285_);
v___x_2287_ = lean_nat_sub(v___x_2286_, v___x_2284_);
lean_dec(v___x_2286_);
v___x_2288_ = l_Lean_Expr_getRevArg_x21(v_e_2168_, v___x_2287_);
lean_dec_ref(v_e_2168_);
v___x_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2283_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
return v___x_2290_;
}
v___jp_2169_:
{
if (lean_obj_tag(v_e_2168_) == 8)
{
lean_object* v_declName_2170_; lean_object* v_type_2171_; lean_object* v_value_2172_; lean_object* v_body_2173_; uint8_t v_nondep_2174_; lean_object* v___x_2175_; 
v_declName_2170_ = lean_ctor_get(v_e_2168_, 0);
lean_inc(v_declName_2170_);
v_type_2171_ = lean_ctor_get(v_e_2168_, 1);
lean_inc_ref(v_type_2171_);
v_value_2172_ = lean_ctor_get(v_e_2168_, 2);
lean_inc_ref(v_value_2172_);
v_body_2173_ = lean_ctor_get(v_e_2168_, 3);
lean_inc_ref(v_body_2173_);
v_nondep_2174_ = lean_ctor_get_uint8(v_e_2168_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2168_, 4);
v___x_2175_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_2173_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_dec_ref(v_value_2172_);
lean_dec_ref(v_type_2171_);
lean_dec(v_declName_2170_);
return v___x_2175_;
}
else
{
lean_object* v_val_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2193_; 
v_val_2176_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2178_ = v___x_2175_;
v_isShared_2179_ = v_isSharedCheck_2193_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_val_2176_);
lean_dec(v___x_2175_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2193_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v_fst_2180_; lean_object* v_snd_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2192_; 
v_fst_2180_ = lean_ctor_get(v_val_2176_, 0);
v_snd_2181_ = lean_ctor_get(v_val_2176_, 1);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_val_2176_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2183_ = v_val_2176_;
v_isShared_2184_ = v_isSharedCheck_2192_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_snd_2181_);
lean_inc(v_fst_2180_);
lean_dec(v_val_2176_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2192_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2185_; lean_object* v___x_2187_; 
v___x_2185_ = l_Lean_Expr_letE___override(v_declName_2170_, v_type_2171_, v_value_2172_, v_snd_2181_, v_nondep_2174_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 1, v___x_2185_);
v___x_2187_ = v___x_2183_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_fst_2180_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2189_; 
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v___x_2187_);
v___x_2189_ = v___x_2178_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
}
else
{
lean_object* v___x_2194_; 
lean_dec_ref(v_e_2168_);
v___x_2194_ = lean_box(0);
return v___x_2194_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(lean_object* v_e_2291_){
_start:
{
lean_object* v___x_2292_; 
lean_inc_ref(v_e_2291_);
v___x_2292_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_e_2291_);
if (lean_obj_tag(v___x_2292_) == 0)
{
return v_e_2291_;
}
else
{
lean_object* v_val_2293_; lean_object* v_fst_2294_; lean_object* v_snd_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
lean_dec_ref(v_e_2291_);
v_val_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_val_2293_);
lean_dec_ref_known(v___x_2292_, 1);
v_fst_2294_ = lean_ctor_get(v_val_2293_, 0);
lean_inc_n(v_fst_2294_, 2);
v_snd_2295_ = lean_ctor_get(v_val_2293_, 1);
lean_inc(v_snd_2295_);
lean_dec(v_val_2293_);
v___x_2296_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_2294_);
v___x_2297_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_2294_, v___x_2296_, v_snd_2295_);
return v___x_2297_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6(void){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Array_mkArray0___redArg();
return v___x_2308_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__23));
v___x_2347_ = l_String_toRawSubstring_x27(v___x_2346_);
return v___x_2347_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30(void){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29));
v___x_2364_ = l_String_toRawSubstring_x27(v___x_2363_);
return v___x_2364_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(lean_object* v_handlers_2379_, lean_object* v_default_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v___x_2386_; lean_object* v_handlers_2387_; 
v___x_2386_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v_handlers_2387_ = l_Lean_Syntax_SepArray_ofElems(v___x_2386_, v_handlers_2379_);
switch(lean_obj_tag(v_default_2380_))
{
case 0:
{
lean_object* v_ref_2388_; uint8_t v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v_ref_2388_ = lean_ctor_get(v_a_2383_, 2);
v___x_2389_ = 0;
v___x_2390_ = l_Lean_SourceInfo_fromRef(v_ref_2388_, v___x_2389_);
v___x_2391_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__2));
v___x_2392_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__3));
lean_inc_n(v___x_2390_, 3);
v___x_2393_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2390_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
v___x_2394_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2395_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2396_ = l_Array_append___redArg(v___x_2395_, v_handlers_2387_);
lean_dec_ref(v_handlers_2387_);
v___x_2397_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2390_);
lean_ctor_set(v___x_2397_, 1, v___x_2394_);
lean_ctor_set(v___x_2397_, 2, v___x_2396_);
v___x_2398_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2399_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2390_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = l_Lean_Syntax_node3(v___x_2390_, v___x_2391_, v___x_2393_, v___x_2397_, v___x_2399_);
v___x_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2400_);
return v___x_2401_;
}
case 1:
{
lean_object* v_toCold_2402_; lean_object* v_ref_2403_; lean_object* v_quotContext_2404_; lean_object* v_currMacroScope_2405_; uint8_t v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v_toCold_2402_ = lean_ctor_get(v_a_2383_, 0);
v_ref_2403_ = lean_ctor_get(v_a_2383_, 2);
v_quotContext_2404_ = lean_ctor_get(v_toCold_2402_, 8);
v_currMacroScope_2405_ = lean_ctor_get(v_toCold_2402_, 9);
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
v___x_2421_ = l_Array_append___redArg(v___x_2420_, v_handlers_2387_);
lean_dec_ref(v_handlers_2387_);
v___x_2422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2407_);
lean_ctor_set(v___x_2422_, 1, v___x_2386_);
v___x_2423_ = lean_array_push(v___x_2421_, v___x_2422_);
v___x_2424_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24);
v___x_2425_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25));
lean_inc(v_currMacroScope_2405_);
lean_inc(v_quotContext_2404_);
v___x_2426_ = l_Lean_addMacroScope(v_quotContext_2404_, v___x_2425_, v_currMacroScope_2405_);
v___x_2427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__28));
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
case 2:
{
lean_object* v_toCold_2440_; lean_object* v_ref_2441_; lean_object* v_quotContext_2442_; lean_object* v_currMacroScope_2443_; uint8_t v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v_toCold_2440_ = lean_ctor_get(v_a_2383_, 0);
v_ref_2441_ = lean_ctor_get(v_a_2383_, 2);
v_quotContext_2442_ = lean_ctor_get(v_toCold_2440_, 8);
v_currMacroScope_2443_ = lean_ctor_get(v_toCold_2440_, 9);
v___x_2444_ = 0;
v___x_2445_ = l_Lean_SourceInfo_fromRef(v_ref_2441_, v___x_2444_);
v___x_2446_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2447_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2445_, 12);
v___x_2448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2445_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2450_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2451_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2452_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2445_);
lean_ctor_set(v___x_2454_, 1, v___x_2452_);
v___x_2455_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2456_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2445_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
v___x_2458_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2459_ = l_Array_append___redArg(v___x_2458_, v_handlers_2387_);
lean_dec_ref(v_handlers_2387_);
v___x_2460_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2445_);
lean_ctor_set(v___x_2460_, 1, v___x_2386_);
v___x_2461_ = lean_array_push(v___x_2459_, v___x_2460_);
v___x_2462_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30);
v___x_2463_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31));
lean_inc(v_currMacroScope_2443_);
lean_inc(v_quotContext_2442_);
v___x_2464_ = l_Lean_addMacroScope(v_quotContext_2442_, v___x_2463_, v_currMacroScope_2443_);
v___x_2465_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__34));
v___x_2466_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2445_);
lean_ctor_set(v___x_2466_, 1, v___x_2462_);
lean_ctor_set(v___x_2466_, 2, v___x_2464_);
lean_ctor_set(v___x_2466_, 3, v___x_2465_);
v___x_2467_ = lean_array_push(v___x_2461_, v___x_2466_);
v___x_2468_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2445_);
lean_ctor_set(v___x_2468_, 1, v___x_2451_);
lean_ctor_set(v___x_2468_, 2, v___x_2467_);
v___x_2469_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2445_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = l_Lean_Syntax_node3(v___x_2445_, v___x_2455_, v___x_2457_, v___x_2468_, v___x_2470_);
v___x_2472_ = l_Lean_Syntax_node2(v___x_2445_, v___x_2453_, v___x_2454_, v___x_2471_);
v___x_2473_ = l_Lean_Syntax_node1(v___x_2445_, v___x_2451_, v___x_2472_);
v___x_2474_ = l_Lean_Syntax_node1(v___x_2445_, v___x_2450_, v___x_2473_);
v___x_2475_ = l_Lean_Syntax_node1(v___x_2445_, v___x_2449_, v___x_2474_);
v___x_2476_ = l_Lean_Syntax_node2(v___x_2445_, v___x_2446_, v___x_2448_, v___x_2475_);
v___x_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2476_);
return v___x_2477_;
}
default: 
{
lean_object* v_e_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v_e_2478_ = lean_ctor_get(v_default_2380_, 0);
lean_inc_ref(v_e_2478_);
lean_dec_ref_known(v_default_2380_, 1);
v___x_2479_ = lean_box(1);
v___x_2480_ = l_Lean_PrettyPrinter_delab(v_e_2478_, v___x_2479_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2517_; 
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2483_ = v___x_2480_;
v_isShared_2484_ = v_isSharedCheck_2517_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2480_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2517_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v_ref_2485_; uint8_t v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2515_; 
v_ref_2485_ = lean_ctor_get(v_a_2383_, 2);
v___x_2486_ = 0;
v___x_2487_ = l_Lean_SourceInfo_fromRef(v_ref_2485_, v___x_2486_);
v___x_2488_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2489_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2487_, 11);
v___x_2490_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2487_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
v___x_2491_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2492_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2493_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2494_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2495_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2496_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2487_);
lean_ctor_set(v___x_2496_, 1, v___x_2494_);
v___x_2497_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2498_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2499_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2487_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2501_ = l_Array_append___redArg(v___x_2500_, v_handlers_2387_);
lean_dec_ref(v_handlers_2387_);
v___x_2502_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2487_);
lean_ctor_set(v___x_2502_, 1, v___x_2386_);
v___x_2503_ = lean_array_push(v___x_2501_, v___x_2502_);
v___x_2504_ = lean_array_push(v___x_2503_, v_a_2481_);
v___x_2505_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2487_);
lean_ctor_set(v___x_2505_, 1, v___x_2493_);
lean_ctor_set(v___x_2505_, 2, v___x_2504_);
v___x_2506_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2507_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2487_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
v___x_2508_ = l_Lean_Syntax_node3(v___x_2487_, v___x_2497_, v___x_2499_, v___x_2505_, v___x_2507_);
v___x_2509_ = l_Lean_Syntax_node2(v___x_2487_, v___x_2495_, v___x_2496_, v___x_2508_);
v___x_2510_ = l_Lean_Syntax_node1(v___x_2487_, v___x_2493_, v___x_2509_);
v___x_2511_ = l_Lean_Syntax_node1(v___x_2487_, v___x_2492_, v___x_2510_);
v___x_2512_ = l_Lean_Syntax_node1(v___x_2487_, v___x_2491_, v___x_2511_);
v___x_2513_ = l_Lean_Syntax_node2(v___x_2487_, v___x_2488_, v___x_2490_, v___x_2512_);
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 0, v___x_2513_);
v___x_2515_ = v___x_2483_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2513_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
else
{
lean_dec_ref(v_handlers_2387_);
return v___x_2480_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions_0interp(lean_interpreter_value* stack)
{
lean_object* v_handlers_2379_ = stack[0].m_obj;
lean_object* v_default_2380_ = stack[1].m_obj;
lean_object* v_a_2381_ = stack[2].m_obj;
lean_object* v_a_2382_ = stack[3].m_obj;
lean_object* v_a_2383_ = stack[4].m_obj;
lean_object* v_a_2384_ = stack[5].m_obj;
lean_object* v_res_2518_;
v_res_2518_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_handlers_2379_, v_default_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_);
stack->m_obj
 = v_res_2518_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___boxed(lean_object* v_handlers_2519_, lean_object* v_default_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_handlers_2519_, v_default_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
lean_dec(v_a_2524_);
lean_dec_ref(v_a_2523_);
lean_dec(v_a_2522_);
lean_dec_ref(v_a_2521_);
lean_dec_ref(v_handlers_2519_);
return v_res_2526_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(lean_object* v_e_2527_, lean_object* v___y_2528_){
_start:
{
uint8_t v___x_2530_; 
v___x_2530_ = l_Lean_Expr_hasMVar(v_e_2527_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; 
v___x_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2531_, 0, v_e_2527_);
return v___x_2531_;
}
else
{
lean_object* v___x_2532_; lean_object* v_mctx_2533_; lean_object* v___x_2534_; lean_object* v_fst_2535_; lean_object* v_snd_2536_; lean_object* v___x_2537_; lean_object* v_cache_2538_; lean_object* v_zetaDeltaFVarIds_2539_; lean_object* v_postponed_2540_; lean_object* v_diag_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2550_; 
v___x_2532_ = lean_st_ref_get(v___y_2528_);
v_mctx_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc_ref(v_mctx_2533_);
lean_dec(v___x_2532_);
v___x_2534_ = l_Lean_instantiateMVarsCore(v_mctx_2533_, v_e_2527_);
v_fst_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_fst_2535_);
v_snd_2536_ = lean_ctor_get(v___x_2534_, 1);
lean_inc(v_snd_2536_);
lean_dec_ref(v___x_2534_);
v___x_2537_ = lean_st_ref_take(v___y_2528_);
v_cache_2538_ = lean_ctor_get(v___x_2537_, 1);
v_zetaDeltaFVarIds_2539_ = lean_ctor_get(v___x_2537_, 2);
v_postponed_2540_ = lean_ctor_get(v___x_2537_, 3);
v_diag_2541_ = lean_ctor_get(v___x_2537_, 4);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2550_ == 0)
{
lean_object* v_unused_2551_; 
v_unused_2551_ = lean_ctor_get(v___x_2537_, 0);
lean_dec(v_unused_2551_);
v___x_2543_ = v___x_2537_;
v_isShared_2544_ = v_isSharedCheck_2550_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_diag_2541_);
lean_inc(v_postponed_2540_);
lean_inc(v_zetaDeltaFVarIds_2539_);
lean_inc(v_cache_2538_);
lean_dec(v___x_2537_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2550_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v_snd_2536_);
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_snd_2536_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v_cache_2538_);
lean_ctor_set(v_reuseFailAlloc_2549_, 2, v_zetaDeltaFVarIds_2539_);
lean_ctor_set(v_reuseFailAlloc_2549_, 3, v_postponed_2540_);
lean_ctor_set(v_reuseFailAlloc_2549_, 4, v_diag_2541_);
v___x_2546_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = lean_st_ref_put(v___y_2528_, v___x_2546_);
v___x_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2548_, 0, v_fst_2535_);
return v___x_2548_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2527_ = stack[0].m_obj;
lean_object* v___y_2528_ = stack[1].m_obj;
lean_object* v_res_2552_;
v_res_2552_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2527_, v___y_2528_);
stack->m_obj
 = v_res_2552_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg___boxed(lean_object* v_e_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2553_, v___y_2554_);
lean_dec(v___y_2554_);
return v_res_2556_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(lean_object* v_e_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v___x_2567_; 
v___x_2567_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2557_, v___y_2563_);
return v___x_2567_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2557_ = stack[0].m_obj;
lean_object* v___y_2558_ = stack[1].m_obj;
lean_object* v___y_2559_ = stack[2].m_obj;
lean_object* v___y_2560_ = stack[3].m_obj;
lean_object* v___y_2561_ = stack[4].m_obj;
lean_object* v___y_2562_ = stack[5].m_obj;
lean_object* v___y_2563_ = stack[6].m_obj;
lean_object* v___y_2564_ = stack[7].m_obj;
lean_object* v___y_2565_ = stack[8].m_obj;
lean_object* v_res_2568_;
v_res_2568_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(v_e_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
stack->m_obj
 = v_res_2568_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___boxed(lean_object* v_e_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(v_e_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
return v_res_2579_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(lean_object* v_x_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v___x_2590_; 
lean_inc(v___y_2584_);
lean_inc_ref(v___y_2583_);
lean_inc(v___y_2582_);
lean_inc_ref(v___y_2581_);
v___x_2590_ = lean_apply_9(v_x_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, lean_box(0));
return v___x_2590_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2580_ = stack[0].m_obj;
lean_object* v___y_2581_ = stack[1].m_obj;
lean_object* v___y_2582_ = stack[2].m_obj;
lean_object* v___y_2583_ = stack[3].m_obj;
lean_object* v___y_2584_ = stack[4].m_obj;
lean_object* v___y_2585_ = stack[5].m_obj;
lean_object* v___y_2586_ = stack[6].m_obj;
lean_object* v___y_2587_ = stack[7].m_obj;
lean_object* v___y_2588_ = stack[8].m_obj;
lean_object* v_res_2591_;
v_res_2591_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(v_x_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
stack->m_obj
 = v_res_2591_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed(lean_object* v_x_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(v_x_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
return v_res_2602_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(lean_object* v_mvarId_2603_, lean_object* v_x_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v___f_2614_; lean_object* v___x_2615_; 
lean_inc(v___y_2608_);
lean_inc_ref(v___y_2607_);
lean_inc(v___y_2606_);
lean_inc_ref(v___y_2605_);
v___f_2614_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2614_, 0, v_x_2604_);
lean_closure_set(v___f_2614_, 1, v___y_2605_);
lean_closure_set(v___f_2614_, 2, v___y_2606_);
lean_closure_set(v___f_2614_, 3, v___y_2607_);
lean_closure_set(v___f_2614_, 4, v___y_2608_);
v___x_2615_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2603_, v___f_2614_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
if (lean_obj_tag(v___x_2615_) == 0)
{
return v___x_2615_;
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2615_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2615_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2603_ = stack[0].m_obj;
lean_object* v_x_2604_ = stack[1].m_obj;
lean_object* v___y_2605_ = stack[2].m_obj;
lean_object* v___y_2606_ = stack[3].m_obj;
lean_object* v___y_2607_ = stack[4].m_obj;
lean_object* v___y_2608_ = stack[5].m_obj;
lean_object* v___y_2609_ = stack[6].m_obj;
lean_object* v___y_2610_ = stack[7].m_obj;
lean_object* v___y_2611_ = stack[8].m_obj;
lean_object* v___y_2612_ = stack[9].m_obj;
lean_object* v_res_2624_;
v_res_2624_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2603_, v_x_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
stack->m_obj
 = v_res_2624_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___boxed(lean_object* v_mvarId_2625_, lean_object* v_x_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2625_, v_x_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
return v_res_2636_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(lean_object* v_00_u03b1_2637_, lean_object* v_mvarId_2638_, lean_object* v_x_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2638_, v_x_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
return v___x_2649_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2638_ = stack[1].m_obj;
lean_object* v_x_2639_ = stack[2].m_obj;
lean_object* v___y_2640_ = stack[3].m_obj;
lean_object* v___y_2641_ = stack[4].m_obj;
lean_object* v___y_2642_ = stack[5].m_obj;
lean_object* v___y_2643_ = stack[6].m_obj;
lean_object* v___y_2644_ = stack[7].m_obj;
lean_object* v___y_2645_ = stack[8].m_obj;
lean_object* v___y_2646_ = stack[9].m_obj;
lean_object* v___y_2647_ = stack[10].m_obj;
lean_object* v_res_2650_;
v_res_2650_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(lean_box(0), v_mvarId_2638_, v_x_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
stack->m_obj
 = v_res_2650_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___boxed(lean_object* v_00_u03b1_2651_, lean_object* v_mvarId_2652_, lean_object* v_x_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(v_00_u03b1_2651_, v_mvarId_2652_, v_x_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
return v_res_2663_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(lean_object* v_a_2664_, lean_object* v_inv_2665_, lean_object* v_xs_2666_, uint8_t v___x_2667_, lean_object* v___x_2668_, lean_object* v_letMuts_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v___x_2679_; 
lean_inc_ref(v_letMuts_2669_);
lean_inc_ref(v_xs_2666_);
v___x_2679_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_a_2664_, v_inv_2665_, v_xs_2666_, v_letMuts_2669_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2756_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2682_ = v___x_2679_;
v_isShared_2683_ = v_isSharedCheck_2756_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2679_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2756_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
if (lean_obj_tag(v_a_2680_) == 1)
{
lean_object* v_val_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2751_; 
lean_del_object(v___x_2682_);
v_val_2684_ = lean_ctor_get(v_a_2680_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v_a_2680_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2686_ = v_a_2680_;
v_isShared_2687_ = v_isSharedCheck_2751_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_val_2684_);
lean_dec(v_a_2680_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2751_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v_snd_2688_; lean_object* v_fst_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2750_; 
v_snd_2688_ = lean_ctor_get(v_val_2684_, 1);
v_fst_2689_ = lean_ctor_get(v_val_2684_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v_val_2684_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2691_ = v_val_2684_;
v_isShared_2692_ = v_isSharedCheck_2750_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_snd_2688_);
lean_inc(v_fst_2689_);
lean_dec(v_val_2684_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2750_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v_fst_2693_; lean_object* v_snd_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2749_; 
v_fst_2693_ = lean_ctor_get(v_snd_2688_, 0);
v_snd_2694_ = lean_ctor_get(v_snd_2688_, 1);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_snd_2688_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2696_ = v_snd_2688_;
v_isShared_2697_ = v_isSharedCheck_2749_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_snd_2694_);
lean_inc(v_fst_2693_);
lean_dec(v_snd_2688_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2749_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v_lvl_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; uint8_t v___x_2707_; uint8_t v___x_2708_; lean_object* v___x_2709_; 
v_lvl_2698_ = lean_ctor_get(v_fst_2689_, 0);
lean_inc(v_lvl_2698_);
v___x_2699_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2689_);
lean_inc(v_fst_2693_);
v___x_2700_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2693_);
v___x_2701_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(v_lvl_2698_, v___x_2699_, v___x_2700_);
v___x_2702_ = lean_unsigned_to_nat(2u);
v___x_2703_ = lean_mk_empty_array_with_capacity(v___x_2702_);
v___x_2704_ = lean_array_push(v___x_2703_, v_xs_2666_);
lean_inc_ref(v_letMuts_2669_);
v___x_2705_ = lean_array_push(v___x_2704_, v_letMuts_2669_);
v___x_2706_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v___x_2701_);
v___x_2707_ = 0;
v___x_2708_ = 1;
v___x_2709_ = l_Lean_Meta_mkLambdaFVars(v___x_2705_, v___x_2706_, v___x_2707_, v___x_2667_, v___x_2707_, v___x_2667_, v___x_2708_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
lean_dec_ref(v___x_2705_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v_letMutsPred_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref_known(v___x_2709_, 1);
v_letMutsPred_2711_ = lean_ctor_get(v_fst_2693_, 2);
lean_inc_ref(v_letMutsPred_2711_);
lean_dec(v_fst_2693_);
v___x_2712_ = lean_mk_empty_array_with_capacity(v___x_2668_);
v___x_2713_ = lean_array_push(v___x_2712_, v_letMuts_2669_);
v___x_2714_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v_letMutsPred_2711_);
v___x_2715_ = l_Lean_Meta_mkLambdaFVars(v___x_2713_, v___x_2714_, v___x_2707_, v___x_2667_, v___x_2707_, v___x_2667_, v___x_2708_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
lean_dec_ref(v___x_2713_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2732_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2732_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2732_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v_a_2716_);
v___x_2721_ = v___x_2696_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2716_);
lean_ctor_set(v_reuseFailAlloc_2731_, 1, v_snd_2694_);
v___x_2721_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
lean_object* v___x_2723_; 
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 1, v___x_2721_);
lean_ctor_set(v___x_2691_, 0, v_a_2710_);
v___x_2723_ = v___x_2691_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2710_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v___x_2721_);
v___x_2723_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
lean_object* v___x_2725_; 
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v___x_2723_);
v___x_2725_ = v___x_2686_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2723_);
v___x_2725_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
lean_object* v___x_2727_; 
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v___x_2725_);
v___x_2727_ = v___x_2718_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
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
}
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
lean_dec(v_a_2710_);
lean_del_object(v___x_2696_);
lean_dec(v_snd_2694_);
lean_del_object(v___x_2691_);
lean_del_object(v___x_2686_);
v_a_2733_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___x_2715_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2715_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_del_object(v___x_2696_);
lean_dec(v_snd_2694_);
lean_dec(v_fst_2693_);
lean_del_object(v___x_2691_);
lean_del_object(v___x_2686_);
lean_dec_ref(v_letMuts_2669_);
v_a_2741_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2709_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2709_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2752_; lean_object* v___x_2754_; 
lean_dec(v_a_2680_);
lean_dec_ref(v_letMuts_2669_);
lean_dec_ref(v_xs_2666_);
v___x_2752_ = lean_box(0);
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 0, v___x_2752_);
v___x_2754_ = v___x_2682_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2752_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_dec_ref(v_letMuts_2669_);
lean_dec_ref(v_xs_2666_);
v_a_2757_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2679_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2679_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2664_ = stack[0].m_obj;
lean_object* v_inv_2665_ = stack[1].m_obj;
lean_object* v_xs_2666_ = stack[2].m_obj;
uint8_t v___x_2667_ = stack[3].m_num;
lean_object* v___x_2668_ = stack[4].m_obj;
lean_object* v_letMuts_2669_ = stack[5].m_obj;
lean_object* v___y_2670_ = stack[6].m_obj;
lean_object* v___y_2671_ = stack[7].m_obj;
lean_object* v___y_2672_ = stack[8].m_obj;
lean_object* v___y_2673_ = stack[9].m_obj;
lean_object* v___y_2674_ = stack[10].m_obj;
lean_object* v___y_2675_ = stack[11].m_obj;
lean_object* v___y_2676_ = stack[12].m_obj;
lean_object* v___y_2677_ = stack[13].m_obj;
lean_object* v_res_2765_;
v_res_2765_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(v_a_2664_, v_inv_2665_, v_xs_2666_, v___x_2667_, v___x_2668_, v_letMuts_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
stack->m_obj
 = v_res_2765_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed(lean_object* v_a_2766_, lean_object* v_inv_2767_, lean_object* v_xs_2768_, lean_object* v___x_2769_, lean_object* v___x_2770_, lean_object* v_letMuts_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
uint8_t v___x_77311__boxed_2781_; lean_object* v_res_2782_; 
v___x_77311__boxed_2781_ = lean_unbox(v___x_2769_);
v_res_2782_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(v_a_2766_, v_inv_2767_, v_xs_2768_, v___x_77311__boxed_2781_, v___x_2770_, v_letMuts_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___x_2770_);
lean_dec_ref(v_a_2766_);
return v_res_2782_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(lean_object* v_k_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v_b_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v___x_2794_; 
lean_inc(v___y_2792_);
lean_inc_ref(v___y_2791_);
lean_inc(v___y_2790_);
lean_inc_ref(v___y_2789_);
lean_inc(v___y_2787_);
lean_inc_ref(v___y_2786_);
lean_inc(v___y_2785_);
lean_inc_ref(v___y_2784_);
v___x_2794_ = lean_apply_10(v_k_2783_, v_b_2788_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, lean_box(0));
return v___x_2794_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2783_ = stack[0].m_obj;
lean_object* v___y_2784_ = stack[1].m_obj;
lean_object* v___y_2785_ = stack[2].m_obj;
lean_object* v___y_2786_ = stack[3].m_obj;
lean_object* v___y_2787_ = stack[4].m_obj;
lean_object* v_b_2788_ = stack[5].m_obj;
lean_object* v___y_2789_ = stack[6].m_obj;
lean_object* v___y_2790_ = stack[7].m_obj;
lean_object* v___y_2791_ = stack[8].m_obj;
lean_object* v___y_2792_ = stack[9].m_obj;
lean_object* v_res_2795_;
v_res_2795_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(v_k_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v_b_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
stack->m_obj
 = v_res_2795_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_k_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v_b_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(v_k_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v_b_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
return v_res_2807_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(lean_object* v_name_2808_, uint8_t v_bi_2809_, lean_object* v_type_2810_, lean_object* v_k_2811_, uint8_t v_kind_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___f_2822_; lean_object* v___x_2823_; 
lean_inc(v___y_2816_);
lean_inc_ref(v___y_2815_);
lean_inc(v___y_2814_);
lean_inc_ref(v___y_2813_);
v___f_2822_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2822_, 0, v_k_2811_);
lean_closure_set(v___f_2822_, 1, v___y_2813_);
lean_closure_set(v___f_2822_, 2, v___y_2814_);
lean_closure_set(v___f_2822_, 3, v___y_2815_);
lean_closure_set(v___f_2822_, 4, v___y_2816_);
v___x_2823_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2808_, v_bi_2809_, v_type_2810_, v___f_2822_, v_kind_2812_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2823_) == 0)
{
return v___x_2823_;
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2823_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2823_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2808_ = stack[0].m_obj;
uint8_t v_bi_2809_ = stack[1].m_num;
lean_object* v_type_2810_ = stack[2].m_obj;
lean_object* v_k_2811_ = stack[3].m_obj;
uint8_t v_kind_2812_ = stack[4].m_num;
lean_object* v___y_2813_ = stack[5].m_obj;
lean_object* v___y_2814_ = stack[6].m_obj;
lean_object* v___y_2815_ = stack[7].m_obj;
lean_object* v___y_2816_ = stack[8].m_obj;
lean_object* v___y_2817_ = stack[9].m_obj;
lean_object* v___y_2818_ = stack[10].m_obj;
lean_object* v___y_2819_ = stack[11].m_obj;
lean_object* v___y_2820_ = stack[12].m_obj;
lean_object* v_res_2832_;
v_res_2832_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2808_, v_bi_2809_, v_type_2810_, v_k_2811_, v_kind_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
stack->m_obj
 = v_res_2832_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___boxed(lean_object* v_name_2833_, lean_object* v_bi_2834_, lean_object* v_type_2835_, lean_object* v_k_2836_, lean_object* v_kind_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
uint8_t v_bi_boxed_2847_; uint8_t v_kind_boxed_2848_; lean_object* v_res_2849_; 
v_bi_boxed_2847_ = lean_unbox(v_bi_2834_);
v_kind_boxed_2848_ = lean_unbox(v_kind_2837_);
v_res_2849_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2833_, v_bi_boxed_2847_, v_type_2835_, v_k_2836_, v_kind_boxed_2848_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
return v_res_2849_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(lean_object* v_name_2850_, lean_object* v_type_2851_, lean_object* v_k_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
uint8_t v___x_2862_; uint8_t v___x_2863_; lean_object* v___x_2864_; 
v___x_2862_ = 0;
v___x_2863_ = 0;
v___x_2864_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2850_, v___x_2862_, v_type_2851_, v_k_2852_, v___x_2863_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
return v___x_2864_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2850_ = stack[0].m_obj;
lean_object* v_type_2851_ = stack[1].m_obj;
lean_object* v_k_2852_ = stack[2].m_obj;
lean_object* v___y_2853_ = stack[3].m_obj;
lean_object* v___y_2854_ = stack[4].m_obj;
lean_object* v___y_2855_ = stack[5].m_obj;
lean_object* v___y_2856_ = stack[6].m_obj;
lean_object* v___y_2857_ = stack[7].m_obj;
lean_object* v___y_2858_ = stack[8].m_obj;
lean_object* v___y_2859_ = stack[9].m_obj;
lean_object* v___y_2860_ = stack[10].m_obj;
lean_object* v_res_2865_;
v_res_2865_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_2850_, v_type_2851_, v_k_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
stack->m_obj
 = v_res_2865_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg___boxed(lean_object* v_name_2866_, lean_object* v_type_2867_, lean_object* v_k_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_2866_, v_type_2867_, v_k_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
return v_res_2878_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(lean_object* v_a_2882_, lean_object* v_inv_2883_, uint8_t v___x_2884_, lean_object* v___x_2885_, lean_object* v_arg_2886_, lean_object* v_xs_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v___x_2897_; lean_object* v___f_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2897_ = lean_box(v___x_2884_);
v___f_2898_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed), 15, 5);
lean_closure_set(v___f_2898_, 0, v_a_2882_);
lean_closure_set(v___f_2898_, 1, v_inv_2883_);
lean_closure_set(v___f_2898_, 2, v_xs_2887_);
lean_closure_set(v___f_2898_, 3, v___x_2897_);
lean_closure_set(v___f_2898_, 4, v___x_2885_);
v___x_2899_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_2900_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_2899_, v_arg_2886_, v___f_2898_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
return v___x_2900_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2882_ = stack[0].m_obj;
lean_object* v_inv_2883_ = stack[1].m_obj;
uint8_t v___x_2884_ = stack[2].m_num;
lean_object* v___x_2885_ = stack[3].m_obj;
lean_object* v_arg_2886_ = stack[4].m_obj;
lean_object* v_xs_2887_ = stack[5].m_obj;
lean_object* v___y_2888_ = stack[6].m_obj;
lean_object* v___y_2889_ = stack[7].m_obj;
lean_object* v___y_2890_ = stack[8].m_obj;
lean_object* v___y_2891_ = stack[9].m_obj;
lean_object* v___y_2892_ = stack[10].m_obj;
lean_object* v___y_2893_ = stack[11].m_obj;
lean_object* v___y_2894_ = stack[12].m_obj;
lean_object* v___y_2895_ = stack[13].m_obj;
lean_object* v_res_2901_;
v_res_2901_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(v_a_2882_, v_inv_2883_, v___x_2884_, v___x_2885_, v_arg_2886_, v_xs_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
stack->m_obj
 = v_res_2901_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed(lean_object* v_a_2902_, lean_object* v_inv_2903_, lean_object* v___x_2904_, lean_object* v___x_2905_, lean_object* v_arg_2906_, lean_object* v_xs_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
uint8_t v___x_77807__boxed_2917_; lean_object* v_res_2918_; 
v___x_77807__boxed_2917_ = lean_unbox(v___x_2904_);
v_res_2918_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(v_a_2902_, v_inv_2903_, v___x_77807__boxed_2917_, v___x_2905_, v_arg_2906_, v_xs_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
return v_res_2918_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2922_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2);
v___x_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
return v___x_2924_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4(void){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2925_ = lean_unsigned_to_nat(32u);
v___x_2926_ = lean_mk_empty_array_with_capacity(v___x_2925_);
v___x_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
return v___x_2927_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(lean_object* v_fst_2928_, lean_object* v_xs_2929_, lean_object* v_fst_2930_, lean_object* v_r_2931_, lean_object* v___x_2932_, lean_object* v_fst_2933_, uint8_t v___x_2934_, lean_object* v___x_2935_, lean_object* v_letMuts_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v___x_2946_; 
lean_inc_ref(v_fst_2928_);
v___x_2946_ = l_Lean_Meta_mkNone(v_fst_2928_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2947_);
lean_dec_ref_known(v___x_2946_, 1);
v___x_2948_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_2949_ = lean_unsigned_to_nat(2u);
v___x_2950_ = lean_mk_empty_array_with_capacity(v___x_2949_);
lean_inc_ref(v___x_2950_);
v___x_2951_ = lean_array_push(v___x_2950_, v_a_2947_);
lean_inc_ref(v_letMuts_2936_);
v___x_2952_ = lean_array_push(v___x_2951_, v_letMuts_2936_);
v___x_2953_ = l_Lean_Meta_mkAppM(v___x_2948_, v___x_2952_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2953_, 1);
lean_inc_ref(v___x_2950_);
v___x_2955_ = lean_array_push(v___x_2950_, v_xs_2929_);
v___x_2956_ = lean_array_push(v___x_2955_, v_a_2954_);
v___x_2957_ = l_Lean_Expr_beta(v_fst_2930_, v___x_2956_);
v___x_2958_ = l_Lean_Meta_mkSome(v_fst_2928_, v_r_2931_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2958_, 1);
v___x_2960_ = lean_array_push(v___x_2950_, v_a_2959_);
v___x_2961_ = lean_array_push(v___x_2960_, v_letMuts_2936_);
v___x_2962_ = l_Lean_Meta_mkAppM(v___x_2948_, v___x_2961_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2962_, 1);
v___x_2964_ = lean_mk_empty_array_with_capacity(v___x_2932_);
lean_inc_ref(v___x_2964_);
v___x_2965_ = lean_array_push(v___x_2964_, v_a_2963_);
v___x_2966_ = l_Lean_Expr_beta(v_fst_2933_, v___x_2965_);
v___x_2967_ = l_Lean_Meta_getSimpTheorems___redArg(v___y_2944_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2969_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
lean_dec_ref_known(v___x_2967_, 1);
v___x_2969_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_2944_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; lean_object* v___x_2971_; uint8_t v___x_2972_; uint8_t v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
lean_dec_ref_known(v___x_2969_, 1);
v___x_2971_ = lean_unsigned_to_nat(100000u);
v___x_2972_ = 0;
v___x_2973_ = 0;
v___x_2974_ = lean_box(0);
v___x_2975_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_2975_, 0, v___x_2971_);
lean_ctor_set(v___x_2975_, 1, v___x_2949_);
lean_ctor_set(v___x_2975_, 2, v___x_2974_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3, v___x_2972_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 1, v___x_2934_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 2, v___x_2972_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 3, v___x_2934_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 4, v___x_2934_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 5, v___x_2934_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 6, v___x_2973_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 7, v___x_2934_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 8, v___x_2934_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 9, v___x_2972_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 10, v___x_2972_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 11, v___x_2972_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 12, v___x_2934_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 13, v___x_2934_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 14, v___x_2972_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 15, v___x_2972_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 16, v___x_2972_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 17, v___x_2934_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 18, v___x_2934_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 19, v___x_2934_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 20, v___x_2934_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 21, v___x_2934_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 22, v___x_2934_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 23, v___x_2934_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 24, v___x_2934_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 25, v___x_2934_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 26, v___x_2972_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 27, v___x_2972_);
lean_ctor_set_uint8(v___x_2975_, sizeof(void*)*3 + 28, v___x_2972_);
v___x_2976_ = lean_array_push(v___x_2964_, v_a_2968_);
v___x_2977_ = l_Lean_Options_empty;
v___x_2978_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2975_, v___x_2976_, v_a_2970_, v___x_2977_, v___y_2941_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2978_, 1);
v___x_2980_ = lean_mk_empty_array_with_capacity(v___x_2935_);
v___x_2981_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__1));
v___x_2982_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_2980_, v___x_2981_, v___x_2972_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; size_t v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc_n(v_a_2983_, 2);
lean_dec_ref_known(v___x_2982_, 1);
v___x_2984_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3);
lean_inc_n(v___x_2935_, 2);
v___x_2985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
lean_ctor_set(v___x_2985_, 1, v___x_2935_);
v___x_2986_ = lean_unsigned_to_nat(32u);
v___x_2987_ = lean_mk_empty_array_with_capacity(v___x_2986_);
v___x_2988_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4);
v___x_2989_ = ((size_t)5ULL);
v___x_2990_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2990_, 0, v___x_2988_);
lean_ctor_set(v___x_2990_, 1, v___x_2987_);
lean_ctor_set(v___x_2990_, 2, v___x_2935_);
lean_ctor_set(v___x_2990_, 3, v___x_2935_);
lean_ctor_set_usize(v___x_2990_, 4, v___x_2989_);
v___x_2991_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2984_);
lean_ctor_set(v___x_2991_, 1, v___x_2984_);
lean_ctor_set(v___x_2991_, 2, v___x_2984_);
lean_ctor_set(v___x_2991_, 3, v___x_2990_);
v___x_2992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2985_);
lean_ctor_set(v___x_2992_, 1, v___x_2991_);
lean_inc(v_a_2979_);
v___x_2993_ = l_Lean_Meta_simp(v___x_2957_, v_a_2979_, v_a_2983_, v___x_2974_, v___x_2992_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v_fst_2995_; lean_object* v___x_2996_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2993_, 1);
v_fst_2995_ = lean_ctor_get(v_a_2994_, 0);
lean_inc(v_fst_2995_);
lean_dec(v_a_2994_);
v___x_2996_ = l_Lean_Meta_simp(v___x_2966_, v_a_2979_, v_a_2983_, v___x_2974_, v___x_2992_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec_ref_known(v___x_2992_, 2);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; lean_object* v_fst_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3035_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v___x_2996_, 1);
v_fst_2998_ = lean_ctor_get(v_a_2997_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v_a_2997_);
if (v_isSharedCheck_3035_ == 0)
{
lean_object* v_unused_3036_; 
v_unused_3036_ = lean_ctor_get(v_a_2997_, 1);
lean_dec(v_unused_3036_);
v___x_3000_ = v_a_2997_;
v_isShared_3001_ = v_isSharedCheck_3035_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_fst_2998_);
lean_dec(v_a_2997_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3035_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v_expr_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v_expr_3002_ = lean_ctor_get(v_fst_2995_, 0);
lean_inc_ref(v_expr_3002_);
lean_dec(v_fst_2995_);
v___x_3003_ = lean_box(1);
v___x_3004_ = l_Lean_PrettyPrinter_delab(v_expr_3002_, v___x_3003_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v_expr_3006_; lean_object* v___x_3007_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3004_, 1);
v_expr_3006_ = lean_ctor_get(v_fst_2998_, 0);
lean_inc_ref(v_expr_3006_);
lean_dec(v_fst_2998_);
v___x_3007_ = l_Lean_PrettyPrinter_delab(v_expr_3006_, v___x_3003_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3018_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3010_ = v___x_3007_;
v_isShared_3011_ = v_isSharedCheck_3018_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_3007_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3018_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 1, v_a_3008_);
lean_ctor_set(v___x_3000_, 0, v_a_3005_);
v___x_3013_ = v___x_3000_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3005_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v_a_3008_);
v___x_3013_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3015_; 
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 0, v___x_3013_);
v___x_3015_ = v___x_3010_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3013_);
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
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec(v_a_3005_);
lean_del_object(v___x_3000_);
v_a_3019_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3007_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3007_);
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
lean_del_object(v___x_3000_);
lean_dec(v_fst_2998_);
v_a_3027_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3004_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3004_);
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
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec(v_fst_2995_);
v_a_3037_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_2996_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_2996_);
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
lean_dec_ref_known(v___x_2992_, 2);
lean_dec(v_a_2983_);
lean_dec(v_a_2979_);
lean_dec_ref(v___x_2966_);
v_a_3045_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_2993_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_2993_);
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
lean_dec(v_a_2979_);
lean_dec_ref(v___x_2966_);
lean_dec_ref(v___x_2957_);
lean_dec(v___x_2935_);
v_a_3053_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_2982_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_2982_);
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
lean_dec_ref(v___x_2966_);
lean_dec_ref(v___x_2957_);
lean_dec(v___x_2935_);
v_a_3061_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_2978_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_2978_);
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
lean_dec(v_a_2968_);
lean_dec_ref(v___x_2966_);
lean_dec_ref(v___x_2964_);
lean_dec_ref(v___x_2957_);
lean_dec(v___x_2935_);
v_a_3069_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_2969_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_2969_);
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
lean_dec_ref(v___x_2966_);
lean_dec_ref(v___x_2964_);
lean_dec_ref(v___x_2957_);
lean_dec(v___x_2935_);
v_a_3077_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_2967_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_2967_);
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
lean_dec_ref(v___x_2957_);
lean_dec(v___x_2935_);
lean_dec_ref(v_fst_2933_);
v_a_3085_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_2962_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_2962_);
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
lean_dec_ref(v___x_2957_);
lean_dec_ref(v___x_2950_);
lean_dec_ref(v_letMuts_2936_);
lean_dec(v___x_2935_);
lean_dec_ref(v_fst_2933_);
v_a_3093_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_2958_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_2958_);
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
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
lean_dec_ref(v___x_2950_);
lean_dec_ref(v_letMuts_2936_);
lean_dec(v___x_2935_);
lean_dec_ref(v_fst_2933_);
lean_dec_ref(v_r_2931_);
lean_dec_ref(v_fst_2930_);
lean_dec_ref(v_xs_2929_);
lean_dec_ref(v_fst_2928_);
v_a_3101_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_2953_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_2953_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_dec_ref(v_letMuts_2936_);
lean_dec(v___x_2935_);
lean_dec_ref(v_fst_2933_);
lean_dec_ref(v_r_2931_);
lean_dec_ref(v_fst_2930_);
lean_dec_ref(v_xs_2929_);
lean_dec_ref(v_fst_2928_);
v_a_3109_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_2946_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_2946_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_2928_ = stack[0].m_obj;
lean_object* v_xs_2929_ = stack[1].m_obj;
lean_object* v_fst_2930_ = stack[2].m_obj;
lean_object* v_r_2931_ = stack[3].m_obj;
lean_object* v___x_2932_ = stack[4].m_obj;
lean_object* v_fst_2933_ = stack[5].m_obj;
uint8_t v___x_2934_ = stack[6].m_num;
lean_object* v___x_2935_ = stack[7].m_obj;
lean_object* v_letMuts_2936_ = stack[8].m_obj;
lean_object* v___y_2937_ = stack[9].m_obj;
lean_object* v___y_2938_ = stack[10].m_obj;
lean_object* v___y_2939_ = stack[11].m_obj;
lean_object* v___y_2940_ = stack[12].m_obj;
lean_object* v___y_2941_ = stack[13].m_obj;
lean_object* v___y_2942_ = stack[14].m_obj;
lean_object* v___y_2943_ = stack[15].m_obj;
lean_object* v___y_2944_ = stack[16].m_obj;
lean_object* v_res_3117_;
v_res_3117_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(v_fst_2928_, v_xs_2929_, v_fst_2930_, v_r_2931_, v___x_2932_, v_fst_2933_, v___x_2934_, v___x_2935_, v_letMuts_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
stack->m_obj
 = v_res_3117_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed(lean_object** _args){
lean_object* v_fst_3118_ = _args[0];
lean_object* v_xs_3119_ = _args[1];
lean_object* v_fst_3120_ = _args[2];
lean_object* v_r_3121_ = _args[3];
lean_object* v___x_3122_ = _args[4];
lean_object* v_fst_3123_ = _args[5];
lean_object* v___x_3124_ = _args[6];
lean_object* v___x_3125_ = _args[7];
lean_object* v_letMuts_3126_ = _args[8];
lean_object* v___y_3127_ = _args[9];
lean_object* v___y_3128_ = _args[10];
lean_object* v___y_3129_ = _args[11];
lean_object* v___y_3130_ = _args[12];
lean_object* v___y_3131_ = _args[13];
lean_object* v___y_3132_ = _args[14];
lean_object* v___y_3133_ = _args[15];
lean_object* v___y_3134_ = _args[16];
lean_object* v___y_3135_ = _args[17];
_start:
{
uint8_t v___x_77916__boxed_3136_; lean_object* v_res_3137_; 
v___x_77916__boxed_3136_ = lean_unbox(v___x_3124_);
v_res_3137_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(v_fst_3118_, v_xs_3119_, v_fst_3120_, v_r_3121_, v___x_3122_, v_fst_3123_, v___x_77916__boxed_3136_, v___x_3125_, v_letMuts_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___x_3122_);
return v_res_3137_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(lean_object* v_fst_3138_, lean_object* v_xs_3139_, lean_object* v_fst_3140_, lean_object* v___x_3141_, lean_object* v_fst_3142_, uint8_t v___x_3143_, lean_object* v___x_3144_, lean_object* v_snd_3145_, lean_object* v_r_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v___x_3156_; lean_object* v___f_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3156_ = lean_box(v___x_3143_);
v___f_3157_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed), 18, 8);
lean_closure_set(v___f_3157_, 0, v_fst_3138_);
lean_closure_set(v___f_3157_, 1, v_xs_3139_);
lean_closure_set(v___f_3157_, 2, v_fst_3140_);
lean_closure_set(v___f_3157_, 3, v_r_3146_);
lean_closure_set(v___f_3157_, 4, v___x_3141_);
lean_closure_set(v___f_3157_, 5, v_fst_3142_);
lean_closure_set(v___f_3157_, 6, v___x_3156_);
lean_closure_set(v___f_3157_, 7, v___x_3144_);
v___x_3158_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3159_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3158_, v_snd_3145_, v___f_3157_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
return v___x_3159_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_3138_ = stack[0].m_obj;
lean_object* v_xs_3139_ = stack[1].m_obj;
lean_object* v_fst_3140_ = stack[2].m_obj;
lean_object* v___x_3141_ = stack[3].m_obj;
lean_object* v_fst_3142_ = stack[4].m_obj;
uint8_t v___x_3143_ = stack[5].m_num;
lean_object* v___x_3144_ = stack[6].m_obj;
lean_object* v_snd_3145_ = stack[7].m_obj;
lean_object* v_r_3146_ = stack[8].m_obj;
lean_object* v___y_3147_ = stack[9].m_obj;
lean_object* v___y_3148_ = stack[10].m_obj;
lean_object* v___y_3149_ = stack[11].m_obj;
lean_object* v___y_3150_ = stack[12].m_obj;
lean_object* v___y_3151_ = stack[13].m_obj;
lean_object* v___y_3152_ = stack[14].m_obj;
lean_object* v___y_3153_ = stack[15].m_obj;
lean_object* v___y_3154_ = stack[16].m_obj;
lean_object* v_res_3160_;
v_res_3160_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(v_fst_3138_, v_xs_3139_, v_fst_3140_, v___x_3141_, v_fst_3142_, v___x_3143_, v___x_3144_, v_snd_3145_, v_r_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
stack->m_obj
 = v_res_3160_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed(lean_object** _args){
lean_object* v_fst_3161_ = _args[0];
lean_object* v_xs_3162_ = _args[1];
lean_object* v_fst_3163_ = _args[2];
lean_object* v___x_3164_ = _args[3];
lean_object* v_fst_3165_ = _args[4];
lean_object* v___x_3166_ = _args[5];
lean_object* v___x_3167_ = _args[6];
lean_object* v_snd_3168_ = _args[7];
lean_object* v_r_3169_ = _args[8];
lean_object* v___y_3170_ = _args[9];
lean_object* v___y_3171_ = _args[10];
lean_object* v___y_3172_ = _args[11];
lean_object* v___y_3173_ = _args[12];
lean_object* v___y_3174_ = _args[13];
lean_object* v___y_3175_ = _args[14];
lean_object* v___y_3176_ = _args[15];
lean_object* v___y_3177_ = _args[16];
lean_object* v___y_3178_ = _args[17];
_start:
{
uint8_t v___x_78520__boxed_3179_; lean_object* v_res_3180_; 
v___x_78520__boxed_3179_ = lean_unbox(v___x_3166_);
v_res_3180_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(v_fst_3161_, v_xs_3162_, v_fst_3163_, v___x_3164_, v_fst_3165_, v___x_78520__boxed_3179_, v___x_3167_, v_snd_3168_, v_r_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
return v_res_3180_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(lean_object* v_fst_3184_, lean_object* v_fst_3185_, lean_object* v___x_3186_, lean_object* v_fst_3187_, uint8_t v___x_3188_, lean_object* v___x_3189_, lean_object* v_snd_3190_, lean_object* v_xs_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v___x_3201_; lean_object* v___f_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3201_ = lean_box(v___x_3188_);
lean_inc_ref(v_fst_3184_);
v___f_3202_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed), 18, 8);
lean_closure_set(v___f_3202_, 0, v_fst_3184_);
lean_closure_set(v___f_3202_, 1, v_xs_3191_);
lean_closure_set(v___f_3202_, 2, v_fst_3185_);
lean_closure_set(v___f_3202_, 3, v___x_3186_);
lean_closure_set(v___f_3202_, 4, v_fst_3187_);
lean_closure_set(v___f_3202_, 5, v___x_3201_);
lean_closure_set(v___f_3202_, 6, v___x_3189_);
lean_closure_set(v___f_3202_, 7, v_snd_3190_);
v___x_3203_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_3204_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3203_, v_fst_3184_, v___f_3202_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
return v___x_3204_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_3184_ = stack[0].m_obj;
lean_object* v_fst_3185_ = stack[1].m_obj;
lean_object* v___x_3186_ = stack[2].m_obj;
lean_object* v_fst_3187_ = stack[3].m_obj;
uint8_t v___x_3188_ = stack[4].m_num;
lean_object* v___x_3189_ = stack[5].m_obj;
lean_object* v_snd_3190_ = stack[6].m_obj;
lean_object* v_xs_3191_ = stack[7].m_obj;
lean_object* v___y_3192_ = stack[8].m_obj;
lean_object* v___y_3193_ = stack[9].m_obj;
lean_object* v___y_3194_ = stack[10].m_obj;
lean_object* v___y_3195_ = stack[11].m_obj;
lean_object* v___y_3196_ = stack[12].m_obj;
lean_object* v___y_3197_ = stack[13].m_obj;
lean_object* v___y_3198_ = stack[14].m_obj;
lean_object* v___y_3199_ = stack[15].m_obj;
lean_object* v_res_3205_;
v_res_3205_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(v_fst_3184_, v_fst_3185_, v___x_3186_, v_fst_3187_, v___x_3188_, v___x_3189_, v_snd_3190_, v_xs_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
stack->m_obj
 = v_res_3205_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed(lean_object** _args){
lean_object* v_fst_3206_ = _args[0];
lean_object* v_fst_3207_ = _args[1];
lean_object* v___x_3208_ = _args[2];
lean_object* v_fst_3209_ = _args[3];
lean_object* v___x_3210_ = _args[4];
lean_object* v___x_3211_ = _args[5];
lean_object* v_snd_3212_ = _args[6];
lean_object* v_xs_3213_ = _args[7];
lean_object* v___y_3214_ = _args[8];
lean_object* v___y_3215_ = _args[9];
lean_object* v___y_3216_ = _args[10];
lean_object* v___y_3217_ = _args[11];
lean_object* v___y_3218_ = _args[12];
lean_object* v___y_3219_ = _args[13];
lean_object* v___y_3220_ = _args[14];
lean_object* v___y_3221_ = _args[15];
lean_object* v___y_3222_ = _args[16];
_start:
{
uint8_t v___x_78619__boxed_3223_; lean_object* v_res_3224_; 
v___x_78619__boxed_3223_ = lean_unbox(v___x_3210_);
v_res_3224_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(v_fst_3206_, v_fst_3207_, v___x_3208_, v_fst_3209_, v___x_78619__boxed_3223_, v___x_3211_, v_snd_3212_, v_xs_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
return v_res_3224_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(lean_object* v_as_3225_, size_t v_sz_3226_, size_t v_i_3227_, lean_object* v_b_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
uint8_t v___x_3234_; 
v___x_3234_ = lean_usize_dec_lt(v_i_3227_, v_sz_3226_);
if (v___x_3234_ == 0)
{
lean_object* v___x_3235_; 
v___x_3235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3235_, 0, v_b_3228_);
return v___x_3235_;
}
else
{
lean_object* v___x_3236_; lean_object* v_a_3237_; lean_object* v___x_3238_; 
v___x_3236_ = lean_box(1);
v_a_3237_ = lean_array_uget_borrowed(v_as_3225_, v_i_3227_);
lean_inc(v_a_3237_);
v___x_3238_ = l_Lean_PrettyPrinter_delab(v_a_3237_, v___x_3236_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; lean_object* v___x_3240_; size_t v___x_3241_; size_t v___x_3242_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
lean_inc(v_a_3239_);
lean_dec_ref_known(v___x_3238_, 1);
v___x_3240_ = lean_array_push(v_b_3228_, v_a_3239_);
v___x_3241_ = ((size_t)1ULL);
v___x_3242_ = lean_usize_add(v_i_3227_, v___x_3241_);
v_i_3227_ = v___x_3242_;
v_b_3228_ = v___x_3240_;
goto _start;
}
else
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
lean_dec_ref(v_b_3228_);
v_a_3244_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3246_ = v___x_3238_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_3238_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3244_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3225_ = stack[0].m_obj;
size_t v_sz_3226_ = stack[1].m_num;
size_t v_i_3227_ = stack[2].m_num;
lean_object* v_b_3228_ = stack[3].m_obj;
lean_object* v___y_3229_ = stack[4].m_obj;
lean_object* v___y_3230_ = stack[5].m_obj;
lean_object* v___y_3231_ = stack[6].m_obj;
lean_object* v___y_3232_ = stack[7].m_obj;
lean_object* v_res_3252_;
v_res_3252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_3225_, v_sz_3226_, v_i_3227_, v_b_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
stack->m_obj
 = v_res_3252_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg___boxed(lean_object* v_as_3253_, lean_object* v_sz_3254_, lean_object* v_i_3255_, lean_object* v_b_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
size_t v_sz_boxed_3262_; size_t v_i_boxed_3263_; lean_object* v_res_3264_; 
v_sz_boxed_3262_ = lean_unbox_usize(v_sz_3254_);
lean_dec(v_sz_3254_);
v_i_boxed_3263_ = lean_unbox_usize(v_i_3255_);
lean_dec(v_i_3255_);
v_res_3264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_3253_, v_sz_boxed_3262_, v_i_boxed_3263_, v_b_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec_ref(v_as_3253_);
return v_res_3264_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(lean_object* v_xs_3285_, lean_object* v_fst_3286_, lean_object* v_snd_3287_, lean_object* v___x_3288_, lean_object* v___x_3289_, lean_object* v___x_3290_, lean_object* v___x_3291_, lean_object* v___x_3292_, lean_object* v___x_3293_, lean_object* v___x_3294_, lean_object* v___x_3295_, uint8_t v___x_3296_, lean_object* v_letMuts_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3307_ = lean_unsigned_to_nat(2u);
v___x_3308_ = lean_mk_empty_array_with_capacity(v___x_3307_);
v___x_3309_ = lean_array_push(v___x_3308_, v_xs_3285_);
v___x_3310_ = lean_array_push(v___x_3309_, v_letMuts_3297_);
v___x_3311_ = l_Lean_Expr_beta(v_fst_3286_, v___x_3310_);
v___x_3312_ = lean_box(1);
v___x_3313_ = l_Lean_PrettyPrinter_delab(v___x_3311_, v___x_3312_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3453_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3316_ = v___x_3313_;
v_isShared_3317_ = v_isSharedCheck_3453_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3313_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3453_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
uint8_t v___y_3319_; lean_object* v_points_3356_; lean_object* v_default_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3452_; 
v_points_3356_ = lean_ctor_get(v_snd_3287_, 0);
v_default_3357_ = lean_ctor_get(v_snd_3287_, 1);
v_isSharedCheck_3452_ = !lean_is_exclusive(v_snd_3287_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3359_ = v_snd_3287_;
v_isShared_3360_ = v_isSharedCheck_3452_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_default_3357_);
lean_inc(v_points_3356_);
lean_dec(v_snd_3287_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3452_;
goto v_resetjp_3358_;
}
v___jp_3318_:
{
lean_object* v_toCold_3320_; lean_object* v_ref_3321_; lean_object* v_quotContext_3322_; lean_object* v_currMacroScope_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3354_; 
v_toCold_3320_ = lean_ctor_get(v___y_3304_, 0);
v_ref_3321_ = lean_ctor_get(v___y_3304_, 2);
v_quotContext_3322_ = lean_ctor_get(v_toCold_3320_, 8);
v_currMacroScope_3323_ = lean_ctor_get(v_toCold_3320_, 9);
v___x_3324_ = l_Lean_SourceInfo_fromRef(v_ref_3321_, v___y_3319_);
v___x_3325_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_3326_ = l_Lean_Name_mkStr3(v___x_3294_, v___x_3295_, v___x_3325_);
v___x_3327_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_3328_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3324_, 11);
v___x_3329_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3324_);
lean_ctor_set(v___x_3329_, 1, v___x_3327_);
lean_ctor_set(v___x_3329_, 2, v___x_3328_);
v___x_3330_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_3331_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3324_);
lean_ctor_set(v___x_3331_, 1, v___x_3330_);
v___x_3332_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3333_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3334_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_3335_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3324_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v___x_3336_ = l_String_toRawSubstring_x27(v___x_3288_);
lean_inc_n(v_currMacroScope_3323_, 2);
lean_inc_n(v_quotContext_3322_, 2);
v___x_3337_ = l_Lean_addMacroScope(v_quotContext_3322_, v___x_3289_, v_currMacroScope_3323_);
v___x_3338_ = lean_box(0);
v___x_3339_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3324_);
lean_ctor_set(v___x_3339_, 1, v___x_3336_);
lean_ctor_set(v___x_3339_, 2, v___x_3337_);
lean_ctor_set(v___x_3339_, 3, v___x_3338_);
v___x_3340_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3341_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3324_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
v___x_3342_ = l_String_toRawSubstring_x27(v___x_3290_);
v___x_3343_ = l_Lean_addMacroScope(v_quotContext_3322_, v___x_3291_, v_currMacroScope_3323_);
v___x_3344_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3324_);
lean_ctor_set(v___x_3344_, 1, v___x_3342_);
lean_ctor_set(v___x_3344_, 2, v___x_3343_);
lean_ctor_set(v___x_3344_, 3, v___x_3338_);
v___x_3345_ = l_Lean_Syntax_node3(v___x_3324_, v___x_3332_, v___x_3339_, v___x_3341_, v___x_3344_);
v___x_3346_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3324_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
v___x_3348_ = l_Lean_Syntax_node3(v___x_3324_, v___x_3333_, v___x_3335_, v___x_3345_, v___x_3347_);
v___x_3349_ = l_Lean_Syntax_node1(v___x_3324_, v___x_3332_, v___x_3348_);
v___x_3350_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3351_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3324_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
v___x_3352_ = l_Lean_Syntax_node5(v___x_3324_, v___x_3326_, v___x_3329_, v___x_3331_, v___x_3349_, v___x_3351_, v_a_3314_);
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 0, v___x_3352_);
v___x_3354_ = v___x_3316_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3352_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
v_resetjp_3358_:
{
uint8_t v___y_3362_; lean_object* v___x_3413_; uint8_t v___x_3414_; 
v___x_3413_ = lean_array_get_size(v_points_3356_);
v___x_3414_ = lean_nat_dec_eq(v___x_3413_, v___x_3293_);
if (v___x_3414_ == 0)
{
lean_del_object(v___x_3316_);
lean_dec_ref(v___x_3295_);
lean_dec_ref(v___x_3294_);
v___y_3362_ = v___x_3414_;
goto v___jp_3361_;
}
else
{
if (lean_obj_tag(v_default_3357_) == 3)
{
uint8_t v___x_3415_; 
lean_del_object(v___x_3316_);
lean_dec_ref(v___x_3295_);
lean_dec_ref(v___x_3294_);
v___x_3415_ = 0;
v___y_3362_ = v___x_3415_;
goto v___jp_3361_;
}
else
{
lean_del_object(v___x_3359_);
lean_dec_ref(v_points_3356_);
if (lean_obj_tag(v_default_3357_) == 2)
{
if (v___x_3296_ == 0)
{
v___y_3319_ = v___x_3296_;
goto v___jp_3318_;
}
else
{
lean_object* v_toCold_3416_; lean_object* v_ref_3417_; lean_object* v_quotContext_3418_; lean_object* v_currMacroScope_3419_; uint8_t v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
lean_del_object(v___x_3316_);
v_toCold_3416_ = lean_ctor_get(v___y_3304_, 0);
v_ref_3417_ = lean_ctor_get(v___y_3304_, 2);
v_quotContext_3418_ = lean_ctor_get(v_toCold_3416_, 8);
v_currMacroScope_3419_ = lean_ctor_get(v_toCold_3416_, 9);
v___x_3420_ = 0;
v___x_3421_ = l_Lean_SourceInfo_fromRef(v_ref_3417_, v___x_3420_);
v___x_3422_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__9));
v___x_3423_ = l_Lean_Name_mkStr3(v___x_3294_, v___x_3295_, v___x_3422_);
v___x_3424_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_3425_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3421_, 11);
v___x_3426_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3421_);
lean_ctor_set(v___x_3426_, 1, v___x_3424_);
lean_ctor_set(v___x_3426_, 2, v___x_3425_);
v___x_3427_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__10));
v___x_3428_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3421_);
lean_ctor_set(v___x_3428_, 1, v___x_3427_);
v___x_3429_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3430_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3431_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_3432_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3421_);
lean_ctor_set(v___x_3432_, 1, v___x_3431_);
v___x_3433_ = l_String_toRawSubstring_x27(v___x_3288_);
lean_inc_n(v_currMacroScope_3419_, 2);
lean_inc_n(v_quotContext_3418_, 2);
v___x_3434_ = l_Lean_addMacroScope(v_quotContext_3418_, v___x_3289_, v_currMacroScope_3419_);
v___x_3435_ = lean_box(0);
v___x_3436_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3421_);
lean_ctor_set(v___x_3436_, 1, v___x_3433_);
lean_ctor_set(v___x_3436_, 2, v___x_3434_);
lean_ctor_set(v___x_3436_, 3, v___x_3435_);
v___x_3437_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3438_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3421_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
v___x_3439_ = l_String_toRawSubstring_x27(v___x_3290_);
v___x_3440_ = l_Lean_addMacroScope(v_quotContext_3418_, v___x_3291_, v_currMacroScope_3419_);
v___x_3441_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3421_);
lean_ctor_set(v___x_3441_, 1, v___x_3439_);
lean_ctor_set(v___x_3441_, 2, v___x_3440_);
lean_ctor_set(v___x_3441_, 3, v___x_3435_);
v___x_3442_ = l_Lean_Syntax_node3(v___x_3421_, v___x_3429_, v___x_3436_, v___x_3438_, v___x_3441_);
v___x_3443_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3444_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3421_);
lean_ctor_set(v___x_3444_, 1, v___x_3443_);
v___x_3445_ = l_Lean_Syntax_node3(v___x_3421_, v___x_3430_, v___x_3432_, v___x_3442_, v___x_3444_);
v___x_3446_ = l_Lean_Syntax_node1(v___x_3421_, v___x_3429_, v___x_3445_);
v___x_3447_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3421_);
lean_ctor_set(v___x_3448_, 1, v___x_3447_);
v___x_3449_ = l_Lean_Syntax_node5(v___x_3421_, v___x_3423_, v___x_3426_, v___x_3428_, v___x_3446_, v___x_3448_, v_a_3314_);
v___x_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3449_);
return v___x_3450_;
}
}
else
{
uint8_t v___x_3451_; 
lean_dec(v_default_3357_);
v___x_3451_ = 0;
v___y_3319_ = v___x_3451_;
goto v___jp_3318_;
}
}
}
v___jp_3361_:
{
lean_object* v_toCold_3363_; lean_object* v_ref_3364_; lean_object* v_quotContext_3365_; lean_object* v_currMacroScope_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3371_; 
v_toCold_3363_ = lean_ctor_get(v___y_3304_, 0);
v_ref_3364_ = lean_ctor_get(v___y_3304_, 2);
v_quotContext_3365_ = lean_ctor_get(v_toCold_3363_, 8);
v_currMacroScope_3366_ = lean_ctor_get(v_toCold_3363_, 9);
v___x_3367_ = l_Lean_SourceInfo_fromRef(v_ref_3364_, v___y_3362_);
v___x_3368_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3369_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc(v___x_3367_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set_tag(v___x_3359_, 2);
lean_ctor_set(v___x_3359_, 1, v___x_3368_);
lean_ctor_set(v___x_3359_, 0, v___x_3367_);
v___x_3371_ = v___x_3359_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3367_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v___x_3368_);
v___x_3371_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; size_t v_sz_3399_; size_t v___x_3400_; lean_object* v___x_3401_; 
v___x_3372_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3373_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3374_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3375_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
lean_inc_n(v___x_3367_, 11);
v___x_3376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3367_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
v___x_3377_ = l_String_toRawSubstring_x27(v___x_3288_);
lean_inc_n(v_currMacroScope_3366_, 2);
lean_inc_n(v_quotContext_3365_, 2);
v___x_3378_ = l_Lean_addMacroScope(v_quotContext_3365_, v___x_3289_, v_currMacroScope_3366_);
v___x_3379_ = lean_box(0);
v___x_3380_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3367_);
lean_ctor_set(v___x_3380_, 1, v___x_3377_);
lean_ctor_set(v___x_3380_, 2, v___x_3378_);
lean_ctor_set(v___x_3380_, 3, v___x_3379_);
v___x_3381_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3382_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3367_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
v___x_3383_ = l_String_toRawSubstring_x27(v___x_3290_);
v___x_3384_ = l_Lean_addMacroScope(v_quotContext_3365_, v___x_3291_, v_currMacroScope_3366_);
v___x_3385_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3367_);
lean_ctor_set(v___x_3385_, 1, v___x_3383_);
lean_ctor_set(v___x_3385_, 2, v___x_3384_);
lean_ctor_set(v___x_3385_, 3, v___x_3379_);
v___x_3386_ = l_Lean_Syntax_node3(v___x_3367_, v___x_3373_, v___x_3380_, v___x_3382_, v___x_3385_);
v___x_3387_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3388_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3367_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
v___x_3389_ = l_Lean_Syntax_node3(v___x_3367_, v___x_3374_, v___x_3376_, v___x_3386_, v___x_3388_);
v___x_3390_ = l_Lean_Syntax_node1(v___x_3367_, v___x_3373_, v___x_3389_);
v___x_3391_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3392_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3367_);
lean_ctor_set(v___x_3392_, 1, v___x_3373_);
lean_ctor_set(v___x_3392_, 2, v___x_3391_);
v___x_3393_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3394_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3367_);
lean_ctor_set(v___x_3394_, 1, v___x_3393_);
v___x_3395_ = l_Lean_Syntax_node4(v___x_3367_, v___x_3372_, v___x_3390_, v___x_3392_, v___x_3394_, v_a_3314_);
v___x_3396_ = l_Lean_Syntax_node2(v___x_3367_, v___x_3369_, v___x_3371_, v___x_3395_);
v___x_3397_ = lean_mk_empty_array_with_capacity(v___x_3292_);
v___x_3398_ = lean_array_push(v___x_3397_, v___x_3396_);
v_sz_3399_ = lean_array_size(v_points_3356_);
v___x_3400_ = ((size_t)0ULL);
v___x_3401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_points_3356_, v_sz_3399_, v___x_3400_, v___x_3398_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
lean_dec_ref(v_points_3356_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; lean_object* v___x_3403_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_a_3402_);
lean_dec_ref_known(v___x_3401_, 1);
v___x_3403_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3402_, v_default_3357_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
lean_dec(v_a_3402_);
return v___x_3403_;
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
lean_dec(v_default_3357_);
v_a_3404_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3401_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3401_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
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
lean_dec_ref(v___x_3295_);
lean_dec_ref(v___x_3294_);
lean_dec(v___x_3291_);
lean_dec_ref(v___x_3290_);
lean_dec(v___x_3289_);
lean_dec_ref(v___x_3288_);
lean_dec_ref(v_snd_3287_);
return v___x_3313_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_3285_ = stack[0].m_obj;
lean_object* v_fst_3286_ = stack[1].m_obj;
lean_object* v_snd_3287_ = stack[2].m_obj;
lean_object* v___x_3288_ = stack[3].m_obj;
lean_object* v___x_3289_ = stack[4].m_obj;
lean_object* v___x_3290_ = stack[5].m_obj;
lean_object* v___x_3291_ = stack[6].m_obj;
lean_object* v___x_3292_ = stack[7].m_obj;
lean_object* v___x_3293_ = stack[8].m_obj;
lean_object* v___x_3294_ = stack[9].m_obj;
lean_object* v___x_3295_ = stack[10].m_obj;
uint8_t v___x_3296_ = stack[11].m_num;
lean_object* v_letMuts_3297_ = stack[12].m_obj;
lean_object* v___y_3298_ = stack[13].m_obj;
lean_object* v___y_3299_ = stack[14].m_obj;
lean_object* v___y_3300_ = stack[15].m_obj;
lean_object* v___y_3301_ = stack[16].m_obj;
lean_object* v___y_3302_ = stack[17].m_obj;
lean_object* v___y_3303_ = stack[18].m_obj;
lean_object* v___y_3304_ = stack[19].m_obj;
lean_object* v___y_3305_ = stack[20].m_obj;
lean_object* v_res_3454_;
v_res_3454_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(v_xs_3285_, v_fst_3286_, v_snd_3287_, v___x_3288_, v___x_3289_, v___x_3290_, v___x_3291_, v___x_3292_, v___x_3293_, v___x_3294_, v___x_3295_, v___x_3296_, v_letMuts_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
stack->m_obj
 = v_res_3454_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed(lean_object** _args){
lean_object* v_xs_3455_ = _args[0];
lean_object* v_fst_3456_ = _args[1];
lean_object* v_snd_3457_ = _args[2];
lean_object* v___x_3458_ = _args[3];
lean_object* v___x_3459_ = _args[4];
lean_object* v___x_3460_ = _args[5];
lean_object* v___x_3461_ = _args[6];
lean_object* v___x_3462_ = _args[7];
lean_object* v___x_3463_ = _args[8];
lean_object* v___x_3464_ = _args[9];
lean_object* v___x_3465_ = _args[10];
lean_object* v___x_3466_ = _args[11];
lean_object* v_letMuts_3467_ = _args[12];
lean_object* v___y_3468_ = _args[13];
lean_object* v___y_3469_ = _args[14];
lean_object* v___y_3470_ = _args[15];
lean_object* v___y_3471_ = _args[16];
lean_object* v___y_3472_ = _args[17];
lean_object* v___y_3473_ = _args[18];
lean_object* v___y_3474_ = _args[19];
lean_object* v___y_3475_ = _args[20];
lean_object* v___y_3476_ = _args[21];
_start:
{
uint8_t v___x_78892__boxed_3477_; lean_object* v_res_3478_; 
v___x_78892__boxed_3477_ = lean_unbox(v___x_3466_);
v_res_3478_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(v_xs_3455_, v_fst_3456_, v_snd_3457_, v___x_3458_, v___x_3459_, v___x_3460_, v___x_3461_, v___x_3462_, v___x_3463_, v___x_3464_, v___x_3465_, v___x_78892__boxed_3477_, v_letMuts_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___x_3463_);
lean_dec(v___x_3462_);
return v_res_3478_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(lean_object* v_fst_3479_, lean_object* v_snd_3480_, lean_object* v___x_3481_, lean_object* v___x_3482_, lean_object* v___x_3483_, lean_object* v___x_3484_, lean_object* v___x_3485_, lean_object* v___x_3486_, uint8_t v___x_3487_, lean_object* v_arg_3488_, lean_object* v_xs_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___f_3502_; lean_object* v___x_3503_; 
v___x_3499_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3500_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3501_ = lean_box(v___x_3487_);
v___f_3502_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed), 22, 12);
lean_closure_set(v___f_3502_, 0, v_xs_3489_);
lean_closure_set(v___f_3502_, 1, v_fst_3479_);
lean_closure_set(v___f_3502_, 2, v_snd_3480_);
lean_closure_set(v___f_3502_, 3, v___x_3481_);
lean_closure_set(v___f_3502_, 4, v___x_3482_);
lean_closure_set(v___f_3502_, 5, v___x_3499_);
lean_closure_set(v___f_3502_, 6, v___x_3500_);
lean_closure_set(v___f_3502_, 7, v___x_3483_);
lean_closure_set(v___f_3502_, 8, v___x_3484_);
lean_closure_set(v___f_3502_, 9, v___x_3485_);
lean_closure_set(v___f_3502_, 10, v___x_3486_);
lean_closure_set(v___f_3502_, 11, v___x_3501_);
v___x_3503_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3500_, v_arg_3488_, v___f_3502_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_);
return v___x_3503_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_3479_ = stack[0].m_obj;
lean_object* v_snd_3480_ = stack[1].m_obj;
lean_object* v___x_3481_ = stack[2].m_obj;
lean_object* v___x_3482_ = stack[3].m_obj;
lean_object* v___x_3483_ = stack[4].m_obj;
lean_object* v___x_3484_ = stack[5].m_obj;
lean_object* v___x_3485_ = stack[6].m_obj;
lean_object* v___x_3486_ = stack[7].m_obj;
uint8_t v___x_3487_ = stack[8].m_num;
lean_object* v_arg_3488_ = stack[9].m_obj;
lean_object* v_xs_3489_ = stack[10].m_obj;
lean_object* v___y_3490_ = stack[11].m_obj;
lean_object* v___y_3491_ = stack[12].m_obj;
lean_object* v___y_3492_ = stack[13].m_obj;
lean_object* v___y_3493_ = stack[14].m_obj;
lean_object* v___y_3494_ = stack[15].m_obj;
lean_object* v___y_3495_ = stack[16].m_obj;
lean_object* v___y_3496_ = stack[17].m_obj;
lean_object* v___y_3497_ = stack[18].m_obj;
lean_object* v_res_3504_;
v_res_3504_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(v_fst_3479_, v_snd_3480_, v___x_3481_, v___x_3482_, v___x_3483_, v___x_3484_, v___x_3485_, v___x_3486_, v___x_3487_, v_arg_3488_, v_xs_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_);
stack->m_obj
 = v_res_3504_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed(lean_object** _args){
lean_object* v_fst_3505_ = _args[0];
lean_object* v_snd_3506_ = _args[1];
lean_object* v___x_3507_ = _args[2];
lean_object* v___x_3508_ = _args[3];
lean_object* v___x_3509_ = _args[4];
lean_object* v___x_3510_ = _args[5];
lean_object* v___x_3511_ = _args[6];
lean_object* v___x_3512_ = _args[7];
lean_object* v___x_3513_ = _args[8];
lean_object* v_arg_3514_ = _args[9];
lean_object* v_xs_3515_ = _args[10];
lean_object* v___y_3516_ = _args[11];
lean_object* v___y_3517_ = _args[12];
lean_object* v___y_3518_ = _args[13];
lean_object* v___y_3519_ = _args[14];
lean_object* v___y_3520_ = _args[15];
lean_object* v___y_3521_ = _args[16];
lean_object* v___y_3522_ = _args[17];
lean_object* v___y_3523_ = _args[18];
lean_object* v___y_3524_ = _args[19];
_start:
{
uint8_t v___x_79431__boxed_3525_; lean_object* v_res_3526_; 
v___x_79431__boxed_3525_ = lean_unbox(v___x_3513_);
v_res_3526_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(v_fst_3505_, v_snd_3506_, v___x_3507_, v___x_3508_, v___x_3509_, v___x_3510_, v___x_3511_, v___x_3512_, v___x_79431__boxed_3525_, v_arg_3514_, v_xs_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
return v_res_3526_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(lean_object* v_as_3527_, size_t v_sz_3528_, size_t v_i_3529_, lean_object* v_b_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
uint8_t v___x_3536_; 
v___x_3536_ = lean_usize_dec_lt(v_i_3529_, v_sz_3528_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; 
v___x_3537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3537_, 0, v_b_3530_);
return v___x_3537_;
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v_a_3538_ = lean_array_uget_borrowed(v_as_3527_, v_i_3529_);
v___x_3539_ = lean_box(1);
lean_inc(v_a_3538_);
v___x_3540_ = l_Lean_PrettyPrinter_delab(v_a_3538_, v___x_3539_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v_a_3541_; lean_object* v___x_3542_; size_t v___x_3543_; size_t v___x_3544_; 
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_a_3541_);
lean_dec_ref_known(v___x_3540_, 1);
v___x_3542_ = lean_array_push(v_b_3530_, v_a_3541_);
v___x_3543_ = ((size_t)1ULL);
v___x_3544_ = lean_usize_add(v_i_3529_, v___x_3543_);
v_i_3529_ = v___x_3544_;
v_b_3530_ = v___x_3542_;
goto _start;
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_dec_ref(v_b_3530_);
v_a_3546_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3540_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3540_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3527_ = stack[0].m_obj;
size_t v_sz_3528_ = stack[1].m_num;
size_t v_i_3529_ = stack[2].m_num;
lean_object* v_b_3530_ = stack[3].m_obj;
lean_object* v___y_3531_ = stack[4].m_obj;
lean_object* v___y_3532_ = stack[5].m_obj;
lean_object* v___y_3533_ = stack[6].m_obj;
lean_object* v___y_3534_ = stack[7].m_obj;
lean_object* v_res_3554_;
v_res_3554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_3527_, v_sz_3528_, v_i_3529_, v_b_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
stack->m_obj
 = v_res_3554_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg___boxed(lean_object* v_as_3555_, lean_object* v_sz_3556_, lean_object* v_i_3557_, lean_object* v_b_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
size_t v_sz_boxed_3564_; size_t v_i_boxed_3565_; lean_object* v_res_3566_; 
v_sz_boxed_3564_ = lean_unbox_usize(v_sz_3556_);
lean_dec(v_sz_3556_);
v_i_boxed_3565_ = lean_unbox_usize(v_i_3557_);
lean_dec(v_i_3557_);
v_res_3566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_3555_, v_sz_boxed_3564_, v_i_boxed_3565_, v_b_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
lean_dec_ref(v_as_3555_);
return v_res_3566_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3(void){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3574_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__2));
v___x_3575_ = l_String_toRawSubstring_x27(v___x_3574_);
return v___x_3575_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9(void){
_start:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; 
v___x_3585_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__8));
v___x_3586_ = l_String_toRawSubstring_x27(v___x_3585_);
return v___x_3586_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12(void){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3590_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__0));
v___x_3591_ = l_String_toRawSubstring_x27(v___x_3590_);
return v___x_3591_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13(void){
_start:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3592_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3593_ = l_String_toRawSubstring_x27(v___x_3592_);
return v___x_3593_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16(void){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3596_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__15));
v___x_3597_ = l_String_toRawSubstring_x27(v___x_3596_);
return v___x_3597_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19(void){
_start:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3601_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__18));
v___x_3602_ = l_String_toRawSubstring_x27(v___x_3601_);
return v___x_3602_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(lean_object* v___x_3612_, lean_object* v___x_3613_, lean_object* v___f_3614_, lean_object* v_a_3615_, lean_object* v_inv_3616_, lean_object* v_arg_3617_, lean_object* v___x_3618_, uint8_t v___x_3619_, lean_object* v___x_3620_, lean_object* v___x_3621_, lean_object* v___x_3622_, lean_object* v___x_3623_, lean_object* v___x_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v_a_3635_; lean_object* v___y_3639_; lean_object* v___x_3641_; 
lean_inc_ref(v___x_3613_);
lean_inc(v___x_3612_);
v___x_3641_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3612_, v___x_3613_, v___f_3614_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v___x_3643_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_a_3642_);
lean_dec_ref_known(v___x_3641_, 1);
v___x_3643_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(v_a_3615_, v_inv_3616_, v_arg_3617_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_a_3644_);
lean_dec_ref_known(v___x_3643_, 1);
if (lean_obj_tag(v_a_3644_) == 1)
{
lean_object* v_val_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_4130_; 
lean_dec_ref(v_arg_3617_);
v_val_3645_ = lean_ctor_get(v_a_3644_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v_a_3644_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_3647_ = v_a_3644_;
v_isShared_3648_ = v_isSharedCheck_4130_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_val_3645_);
lean_dec(v_a_3644_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_4130_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
if (lean_obj_tag(v_a_3642_) == 1)
{
lean_object* v_val_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_4052_; 
lean_del_object(v___x_3647_);
v_val_3649_ = lean_ctor_get(v_a_3642_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v_a_3642_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_3651_ = v_a_3642_;
v_isShared_3652_ = v_isSharedCheck_4052_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_val_3649_);
lean_dec(v_a_3642_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_4052_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v_snd_3653_; lean_object* v_fst_3654_; lean_object* v_snd_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_4051_; 
v_snd_3653_ = lean_ctor_get(v_val_3649_, 1);
lean_inc(v_snd_3653_);
v_fst_3654_ = lean_ctor_get(v_val_3645_, 0);
v_snd_3655_ = lean_ctor_get(v_val_3645_, 1);
v_isSharedCheck_4051_ = !lean_is_exclusive(v_val_3645_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_3657_ = v_val_3645_;
v_isShared_3658_ = v_isSharedCheck_4051_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_snd_3655_);
lean_inc(v_fst_3654_);
lean_dec(v_val_3645_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_4051_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v_fst_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_4049_; 
v_fst_3659_ = lean_ctor_get(v_val_3649_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v_val_3649_);
if (v_isSharedCheck_4049_ == 0)
{
lean_object* v_unused_4050_; 
v_unused_4050_ = lean_ctor_get(v_val_3649_, 1);
lean_dec(v_unused_4050_);
v___x_3661_ = v_val_3649_;
v_isShared_3662_ = v_isSharedCheck_4049_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_fst_3659_);
lean_dec(v_val_3649_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_4049_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v_fst_3663_; lean_object* v_snd_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_4048_; 
v_fst_3663_ = lean_ctor_get(v_snd_3653_, 0);
v_snd_3664_ = lean_ctor_get(v_snd_3653_, 1);
v_isSharedCheck_4048_ = !lean_is_exclusive(v_snd_3653_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_3666_ = v_snd_3653_;
v_isShared_3667_ = v_isSharedCheck_4048_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_snd_3664_);
lean_inc(v_fst_3663_);
lean_dec(v_snd_3653_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_4048_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3668_; lean_object* v___f_3669_; lean_object* v___x_3670_; 
v___x_3668_ = lean_box(v___x_3619_);
lean_inc(v___x_3620_);
v___f_3669_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed), 17, 7);
lean_closure_set(v___f_3669_, 0, v_fst_3654_);
lean_closure_set(v___f_3669_, 1, v_fst_3659_);
lean_closure_set(v___f_3669_, 2, v___x_3618_);
lean_closure_set(v___f_3669_, 3, v_fst_3663_);
lean_closure_set(v___f_3669_, 4, v___x_3668_);
lean_closure_set(v___f_3669_, 5, v___x_3620_);
lean_closure_set(v___f_3669_, 6, v_snd_3655_);
lean_inc(v___x_3612_);
v___x_3670_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3612_, v___x_3613_, v___f_3669_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v_fst_3672_; lean_object* v_snd_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_4039_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc(v_a_3671_);
lean_dec_ref_known(v___x_3670_, 1);
v_fst_3672_ = lean_ctor_get(v_a_3671_, 0);
v_snd_3673_ = lean_ctor_get(v_a_3671_, 1);
v_isSharedCheck_4039_ = !lean_is_exclusive(v_a_3671_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_3675_ = v_a_3671_;
v_isShared_3676_ = v_isSharedCheck_4039_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_snd_3673_);
lean_inc(v_fst_3672_);
lean_dec(v_a_3671_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_4039_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v_points_3677_; lean_object* v_default_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_4038_; 
v_points_3677_ = lean_ctor_get(v_snd_3664_, 0);
v_default_3678_ = lean_ctor_get(v_snd_3664_, 1);
v_isSharedCheck_4038_ = !lean_is_exclusive(v_snd_3664_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_3680_ = v_snd_3664_;
v_isShared_3681_ = v_isSharedCheck_4038_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_default_3678_);
lean_inc(v_points_3677_);
lean_dec(v_snd_3664_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_4038_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3682_; uint8_t v___x_3683_; 
v___x_3682_ = lean_array_get_size(v_points_3677_);
v___x_3683_ = lean_nat_dec_eq(v___x_3682_, v___x_3620_);
if (v___x_3683_ == 0)
{
lean_object* v___x_3684_; size_t v_sz_3685_; size_t v___x_3686_; lean_object* v___x_3687_; 
lean_del_object(v___x_3651_);
v___x_3684_ = lean_mk_empty_array_with_capacity(v___x_3620_);
lean_dec(v___x_3620_);
v_sz_3685_ = lean_array_size(v_points_3677_);
v___x_3686_ = ((size_t)0ULL);
v___x_3687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_points_3677_, v_sz_3685_, v___x_3686_, v___x_3684_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
lean_dec_ref(v_points_3677_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_a_3688_; lean_object* v___x_3689_; 
v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_a_3688_);
lean_dec_ref_known(v___x_3687_, 1);
v___x_3689_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3688_, v_default_3678_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
lean_dec(v_a_3688_);
if (lean_obj_tag(v___x_3689_) == 0)
{
lean_object* v_toCold_3690_; lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3773_; 
v_toCold_3690_ = lean_ctor_get(v___y_3631_, 0);
lean_inc_ref(v_toCold_3690_);
v_a_3691_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3693_ = v___x_3689_;
v_isShared_3694_ = v_isSharedCheck_3773_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3689_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3773_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v_ref_3695_; lean_object* v_quotContext_3696_; lean_object* v_currMacroScope_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3707_; 
v_ref_3695_ = lean_ctor_get(v___y_3631_, 2);
lean_inc(v_ref_3695_);
lean_dec_ref(v___y_3631_);
v_quotContext_3696_ = lean_ctor_get(v_toCold_3690_, 8);
lean_inc_n(v_quotContext_3696_, 2);
v_currMacroScope_3697_ = lean_ctor_get(v_toCold_3690_, 9);
lean_inc_n(v_currMacroScope_3697_, 2);
lean_dec_ref(v_toCold_3690_);
v___x_3698_ = l_Lean_SourceInfo_fromRef(v_ref_3695_, v___x_3683_);
lean_dec(v_ref_3695_);
v___x_3699_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3700_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3701_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3621_);
v___x_3702_ = l_Lean_Name_mkStr2(v___x_3621_, v___x_3701_);
v___x_3703_ = l_Lean_addMacroScope(v_quotContext_3696_, v___x_3702_, v_currMacroScope_3697_);
v___x_3704_ = l_Lean_Name_mkStr4(v___x_3622_, v___x_3623_, v___x_3621_, v___x_3701_);
v___x_3705_ = lean_box(0);
lean_inc(v___x_3704_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set_tag(v___x_3680_, 1);
lean_ctor_set(v___x_3680_, 1, v___x_3705_);
lean_ctor_set(v___x_3680_, 0, v___x_3704_);
v___x_3707_ = v___x_3680_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3704_);
lean_ctor_set(v_reuseFailAlloc_3772_, 1, v___x_3705_);
v___x_3707_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
lean_object* v___x_3709_; 
if (v_isShared_3694_ == 0)
{
lean_ctor_set(v___x_3693_, 0, v___x_3704_);
v___x_3709_ = v___x_3693_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3704_);
v___x_3709_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
lean_object* v___x_3711_; 
if (v_isShared_3676_ == 0)
{
lean_ctor_set_tag(v___x_3675_, 1);
lean_ctor_set(v___x_3675_, 1, v___x_3705_);
lean_ctor_set(v___x_3675_, 0, v___x_3709_);
v___x_3711_ = v___x_3675_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3709_);
lean_ctor_set(v_reuseFailAlloc_3770_, 1, v___x_3705_);
v___x_3711_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
lean_object* v___x_3713_; 
if (v_isShared_3667_ == 0)
{
lean_ctor_set_tag(v___x_3666_, 1);
lean_ctor_set(v___x_3666_, 1, v___x_3711_);
lean_ctor_set(v___x_3666_, 0, v___x_3707_);
v___x_3713_ = v___x_3666_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3707_);
lean_ctor_set(v_reuseFailAlloc_3769_, 1, v___x_3711_);
v___x_3713_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3719_; 
lean_inc_n(v___x_3698_, 2);
v___x_3714_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3698_);
lean_ctor_set(v___x_3714_, 1, v___x_3700_);
lean_ctor_set(v___x_3714_, 2, v___x_3703_);
lean_ctor_set(v___x_3714_, 3, v___x_3713_);
v___x_3715_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3716_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3717_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3662_ == 0)
{
lean_ctor_set_tag(v___x_3661_, 2);
lean_ctor_set(v___x_3661_, 1, v___x_3717_);
lean_ctor_set(v___x_3661_, 0, v___x_3698_);
v___x_3719_ = v___x_3661_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v___x_3698_);
lean_ctor_set(v_reuseFailAlloc_3768_, 1, v___x_3717_);
v___x_3719_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3726_; 
v___x_3720_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3721_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3697_);
lean_inc(v_quotContext_3696_);
v___x_3722_ = l_Lean_addMacroScope(v_quotContext_3696_, v___x_3721_, v_currMacroScope_3697_);
lean_inc_n(v___x_3698_, 2);
v___x_3723_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3698_);
lean_ctor_set(v___x_3723_, 1, v___x_3720_);
lean_ctor_set(v___x_3723_, 2, v___x_3722_);
lean_ctor_set(v___x_3723_, 3, v___x_3705_);
v___x_3724_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3658_ == 0)
{
lean_ctor_set_tag(v___x_3657_, 2);
lean_ctor_set(v___x_3657_, 1, v___x_3724_);
lean_ctor_set(v___x_3657_, 0, v___x_3698_);
v___x_3726_ = v___x_3657_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3698_);
lean_ctor_set(v_reuseFailAlloc_3767_, 1, v___x_3724_);
v___x_3726_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3727_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3728_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3698_, 19);
v___x_3729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3698_);
lean_ctor_set(v___x_3729_, 1, v___x_3727_);
v___x_3730_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3731_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3732_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3697_, 4);
lean_inc_n(v_quotContext_3696_, 4);
v___x_3733_ = l_Lean_addMacroScope(v_quotContext_3696_, v___x_3732_, v_currMacroScope_3697_);
v___x_3734_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3698_);
lean_ctor_set(v___x_3734_, 1, v___x_3731_);
lean_ctor_set(v___x_3734_, 2, v___x_3733_);
lean_ctor_set(v___x_3734_, 3, v___x_3705_);
v___x_3735_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3736_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3737_ = l_Lean_addMacroScope(v_quotContext_3696_, v___x_3736_, v_currMacroScope_3697_);
v___x_3738_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3698_);
lean_ctor_set(v___x_3738_, 1, v___x_3735_);
lean_ctor_set(v___x_3738_, 2, v___x_3737_);
lean_ctor_set(v___x_3738_, 3, v___x_3705_);
lean_inc_ref(v___x_3738_);
v___x_3739_ = l_Lean_Syntax_node2(v___x_3698_, v___x_3715_, v___x_3734_, v___x_3738_);
v___x_3740_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3741_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3698_);
lean_ctor_set(v___x_3741_, 1, v___x_3715_);
lean_ctor_set(v___x_3741_, 2, v___x_3740_);
v___x_3742_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3698_);
lean_ctor_set(v___x_3743_, 1, v___x_3742_);
lean_inc_ref(v___x_3743_);
lean_inc_ref(v___x_3741_);
v___x_3744_ = l_Lean_Syntax_node4(v___x_3698_, v___x_3730_, v___x_3739_, v___x_3741_, v___x_3743_, v_snd_3673_);
lean_inc_ref(v___x_3729_);
v___x_3745_ = l_Lean_Syntax_node2(v___x_3698_, v___x_3728_, v___x_3729_, v___x_3744_);
v___x_3746_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3698_);
lean_ctor_set(v___x_3747_, 1, v___x_3746_);
lean_inc_ref_n(v___x_3747_, 2);
lean_inc_ref_n(v___x_3726_, 2);
lean_inc_ref_n(v___x_3719_, 2);
v___x_3748_ = l_Lean_Syntax_node5(v___x_3698_, v___x_3716_, v___x_3719_, v___x_3723_, v___x_3726_, v___x_3745_, v___x_3747_);
v___x_3749_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3750_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3751_ = l_Lean_addMacroScope(v_quotContext_3696_, v___x_3750_, v_currMacroScope_3697_);
v___x_3752_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3698_);
lean_ctor_set(v___x_3752_, 1, v___x_3749_);
lean_ctor_set(v___x_3752_, 2, v___x_3751_);
lean_ctor_set(v___x_3752_, 3, v___x_3705_);
v___x_3753_ = l_String_toRawSubstring_x27(v___x_3624_);
v___x_3754_ = l_Lean_addMacroScope(v_quotContext_3696_, v___x_3612_, v_currMacroScope_3697_);
v___x_3755_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3698_);
lean_ctor_set(v___x_3755_, 1, v___x_3753_);
lean_ctor_set(v___x_3755_, 2, v___x_3754_);
lean_ctor_set(v___x_3755_, 3, v___x_3705_);
v___x_3756_ = l_Lean_Syntax_node2(v___x_3698_, v___x_3715_, v___x_3755_, v___x_3738_);
v___x_3757_ = l_Lean_Syntax_node4(v___x_3698_, v___x_3730_, v___x_3756_, v___x_3741_, v___x_3743_, v_fst_3672_);
v___x_3758_ = l_Lean_Syntax_node2(v___x_3698_, v___x_3728_, v___x_3729_, v___x_3757_);
v___x_3759_ = l_Lean_Syntax_node5(v___x_3698_, v___x_3716_, v___x_3719_, v___x_3752_, v___x_3726_, v___x_3758_, v___x_3747_);
v___x_3760_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3761_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3762_ = l_Lean_addMacroScope(v_quotContext_3696_, v___x_3761_, v_currMacroScope_3697_);
v___x_3763_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3698_);
lean_ctor_set(v___x_3763_, 1, v___x_3760_);
lean_ctor_set(v___x_3763_, 2, v___x_3762_);
lean_ctor_set(v___x_3763_, 3, v___x_3705_);
v___x_3764_ = l_Lean_Syntax_node5(v___x_3698_, v___x_3716_, v___x_3719_, v___x_3763_, v___x_3726_, v_a_3691_, v___x_3747_);
v___x_3765_ = l_Lean_Syntax_node3(v___x_3698_, v___x_3715_, v___x_3748_, v___x_3759_, v___x_3764_);
v___x_3766_ = l_Lean_Syntax_node2(v___x_3698_, v___x_3699_, v___x_3714_, v___x_3765_);
v_a_3635_ = v___x_3766_;
goto v___jp_3634_;
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
lean_del_object(v___x_3680_);
lean_del_object(v___x_3675_);
lean_dec(v_snd_3673_);
lean_dec(v_fst_3672_);
lean_del_object(v___x_3666_);
lean_del_object(v___x_3661_);
lean_del_object(v___x_3657_);
lean_dec_ref(v___y_3631_);
lean_dec_ref(v___x_3624_);
lean_dec_ref(v___x_3623_);
lean_dec_ref(v___x_3622_);
lean_dec_ref(v___x_3621_);
lean_dec(v___x_3612_);
v___y_3639_ = v___x_3689_;
goto v___jp_3638_;
}
}
else
{
lean_object* v_a_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3781_; 
lean_del_object(v___x_3680_);
lean_dec(v_default_3678_);
lean_del_object(v___x_3675_);
lean_dec(v_snd_3673_);
lean_dec(v_fst_3672_);
lean_del_object(v___x_3666_);
lean_del_object(v___x_3661_);
lean_del_object(v___x_3657_);
lean_dec_ref(v___y_3631_);
lean_dec_ref(v___x_3624_);
lean_dec_ref(v___x_3623_);
lean_dec_ref(v___x_3622_);
lean_dec_ref(v___x_3621_);
lean_dec(v___x_3612_);
v_a_3774_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3776_ = v___x_3687_;
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_a_3774_);
lean_dec(v___x_3687_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3779_; 
if (v_isShared_3777_ == 0)
{
v___x_3779_ = v___x_3776_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3774_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
}
else
{
lean_dec_ref(v_points_3677_);
lean_dec(v___x_3620_);
switch(lean_obj_tag(v_default_3678_))
{
case 2:
{
lean_object* v_toCold_3782_; lean_object* v_ref_3783_; lean_object* v_quotContext_3784_; lean_object* v_currMacroScope_3785_; uint8_t v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3796_; 
v_toCold_3782_ = lean_ctor_get(v___y_3631_, 0);
lean_inc_ref(v_toCold_3782_);
v_ref_3783_ = lean_ctor_get(v___y_3631_, 2);
lean_inc(v_ref_3783_);
lean_dec_ref(v___y_3631_);
v_quotContext_3784_ = lean_ctor_get(v_toCold_3782_, 8);
lean_inc_n(v_quotContext_3784_, 2);
v_currMacroScope_3785_ = lean_ctor_get(v_toCold_3782_, 9);
lean_inc_n(v_currMacroScope_3785_, 2);
lean_dec_ref(v_toCold_3782_);
v___x_3786_ = 0;
v___x_3787_ = l_Lean_SourceInfo_fromRef(v_ref_3783_, v___x_3786_);
lean_dec(v_ref_3783_);
v___x_3788_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3789_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3790_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3621_);
v___x_3791_ = l_Lean_Name_mkStr2(v___x_3621_, v___x_3790_);
v___x_3792_ = l_Lean_addMacroScope(v_quotContext_3784_, v___x_3791_, v_currMacroScope_3785_);
lean_inc_ref(v___x_3623_);
lean_inc_ref(v___x_3622_);
v___x_3793_ = l_Lean_Name_mkStr4(v___x_3622_, v___x_3623_, v___x_3621_, v___x_3790_);
v___x_3794_ = lean_box(0);
lean_inc(v___x_3793_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set_tag(v___x_3680_, 1);
lean_ctor_set(v___x_3680_, 1, v___x_3794_);
lean_ctor_set(v___x_3680_, 0, v___x_3793_);
v___x_3796_ = v___x_3680_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3793_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v___x_3794_);
v___x_3796_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
lean_object* v___x_3798_; 
if (v_isShared_3652_ == 0)
{
lean_ctor_set_tag(v___x_3651_, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3793_);
v___x_3798_ = v___x_3651_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3793_);
v___x_3798_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
lean_object* v___x_3800_; 
if (v_isShared_3676_ == 0)
{
lean_ctor_set_tag(v___x_3675_, 1);
lean_ctor_set(v___x_3675_, 1, v___x_3794_);
lean_ctor_set(v___x_3675_, 0, v___x_3798_);
v___x_3800_ = v___x_3675_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v___x_3798_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v___x_3794_);
v___x_3800_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
lean_object* v___x_3802_; 
if (v_isShared_3667_ == 0)
{
lean_ctor_set_tag(v___x_3666_, 1);
lean_ctor_set(v___x_3666_, 1, v___x_3800_);
lean_ctor_set(v___x_3666_, 0, v___x_3796_);
v___x_3802_ = v___x_3666_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v___x_3796_);
lean_ctor_set(v_reuseFailAlloc_3869_, 1, v___x_3800_);
v___x_3802_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3808_; 
lean_inc_n(v___x_3787_, 2);
v___x_3803_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3787_);
lean_ctor_set(v___x_3803_, 1, v___x_3789_);
lean_ctor_set(v___x_3803_, 2, v___x_3792_);
lean_ctor_set(v___x_3803_, 3, v___x_3802_);
v___x_3804_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3805_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3806_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3662_ == 0)
{
lean_ctor_set_tag(v___x_3661_, 2);
lean_ctor_set(v___x_3661_, 1, v___x_3806_);
lean_ctor_set(v___x_3661_, 0, v___x_3787_);
v___x_3808_ = v___x_3661_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3787_);
lean_ctor_set(v_reuseFailAlloc_3868_, 1, v___x_3806_);
v___x_3808_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3815_; 
v___x_3809_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3810_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3785_);
lean_inc(v_quotContext_3784_);
v___x_3811_ = l_Lean_addMacroScope(v_quotContext_3784_, v___x_3810_, v_currMacroScope_3785_);
lean_inc_n(v___x_3787_, 2);
v___x_3812_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3787_);
lean_ctor_set(v___x_3812_, 1, v___x_3809_);
lean_ctor_set(v___x_3812_, 2, v___x_3811_);
lean_ctor_set(v___x_3812_, 3, v___x_3794_);
v___x_3813_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3658_ == 0)
{
lean_ctor_set_tag(v___x_3657_, 2);
lean_ctor_set(v___x_3657_, 1, v___x_3813_);
lean_ctor_set(v___x_3657_, 0, v___x_3787_);
v___x_3815_ = v___x_3657_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3787_);
lean_ctor_set(v_reuseFailAlloc_3867_, 1, v___x_3813_);
v___x_3815_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3816_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3817_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3787_, 22);
v___x_3818_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3787_);
lean_ctor_set(v___x_3818_, 1, v___x_3816_);
v___x_3819_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3820_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3821_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3785_, 5);
lean_inc_n(v_quotContext_3784_, 5);
v___x_3822_ = l_Lean_addMacroScope(v_quotContext_3784_, v___x_3821_, v_currMacroScope_3785_);
v___x_3823_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3787_);
lean_ctor_set(v___x_3823_, 1, v___x_3820_);
lean_ctor_set(v___x_3823_, 2, v___x_3822_);
lean_ctor_set(v___x_3823_, 3, v___x_3794_);
v___x_3824_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3825_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3826_ = l_Lean_addMacroScope(v_quotContext_3784_, v___x_3825_, v_currMacroScope_3785_);
v___x_3827_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3787_);
lean_ctor_set(v___x_3827_, 1, v___x_3824_);
lean_ctor_set(v___x_3827_, 2, v___x_3826_);
lean_ctor_set(v___x_3827_, 3, v___x_3794_);
lean_inc_ref(v___x_3827_);
v___x_3828_ = l_Lean_Syntax_node2(v___x_3787_, v___x_3804_, v___x_3823_, v___x_3827_);
v___x_3829_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3830_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3787_);
lean_ctor_set(v___x_3830_, 1, v___x_3804_);
lean_ctor_set(v___x_3830_, 2, v___x_3829_);
v___x_3831_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3832_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3787_);
lean_ctor_set(v___x_3832_, 1, v___x_3831_);
lean_inc_ref(v___x_3832_);
lean_inc_ref(v___x_3830_);
v___x_3833_ = l_Lean_Syntax_node4(v___x_3787_, v___x_3819_, v___x_3828_, v___x_3830_, v___x_3832_, v_snd_3673_);
lean_inc_ref(v___x_3818_);
v___x_3834_ = l_Lean_Syntax_node2(v___x_3787_, v___x_3817_, v___x_3818_, v___x_3833_);
v___x_3835_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3787_);
lean_ctor_set(v___x_3836_, 1, v___x_3835_);
lean_inc_ref_n(v___x_3836_, 2);
lean_inc_ref_n(v___x_3815_, 2);
lean_inc_ref_n(v___x_3808_, 2);
v___x_3837_ = l_Lean_Syntax_node5(v___x_3787_, v___x_3805_, v___x_3808_, v___x_3812_, v___x_3815_, v___x_3834_, v___x_3836_);
v___x_3838_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3839_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3840_ = l_Lean_addMacroScope(v_quotContext_3784_, v___x_3839_, v_currMacroScope_3785_);
v___x_3841_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3787_);
lean_ctor_set(v___x_3841_, 1, v___x_3838_);
lean_ctor_set(v___x_3841_, 2, v___x_3840_);
lean_ctor_set(v___x_3841_, 3, v___x_3794_);
v___x_3842_ = l_String_toRawSubstring_x27(v___x_3624_);
v___x_3843_ = l_Lean_addMacroScope(v_quotContext_3784_, v___x_3612_, v_currMacroScope_3785_);
v___x_3844_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3787_);
lean_ctor_set(v___x_3844_, 1, v___x_3842_);
lean_ctor_set(v___x_3844_, 2, v___x_3843_);
lean_ctor_set(v___x_3844_, 3, v___x_3794_);
v___x_3845_ = l_Lean_Syntax_node2(v___x_3787_, v___x_3804_, v___x_3844_, v___x_3827_);
v___x_3846_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3847_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3848_ = l_Lean_addMacroScope(v_quotContext_3784_, v___x_3847_, v_currMacroScope_3785_);
v___x_3849_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3787_);
lean_ctor_set(v___x_3849_, 1, v___x_3846_);
lean_ctor_set(v___x_3849_, 2, v___x_3848_);
lean_ctor_set(v___x_3849_, 3, v___x_3794_);
v___x_3850_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30);
v___x_3851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5));
v___x_3852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4));
v___x_3853_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31));
v___x_3854_ = l_Lean_addMacroScope(v_quotContext_3784_, v___x_3853_, v_currMacroScope_3785_);
v___x_3855_ = l_Lean_Name_mkStr4(v___x_3622_, v___x_3623_, v___x_3851_, v___x_3852_);
v___x_3856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3855_);
lean_ctor_set(v___x_3856_, 1, v___x_3794_);
v___x_3857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
lean_ctor_set(v___x_3857_, 1, v___x_3794_);
v___x_3858_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3787_);
lean_ctor_set(v___x_3858_, 1, v___x_3850_);
lean_ctor_set(v___x_3858_, 2, v___x_3854_);
lean_ctor_set(v___x_3858_, 3, v___x_3857_);
v___x_3859_ = l_Lean_Syntax_node5(v___x_3787_, v___x_3805_, v___x_3808_, v___x_3849_, v___x_3815_, v___x_3858_, v___x_3836_);
v___x_3860_ = l_Lean_Syntax_node1(v___x_3787_, v___x_3804_, v___x_3859_);
v___x_3861_ = l_Lean_Syntax_node2(v___x_3787_, v___x_3788_, v_fst_3672_, v___x_3860_);
v___x_3862_ = l_Lean_Syntax_node4(v___x_3787_, v___x_3819_, v___x_3845_, v___x_3830_, v___x_3832_, v___x_3861_);
v___x_3863_ = l_Lean_Syntax_node2(v___x_3787_, v___x_3817_, v___x_3818_, v___x_3862_);
v___x_3864_ = l_Lean_Syntax_node5(v___x_3787_, v___x_3805_, v___x_3808_, v___x_3841_, v___x_3815_, v___x_3863_, v___x_3836_);
v___x_3865_ = l_Lean_Syntax_node2(v___x_3787_, v___x_3804_, v___x_3837_, v___x_3864_);
v___x_3866_ = l_Lean_Syntax_node2(v___x_3787_, v___x_3788_, v___x_3803_, v___x_3865_);
v_a_3635_ = v___x_3866_;
goto v___jp_3634_;
}
}
}
}
}
}
}
case 3:
{
lean_object* v_e_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
lean_del_object(v___x_3651_);
v_e_3873_ = lean_ctor_get(v_default_3678_, 0);
lean_inc_ref(v_e_3873_);
lean_dec_ref_known(v_default_3678_, 1);
v___x_3874_ = lean_box(1);
v___x_3875_ = l_Lean_PrettyPrinter_delab(v_e_3873_, v___x_3874_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_toCold_3876_; lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3962_; 
v_toCold_3876_ = lean_ctor_get(v___y_3631_, 0);
lean_inc_ref(v_toCold_3876_);
v_a_3877_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3879_ = v___x_3875_;
v_isShared_3880_ = v_isSharedCheck_3962_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3875_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3962_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v_ref_3881_; lean_object* v_quotContext_3882_; lean_object* v_currMacroScope_3883_; uint8_t v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3894_; 
v_ref_3881_ = lean_ctor_get(v___y_3631_, 2);
lean_inc(v_ref_3881_);
lean_dec_ref(v___y_3631_);
v_quotContext_3882_ = lean_ctor_get(v_toCold_3876_, 8);
lean_inc_n(v_quotContext_3882_, 2);
v_currMacroScope_3883_ = lean_ctor_get(v_toCold_3876_, 9);
lean_inc_n(v_currMacroScope_3883_, 2);
lean_dec_ref(v_toCold_3876_);
v___x_3884_ = 0;
v___x_3885_ = l_Lean_SourceInfo_fromRef(v_ref_3881_, v___x_3884_);
lean_dec(v_ref_3881_);
v___x_3886_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3887_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3888_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3621_);
v___x_3889_ = l_Lean_Name_mkStr2(v___x_3621_, v___x_3888_);
v___x_3890_ = l_Lean_addMacroScope(v_quotContext_3882_, v___x_3889_, v_currMacroScope_3883_);
v___x_3891_ = l_Lean_Name_mkStr4(v___x_3622_, v___x_3623_, v___x_3621_, v___x_3888_);
v___x_3892_ = lean_box(0);
lean_inc(v___x_3891_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set_tag(v___x_3680_, 1);
lean_ctor_set(v___x_3680_, 1, v___x_3892_);
lean_ctor_set(v___x_3680_, 0, v___x_3891_);
v___x_3894_ = v___x_3680_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v___x_3891_);
lean_ctor_set(v_reuseFailAlloc_3961_, 1, v___x_3892_);
v___x_3894_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
lean_object* v___x_3896_; 
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 0, v___x_3891_);
v___x_3896_ = v___x_3879_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v___x_3891_);
v___x_3896_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
lean_object* v___x_3898_; 
if (v_isShared_3676_ == 0)
{
lean_ctor_set_tag(v___x_3675_, 1);
lean_ctor_set(v___x_3675_, 1, v___x_3892_);
lean_ctor_set(v___x_3675_, 0, v___x_3896_);
v___x_3898_ = v___x_3675_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3896_);
lean_ctor_set(v_reuseFailAlloc_3959_, 1, v___x_3892_);
v___x_3898_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
lean_object* v___x_3900_; 
if (v_isShared_3667_ == 0)
{
lean_ctor_set_tag(v___x_3666_, 1);
lean_ctor_set(v___x_3666_, 1, v___x_3898_);
lean_ctor_set(v___x_3666_, 0, v___x_3894_);
v___x_3900_ = v___x_3666_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3894_);
lean_ctor_set(v_reuseFailAlloc_3958_, 1, v___x_3898_);
v___x_3900_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3906_; 
lean_inc_n(v___x_3885_, 2);
v___x_3901_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3885_);
lean_ctor_set(v___x_3901_, 1, v___x_3887_);
lean_ctor_set(v___x_3901_, 2, v___x_3890_);
lean_ctor_set(v___x_3901_, 3, v___x_3900_);
v___x_3902_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3903_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3904_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3662_ == 0)
{
lean_ctor_set_tag(v___x_3661_, 2);
lean_ctor_set(v___x_3661_, 1, v___x_3904_);
lean_ctor_set(v___x_3661_, 0, v___x_3885_);
v___x_3906_ = v___x_3661_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v___x_3885_);
lean_ctor_set(v_reuseFailAlloc_3957_, 1, v___x_3904_);
v___x_3906_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3913_; 
v___x_3907_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3908_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3883_);
lean_inc(v_quotContext_3882_);
v___x_3909_ = l_Lean_addMacroScope(v_quotContext_3882_, v___x_3908_, v_currMacroScope_3883_);
lean_inc_n(v___x_3885_, 2);
v___x_3910_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3885_);
lean_ctor_set(v___x_3910_, 1, v___x_3907_);
lean_ctor_set(v___x_3910_, 2, v___x_3909_);
lean_ctor_set(v___x_3910_, 3, v___x_3892_);
v___x_3911_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3658_ == 0)
{
lean_ctor_set_tag(v___x_3657_, 2);
lean_ctor_set(v___x_3657_, 1, v___x_3911_);
lean_ctor_set(v___x_3657_, 0, v___x_3885_);
v___x_3913_ = v___x_3657_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3885_);
lean_ctor_set(v_reuseFailAlloc_3956_, 1, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3914_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3915_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3885_, 21);
v___x_3916_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3885_);
lean_ctor_set(v___x_3916_, 1, v___x_3914_);
v___x_3917_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3918_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3919_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3883_, 4);
lean_inc_n(v_quotContext_3882_, 4);
v___x_3920_ = l_Lean_addMacroScope(v_quotContext_3882_, v___x_3919_, v_currMacroScope_3883_);
v___x_3921_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3885_);
lean_ctor_set(v___x_3921_, 1, v___x_3918_);
lean_ctor_set(v___x_3921_, 2, v___x_3920_);
lean_ctor_set(v___x_3921_, 3, v___x_3892_);
v___x_3922_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3923_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3924_ = l_Lean_addMacroScope(v_quotContext_3882_, v___x_3923_, v_currMacroScope_3883_);
v___x_3925_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3885_);
lean_ctor_set(v___x_3925_, 1, v___x_3922_);
lean_ctor_set(v___x_3925_, 2, v___x_3924_);
lean_ctor_set(v___x_3925_, 3, v___x_3892_);
lean_inc_ref(v___x_3925_);
v___x_3926_ = l_Lean_Syntax_node2(v___x_3885_, v___x_3902_, v___x_3921_, v___x_3925_);
v___x_3927_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3928_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3885_);
lean_ctor_set(v___x_3928_, 1, v___x_3902_);
lean_ctor_set(v___x_3928_, 2, v___x_3927_);
v___x_3929_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3930_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3885_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
lean_inc_ref(v___x_3930_);
lean_inc_ref(v___x_3928_);
v___x_3931_ = l_Lean_Syntax_node4(v___x_3885_, v___x_3917_, v___x_3926_, v___x_3928_, v___x_3930_, v_snd_3673_);
lean_inc_ref(v___x_3916_);
v___x_3932_ = l_Lean_Syntax_node2(v___x_3885_, v___x_3915_, v___x_3916_, v___x_3931_);
v___x_3933_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3934_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3885_);
lean_ctor_set(v___x_3934_, 1, v___x_3933_);
lean_inc_ref_n(v___x_3934_, 2);
lean_inc_ref_n(v___x_3913_, 2);
lean_inc_ref_n(v___x_3906_, 2);
v___x_3935_ = l_Lean_Syntax_node5(v___x_3885_, v___x_3903_, v___x_3906_, v___x_3910_, v___x_3913_, v___x_3932_, v___x_3934_);
v___x_3936_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3937_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3938_ = l_Lean_addMacroScope(v_quotContext_3882_, v___x_3937_, v_currMacroScope_3883_);
v___x_3939_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3885_);
lean_ctor_set(v___x_3939_, 1, v___x_3936_);
lean_ctor_set(v___x_3939_, 2, v___x_3938_);
lean_ctor_set(v___x_3939_, 3, v___x_3892_);
v___x_3940_ = l_String_toRawSubstring_x27(v___x_3624_);
v___x_3941_ = l_Lean_addMacroScope(v_quotContext_3882_, v___x_3612_, v_currMacroScope_3883_);
v___x_3942_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3885_);
lean_ctor_set(v___x_3942_, 1, v___x_3940_);
lean_ctor_set(v___x_3942_, 2, v___x_3941_);
lean_ctor_set(v___x_3942_, 3, v___x_3892_);
v___x_3943_ = l_Lean_Syntax_node2(v___x_3885_, v___x_3902_, v___x_3942_, v___x_3925_);
v___x_3944_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3945_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3946_ = l_Lean_addMacroScope(v_quotContext_3882_, v___x_3945_, v_currMacroScope_3883_);
v___x_3947_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3885_);
lean_ctor_set(v___x_3947_, 1, v___x_3944_);
lean_ctor_set(v___x_3947_, 2, v___x_3946_);
lean_ctor_set(v___x_3947_, 3, v___x_3892_);
v___x_3948_ = l_Lean_Syntax_node5(v___x_3885_, v___x_3903_, v___x_3906_, v___x_3947_, v___x_3913_, v_a_3877_, v___x_3934_);
v___x_3949_ = l_Lean_Syntax_node1(v___x_3885_, v___x_3902_, v___x_3948_);
v___x_3950_ = l_Lean_Syntax_node2(v___x_3885_, v___x_3886_, v_fst_3672_, v___x_3949_);
v___x_3951_ = l_Lean_Syntax_node4(v___x_3885_, v___x_3917_, v___x_3943_, v___x_3928_, v___x_3930_, v___x_3950_);
v___x_3952_ = l_Lean_Syntax_node2(v___x_3885_, v___x_3915_, v___x_3916_, v___x_3951_);
v___x_3953_ = l_Lean_Syntax_node5(v___x_3885_, v___x_3903_, v___x_3906_, v___x_3939_, v___x_3913_, v___x_3952_, v___x_3934_);
v___x_3954_ = l_Lean_Syntax_node2(v___x_3885_, v___x_3902_, v___x_3935_, v___x_3953_);
v___x_3955_ = l_Lean_Syntax_node2(v___x_3885_, v___x_3886_, v___x_3901_, v___x_3954_);
v_a_3635_ = v___x_3955_;
goto v___jp_3634_;
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
lean_del_object(v___x_3680_);
lean_del_object(v___x_3675_);
lean_dec(v_snd_3673_);
lean_dec(v_fst_3672_);
lean_del_object(v___x_3666_);
lean_del_object(v___x_3661_);
lean_del_object(v___x_3657_);
lean_dec_ref(v___y_3631_);
lean_dec_ref(v___x_3624_);
lean_dec_ref(v___x_3623_);
lean_dec_ref(v___x_3622_);
lean_dec_ref(v___x_3621_);
lean_dec(v___x_3612_);
v___y_3639_ = v___x_3875_;
goto v___jp_3638_;
}
}
default: 
{
lean_object* v_toCold_3963_; lean_object* v_ref_3964_; lean_object* v_quotContext_3965_; lean_object* v_currMacroScope_3966_; uint8_t v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3977_; 
lean_dec(v_default_3678_);
v_toCold_3963_ = lean_ctor_get(v___y_3631_, 0);
lean_inc_ref(v_toCold_3963_);
v_ref_3964_ = lean_ctor_get(v___y_3631_, 2);
lean_inc(v_ref_3964_);
lean_dec_ref(v___y_3631_);
v_quotContext_3965_ = lean_ctor_get(v_toCold_3963_, 8);
lean_inc_n(v_quotContext_3965_, 2);
v_currMacroScope_3966_ = lean_ctor_get(v_toCold_3963_, 9);
lean_inc_n(v_currMacroScope_3966_, 2);
lean_dec_ref(v_toCold_3963_);
v___x_3967_ = 0;
v___x_3968_ = l_Lean_SourceInfo_fromRef(v_ref_3964_, v___x_3967_);
lean_dec(v_ref_3964_);
v___x_3969_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3970_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3971_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3621_);
v___x_3972_ = l_Lean_Name_mkStr2(v___x_3621_, v___x_3971_);
v___x_3973_ = l_Lean_addMacroScope(v_quotContext_3965_, v___x_3972_, v_currMacroScope_3966_);
v___x_3974_ = l_Lean_Name_mkStr4(v___x_3622_, v___x_3623_, v___x_3621_, v___x_3971_);
v___x_3975_ = lean_box(0);
lean_inc(v___x_3974_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set_tag(v___x_3680_, 1);
lean_ctor_set(v___x_3680_, 1, v___x_3975_);
lean_ctor_set(v___x_3680_, 0, v___x_3974_);
v___x_3977_ = v___x_3680_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v___x_3974_);
lean_ctor_set(v_reuseFailAlloc_4037_, 1, v___x_3975_);
v___x_3977_ = v_reuseFailAlloc_4037_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
lean_object* v___x_3979_; 
if (v_isShared_3652_ == 0)
{
lean_ctor_set_tag(v___x_3651_, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3974_);
v___x_3979_ = v___x_3651_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v___x_3974_);
v___x_3979_ = v_reuseFailAlloc_4036_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
lean_object* v___x_3981_; 
if (v_isShared_3676_ == 0)
{
lean_ctor_set_tag(v___x_3675_, 1);
lean_ctor_set(v___x_3675_, 1, v___x_3975_);
lean_ctor_set(v___x_3675_, 0, v___x_3979_);
v___x_3981_ = v___x_3675_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v___x_3979_);
lean_ctor_set(v_reuseFailAlloc_4035_, 1, v___x_3975_);
v___x_3981_ = v_reuseFailAlloc_4035_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
lean_object* v___x_3983_; 
if (v_isShared_3667_ == 0)
{
lean_ctor_set_tag(v___x_3666_, 1);
lean_ctor_set(v___x_3666_, 1, v___x_3981_);
lean_ctor_set(v___x_3666_, 0, v___x_3977_);
v___x_3983_ = v___x_3666_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_3977_);
lean_ctor_set(v_reuseFailAlloc_4034_, 1, v___x_3981_);
v___x_3983_ = v_reuseFailAlloc_4034_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3989_; 
lean_inc_n(v___x_3968_, 2);
v___x_3984_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3968_);
lean_ctor_set(v___x_3984_, 1, v___x_3970_);
lean_ctor_set(v___x_3984_, 2, v___x_3973_);
lean_ctor_set(v___x_3984_, 3, v___x_3983_);
v___x_3985_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3986_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3987_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3662_ == 0)
{
lean_ctor_set_tag(v___x_3661_, 2);
lean_ctor_set(v___x_3661_, 1, v___x_3987_);
lean_ctor_set(v___x_3661_, 0, v___x_3968_);
v___x_3989_ = v___x_3661_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_3968_);
lean_ctor_set(v_reuseFailAlloc_4033_, 1, v___x_3987_);
v___x_3989_ = v_reuseFailAlloc_4033_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3996_; 
v___x_3990_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3991_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3966_);
lean_inc(v_quotContext_3965_);
v___x_3992_ = l_Lean_addMacroScope(v_quotContext_3965_, v___x_3991_, v_currMacroScope_3966_);
lean_inc_n(v___x_3968_, 2);
v___x_3993_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3968_);
lean_ctor_set(v___x_3993_, 1, v___x_3990_);
lean_ctor_set(v___x_3993_, 2, v___x_3992_);
lean_ctor_set(v___x_3993_, 3, v___x_3975_);
v___x_3994_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3658_ == 0)
{
lean_ctor_set_tag(v___x_3657_, 2);
lean_ctor_set(v___x_3657_, 1, v___x_3994_);
lean_ctor_set(v___x_3657_, 0, v___x_3968_);
v___x_3996_ = v___x_3657_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v___x_3968_);
lean_ctor_set(v_reuseFailAlloc_4032_, 1, v___x_3994_);
v___x_3996_ = v_reuseFailAlloc_4032_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v___x_3997_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3998_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3968_, 17);
v___x_3999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3968_);
lean_ctor_set(v___x_3999_, 1, v___x_3997_);
v___x_4000_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_4001_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_4002_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3966_, 3);
lean_inc_n(v_quotContext_3965_, 3);
v___x_4003_ = l_Lean_addMacroScope(v_quotContext_3965_, v___x_4002_, v_currMacroScope_3966_);
v___x_4004_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4004_, 0, v___x_3968_);
lean_ctor_set(v___x_4004_, 1, v___x_4001_);
lean_ctor_set(v___x_4004_, 2, v___x_4003_);
lean_ctor_set(v___x_4004_, 3, v___x_3975_);
v___x_4005_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4006_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4007_ = l_Lean_addMacroScope(v_quotContext_3965_, v___x_4006_, v_currMacroScope_3966_);
v___x_4008_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4008_, 0, v___x_3968_);
lean_ctor_set(v___x_4008_, 1, v___x_4005_);
lean_ctor_set(v___x_4008_, 2, v___x_4007_);
lean_ctor_set(v___x_4008_, 3, v___x_3975_);
lean_inc_ref(v___x_4008_);
v___x_4009_ = l_Lean_Syntax_node2(v___x_3968_, v___x_3985_, v___x_4004_, v___x_4008_);
v___x_4010_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_4011_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4011_, 0, v___x_3968_);
lean_ctor_set(v___x_4011_, 1, v___x_3985_);
lean_ctor_set(v___x_4011_, 2, v___x_4010_);
v___x_4012_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_4013_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4013_, 0, v___x_3968_);
lean_ctor_set(v___x_4013_, 1, v___x_4012_);
lean_inc_ref(v___x_4013_);
lean_inc_ref(v___x_4011_);
v___x_4014_ = l_Lean_Syntax_node4(v___x_3968_, v___x_4000_, v___x_4009_, v___x_4011_, v___x_4013_, v_snd_3673_);
lean_inc_ref(v___x_3999_);
v___x_4015_ = l_Lean_Syntax_node2(v___x_3968_, v___x_3998_, v___x_3999_, v___x_4014_);
v___x_4016_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_4017_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4017_, 0, v___x_3968_);
lean_ctor_set(v___x_4017_, 1, v___x_4016_);
lean_inc_ref(v___x_4017_);
lean_inc_ref(v___x_3996_);
lean_inc_ref(v___x_3989_);
v___x_4018_ = l_Lean_Syntax_node5(v___x_3968_, v___x_3986_, v___x_3989_, v___x_3993_, v___x_3996_, v___x_4015_, v___x_4017_);
v___x_4019_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_4020_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_4021_ = l_Lean_addMacroScope(v_quotContext_3965_, v___x_4020_, v_currMacroScope_3966_);
v___x_4022_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4022_, 0, v___x_3968_);
lean_ctor_set(v___x_4022_, 1, v___x_4019_);
lean_ctor_set(v___x_4022_, 2, v___x_4021_);
lean_ctor_set(v___x_4022_, 3, v___x_3975_);
v___x_4023_ = l_String_toRawSubstring_x27(v___x_3624_);
v___x_4024_ = l_Lean_addMacroScope(v_quotContext_3965_, v___x_3612_, v_currMacroScope_3966_);
v___x_4025_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4025_, 0, v___x_3968_);
lean_ctor_set(v___x_4025_, 1, v___x_4023_);
lean_ctor_set(v___x_4025_, 2, v___x_4024_);
lean_ctor_set(v___x_4025_, 3, v___x_3975_);
v___x_4026_ = l_Lean_Syntax_node2(v___x_3968_, v___x_3985_, v___x_4025_, v___x_4008_);
v___x_4027_ = l_Lean_Syntax_node4(v___x_3968_, v___x_4000_, v___x_4026_, v___x_4011_, v___x_4013_, v_fst_3672_);
v___x_4028_ = l_Lean_Syntax_node2(v___x_3968_, v___x_3998_, v___x_3999_, v___x_4027_);
v___x_4029_ = l_Lean_Syntax_node5(v___x_3968_, v___x_3986_, v___x_3989_, v___x_4022_, v___x_3996_, v___x_4028_, v___x_4017_);
v___x_4030_ = l_Lean_Syntax_node2(v___x_3968_, v___x_3985_, v___x_4018_, v___x_4029_);
v___x_4031_ = l_Lean_Syntax_node2(v___x_3968_, v___x_3969_, v___x_3984_, v___x_4030_);
v_a_3635_ = v___x_4031_;
goto v___jp_3634_;
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
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4047_; 
lean_del_object(v___x_3666_);
lean_dec(v_snd_3664_);
lean_del_object(v___x_3661_);
lean_del_object(v___x_3657_);
lean_del_object(v___x_3651_);
lean_dec_ref(v___y_3631_);
lean_dec_ref(v___x_3624_);
lean_dec_ref(v___x_3623_);
lean_dec_ref(v___x_3622_);
lean_dec_ref(v___x_3621_);
lean_dec(v___x_3620_);
lean_dec(v___x_3612_);
v_a_4040_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4042_ = v___x_3670_;
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v___x_3670_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4045_; 
if (v_isShared_4043_ == 0)
{
v___x_4045_ = v___x_4042_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_a_4040_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
return v___x_4045_;
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
lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4127_; 
lean_dec(v_a_3642_);
lean_dec(v___x_3620_);
lean_dec(v___x_3618_);
lean_dec_ref(v___x_3613_);
v_isSharedCheck_4127_ = !lean_is_exclusive(v_val_3645_);
if (v_isSharedCheck_4127_ == 0)
{
lean_object* v_unused_4128_; lean_object* v_unused_4129_; 
v_unused_4128_ = lean_ctor_get(v_val_3645_, 1);
lean_dec(v_unused_4128_);
v_unused_4129_ = lean_ctor_get(v_val_3645_, 0);
lean_dec(v_unused_4129_);
v___x_4054_ = v_val_3645_;
v_isShared_4055_ = v_isSharedCheck_4127_;
goto v_resetjp_4053_;
}
else
{
lean_dec(v_val_3645_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4127_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v_toCold_4056_; lean_object* v_ref_4057_; lean_object* v_quotContext_4058_; lean_object* v_currMacroScope_4059_; uint8_t v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4070_; 
v_toCold_4056_ = lean_ctor_get(v___y_3631_, 0);
lean_inc_ref(v_toCold_4056_);
v_ref_4057_ = lean_ctor_get(v___y_3631_, 2);
lean_inc(v_ref_4057_);
lean_dec_ref(v___y_3631_);
v_quotContext_4058_ = lean_ctor_get(v_toCold_4056_, 8);
lean_inc_n(v_quotContext_4058_, 2);
v_currMacroScope_4059_ = lean_ctor_get(v_toCold_4056_, 9);
lean_inc_n(v_currMacroScope_4059_, 2);
lean_dec_ref(v_toCold_4056_);
v___x_4060_ = 0;
v___x_4061_ = l_Lean_SourceInfo_fromRef(v_ref_4057_, v___x_4060_);
lean_dec(v_ref_4057_);
v___x_4062_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_4063_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_4064_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3621_);
v___x_4065_ = l_Lean_Name_mkStr2(v___x_3621_, v___x_4064_);
v___x_4066_ = l_Lean_addMacroScope(v_quotContext_4058_, v___x_4065_, v_currMacroScope_4059_);
v___x_4067_ = l_Lean_Name_mkStr4(v___x_3622_, v___x_3623_, v___x_3621_, v___x_4064_);
v___x_4068_ = lean_box(0);
lean_inc(v___x_4067_);
if (v_isShared_4055_ == 0)
{
lean_ctor_set_tag(v___x_4054_, 1);
lean_ctor_set(v___x_4054_, 1, v___x_4068_);
lean_ctor_set(v___x_4054_, 0, v___x_4067_);
v___x_4070_ = v___x_4054_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4067_);
lean_ctor_set(v_reuseFailAlloc_4126_, 1, v___x_4068_);
v___x_4070_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
lean_object* v___x_4072_; 
if (v_isShared_3648_ == 0)
{
lean_ctor_set_tag(v___x_3647_, 0);
lean_ctor_set(v___x_3647_, 0, v___x_4067_);
v___x_4072_ = v___x_3647_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v___x_4067_);
v___x_4072_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4072_);
lean_ctor_set(v___x_4073_, 1, v___x_4068_);
v___x_4074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4070_);
lean_ctor_set(v___x_4074_, 1, v___x_4073_);
lean_inc_n(v___x_4061_, 23);
v___x_4075_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4061_);
lean_ctor_set(v___x_4075_, 1, v___x_4063_);
lean_ctor_set(v___x_4075_, 2, v___x_4066_);
lean_ctor_set(v___x_4075_, 3, v___x_4074_);
v___x_4076_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_4077_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_4078_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
v___x_4079_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4061_);
lean_ctor_set(v___x_4079_, 1, v___x_4078_);
v___x_4080_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_4081_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc_n(v_currMacroScope_4059_, 4);
lean_inc_n(v_quotContext_4058_, 4);
v___x_4082_ = l_Lean_addMacroScope(v_quotContext_4058_, v___x_4081_, v_currMacroScope_4059_);
v___x_4083_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4061_);
lean_ctor_set(v___x_4083_, 1, v___x_4080_);
lean_ctor_set(v___x_4083_, 2, v___x_4082_);
lean_ctor_set(v___x_4083_, 3, v___x_4068_);
v___x_4084_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
v___x_4085_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4061_);
lean_ctor_set(v___x_4085_, 1, v___x_4084_);
v___x_4086_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_4087_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
v___x_4088_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4061_);
lean_ctor_set(v___x_4088_, 1, v___x_4086_);
v___x_4089_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_4090_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_4091_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_4092_ = l_Lean_addMacroScope(v_quotContext_4058_, v___x_4091_, v_currMacroScope_4059_);
v___x_4093_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4061_);
lean_ctor_set(v___x_4093_, 1, v___x_4090_);
lean_ctor_set(v___x_4093_, 2, v___x_4092_);
lean_ctor_set(v___x_4093_, 3, v___x_4068_);
v___x_4094_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4095_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4096_ = l_Lean_addMacroScope(v_quotContext_4058_, v___x_4095_, v_currMacroScope_4059_);
v___x_4097_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4061_);
lean_ctor_set(v___x_4097_, 1, v___x_4094_);
lean_ctor_set(v___x_4097_, 2, v___x_4096_);
lean_ctor_set(v___x_4097_, 3, v___x_4068_);
lean_inc_ref(v___x_4097_);
v___x_4098_ = l_Lean_Syntax_node2(v___x_4061_, v___x_4076_, v___x_4093_, v___x_4097_);
v___x_4099_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_4100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4061_);
lean_ctor_set(v___x_4100_, 1, v___x_4076_);
lean_ctor_set(v___x_4100_, 2, v___x_4099_);
v___x_4101_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_4102_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4061_);
lean_ctor_set(v___x_4102_, 1, v___x_4101_);
v___x_4103_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_4104_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
v___x_4105_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4061_);
lean_ctor_set(v___x_4105_, 1, v___x_4104_);
v___x_4106_ = l_Lean_Syntax_node1(v___x_4061_, v___x_4103_, v___x_4105_);
lean_inc(v___x_4106_);
lean_inc_ref(v___x_4102_);
lean_inc_ref(v___x_4100_);
v___x_4107_ = l_Lean_Syntax_node4(v___x_4061_, v___x_4089_, v___x_4098_, v___x_4100_, v___x_4102_, v___x_4106_);
lean_inc_ref(v___x_4088_);
v___x_4108_ = l_Lean_Syntax_node2(v___x_4061_, v___x_4087_, v___x_4088_, v___x_4107_);
v___x_4109_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_4110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4061_);
lean_ctor_set(v___x_4110_, 1, v___x_4109_);
lean_inc_ref(v___x_4110_);
lean_inc_ref(v___x_4085_);
lean_inc_ref(v___x_4079_);
v___x_4111_ = l_Lean_Syntax_node5(v___x_4061_, v___x_4077_, v___x_4079_, v___x_4083_, v___x_4085_, v___x_4108_, v___x_4110_);
v___x_4112_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_4113_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_4114_ = l_Lean_addMacroScope(v_quotContext_4058_, v___x_4113_, v_currMacroScope_4059_);
v___x_4115_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4061_);
lean_ctor_set(v___x_4115_, 1, v___x_4112_);
lean_ctor_set(v___x_4115_, 2, v___x_4114_);
lean_ctor_set(v___x_4115_, 3, v___x_4068_);
v___x_4116_ = l_String_toRawSubstring_x27(v___x_3624_);
v___x_4117_ = l_Lean_addMacroScope(v_quotContext_4058_, v___x_3612_, v_currMacroScope_4059_);
v___x_4118_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4061_);
lean_ctor_set(v___x_4118_, 1, v___x_4116_);
lean_ctor_set(v___x_4118_, 2, v___x_4117_);
lean_ctor_set(v___x_4118_, 3, v___x_4068_);
v___x_4119_ = l_Lean_Syntax_node2(v___x_4061_, v___x_4076_, v___x_4118_, v___x_4097_);
v___x_4120_ = l_Lean_Syntax_node4(v___x_4061_, v___x_4089_, v___x_4119_, v___x_4100_, v___x_4102_, v___x_4106_);
v___x_4121_ = l_Lean_Syntax_node2(v___x_4061_, v___x_4087_, v___x_4088_, v___x_4120_);
v___x_4122_ = l_Lean_Syntax_node5(v___x_4061_, v___x_4077_, v___x_4079_, v___x_4115_, v___x_4085_, v___x_4121_, v___x_4110_);
v___x_4123_ = l_Lean_Syntax_node2(v___x_4061_, v___x_4076_, v___x_4111_, v___x_4122_);
v___x_4124_ = l_Lean_Syntax_node2(v___x_4061_, v___x_4062_, v___x_4075_, v___x_4123_);
v_a_3635_ = v___x_4124_;
goto v___jp_3634_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3644_);
lean_dec_ref(v___x_3621_);
if (lean_obj_tag(v_a_3642_) == 1)
{
lean_object* v_val_4131_; lean_object* v_snd_4132_; lean_object* v_fst_4133_; lean_object* v_snd_4134_; lean_object* v___x_4135_; lean_object* v___f_4136_; lean_object* v___x_4137_; 
v_val_4131_ = lean_ctor_get(v_a_3642_, 0);
lean_inc(v_val_4131_);
lean_dec_ref_known(v_a_3642_, 1);
v_snd_4132_ = lean_ctor_get(v_val_4131_, 1);
lean_inc(v_snd_4132_);
v_fst_4133_ = lean_ctor_get(v_val_4131_, 0);
lean_inc(v_fst_4133_);
lean_dec(v_val_4131_);
v_snd_4134_ = lean_ctor_get(v_snd_4132_, 1);
lean_inc(v_snd_4134_);
lean_dec(v_snd_4132_);
v___x_4135_ = lean_box(v___x_3619_);
lean_inc(v___x_3612_);
v___f_4136_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed), 20, 10);
lean_closure_set(v___f_4136_, 0, v_fst_4133_);
lean_closure_set(v___f_4136_, 1, v_snd_4134_);
lean_closure_set(v___f_4136_, 2, v___x_3624_);
lean_closure_set(v___f_4136_, 3, v___x_3612_);
lean_closure_set(v___f_4136_, 4, v___x_3618_);
lean_closure_set(v___f_4136_, 5, v___x_3620_);
lean_closure_set(v___f_4136_, 6, v___x_3622_);
lean_closure_set(v___f_4136_, 7, v___x_3623_);
lean_closure_set(v___f_4136_, 8, v___x_4135_);
lean_closure_set(v___f_4136_, 9, v_arg_3617_);
v___x_4137_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3612_, v___x_3613_, v___f_4136_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
lean_dec_ref(v___y_3631_);
v___y_3639_ = v___x_4137_;
goto v___jp_3638_;
}
else
{
lean_object* v_toCold_4138_; lean_object* v_ref_4139_; lean_object* v_quotContext_4140_; lean_object* v_currMacroScope_4141_; uint8_t v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
lean_dec(v_a_3642_);
lean_dec(v___x_3620_);
lean_dec(v___x_3618_);
lean_dec_ref(v_arg_3617_);
lean_dec_ref(v___x_3613_);
v_toCold_4138_ = lean_ctor_get(v___y_3631_, 0);
lean_inc_ref(v_toCold_4138_);
v_ref_4139_ = lean_ctor_get(v___y_3631_, 2);
lean_inc(v_ref_4139_);
lean_dec_ref(v___y_3631_);
v_quotContext_4140_ = lean_ctor_get(v_toCold_4138_, 8);
lean_inc_n(v_quotContext_4140_, 2);
v_currMacroScope_4141_ = lean_ctor_get(v_toCold_4138_, 9);
lean_inc_n(v_currMacroScope_4141_, 2);
lean_dec_ref(v_toCold_4138_);
v___x_4142_ = 0;
v___x_4143_ = l_Lean_SourceInfo_fromRef(v_ref_4139_, v___x_4142_);
lean_dec(v_ref_4139_);
v___x_4144_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_4145_ = l_Lean_Name_mkStr3(v___x_3622_, v___x_3623_, v___x_4144_);
v___x_4146_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_4147_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_4143_, 13);
v___x_4148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4143_);
lean_ctor_set(v___x_4148_, 1, v___x_4146_);
lean_ctor_set(v___x_4148_, 2, v___x_4147_);
v___x_4149_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_4150_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4143_);
lean_ctor_set(v___x_4150_, 1, v___x_4149_);
v___x_4151_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_4152_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_4153_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_4154_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4143_);
lean_ctor_set(v___x_4154_, 1, v___x_4153_);
v___x_4155_ = l_String_toRawSubstring_x27(v___x_3624_);
v___x_4156_ = l_Lean_addMacroScope(v_quotContext_4140_, v___x_3612_, v_currMacroScope_4141_);
v___x_4157_ = lean_box(0);
v___x_4158_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4143_);
lean_ctor_set(v___x_4158_, 1, v___x_4155_);
lean_ctor_set(v___x_4158_, 2, v___x_4156_);
lean_ctor_set(v___x_4158_, 3, v___x_4157_);
v___x_4159_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_4160_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4143_);
lean_ctor_set(v___x_4160_, 1, v___x_4159_);
v___x_4161_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4162_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4163_ = l_Lean_addMacroScope(v_quotContext_4140_, v___x_4162_, v_currMacroScope_4141_);
v___x_4164_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4143_);
lean_ctor_set(v___x_4164_, 1, v___x_4161_);
lean_ctor_set(v___x_4164_, 2, v___x_4163_);
lean_ctor_set(v___x_4164_, 3, v___x_4157_);
v___x_4165_ = l_Lean_Syntax_node3(v___x_4143_, v___x_4151_, v___x_4158_, v___x_4160_, v___x_4164_);
v___x_4166_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_4167_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4143_);
lean_ctor_set(v___x_4167_, 1, v___x_4166_);
v___x_4168_ = l_Lean_Syntax_node3(v___x_4143_, v___x_4152_, v___x_4154_, v___x_4165_, v___x_4167_);
v___x_4169_ = l_Lean_Syntax_node1(v___x_4143_, v___x_4151_, v___x_4168_);
v___x_4170_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_4171_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4143_);
lean_ctor_set(v___x_4171_, 1, v___x_4170_);
v___x_4172_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_4173_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
v___x_4174_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4143_);
lean_ctor_set(v___x_4174_, 1, v___x_4173_);
v___x_4175_ = l_Lean_Syntax_node1(v___x_4143_, v___x_4172_, v___x_4174_);
v___x_4176_ = l_Lean_Syntax_node5(v___x_4143_, v___x_4145_, v___x_4148_, v___x_4150_, v___x_4169_, v___x_4171_, v___x_4175_);
v_a_3635_ = v___x_4176_;
goto v___jp_3634_;
}
}
}
else
{
lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4184_; 
lean_dec(v_a_3642_);
lean_dec_ref(v___y_3631_);
lean_dec_ref(v___x_3624_);
lean_dec_ref(v___x_3623_);
lean_dec_ref(v___x_3622_);
lean_dec_ref(v___x_3621_);
lean_dec(v___x_3620_);
lean_dec(v___x_3618_);
lean_dec_ref(v_arg_3617_);
lean_dec_ref(v___x_3613_);
lean_dec(v___x_3612_);
v_a_4177_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4179_ = v___x_3643_;
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___x_3643_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4182_; 
if (v_isShared_4180_ == 0)
{
v___x_4182_ = v___x_4179_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
}
}
else
{
lean_object* v_a_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4192_; 
lean_dec_ref(v___y_3631_);
lean_dec_ref(v___x_3624_);
lean_dec_ref(v___x_3623_);
lean_dec_ref(v___x_3622_);
lean_dec_ref(v___x_3621_);
lean_dec(v___x_3620_);
lean_dec(v___x_3618_);
lean_dec_ref(v_arg_3617_);
lean_dec(v_inv_3616_);
lean_dec_ref(v___x_3613_);
lean_dec(v___x_3612_);
v_a_4185_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4187_ = v___x_3641_;
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_a_4185_);
lean_dec(v___x_3641_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v___x_4190_; 
if (v_isShared_4188_ == 0)
{
v___x_4190_ = v___x_4187_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_a_4185_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
v___jp_3634_:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3636_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_a_3635_);
v___x_3637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3637_, 0, v___x_3636_);
return v___x_3637_;
}
v___jp_3638_:
{
if (lean_obj_tag(v___y_3639_) == 0)
{
lean_object* v_a_3640_; 
v_a_3640_ = lean_ctor_get(v___y_3639_, 0);
lean_inc(v_a_3640_);
lean_dec_ref_known(v___y_3639_, 1);
v_a_3635_ = v_a_3640_;
goto v___jp_3634_;
}
else
{
return v___y_3639_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3612_ = stack[0].m_obj;
lean_object* v___x_3613_ = stack[1].m_obj;
lean_object* v___f_3614_ = stack[2].m_obj;
lean_object* v_a_3615_ = stack[3].m_obj;
lean_object* v_inv_3616_ = stack[4].m_obj;
lean_object* v_arg_3617_ = stack[5].m_obj;
lean_object* v___x_3618_ = stack[6].m_obj;
uint8_t v___x_3619_ = stack[7].m_num;
lean_object* v___x_3620_ = stack[8].m_obj;
lean_object* v___x_3621_ = stack[9].m_obj;
lean_object* v___x_3622_ = stack[10].m_obj;
lean_object* v___x_3623_ = stack[11].m_obj;
lean_object* v___x_3624_ = stack[12].m_obj;
lean_object* v___y_3625_ = stack[13].m_obj;
lean_object* v___y_3626_ = stack[14].m_obj;
lean_object* v___y_3627_ = stack[15].m_obj;
lean_object* v___y_3628_ = stack[16].m_obj;
lean_object* v___y_3629_ = stack[17].m_obj;
lean_object* v___y_3630_ = stack[18].m_obj;
lean_object* v___y_3631_ = stack[19].m_obj;
lean_object* v___y_3632_ = stack[20].m_obj;
lean_object* v_res_4193_;
v_res_4193_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(v___x_3612_, v___x_3613_, v___f_3614_, v_a_3615_, v_inv_3616_, v_arg_3617_, v___x_3618_, v___x_3619_, v___x_3620_, v___x_3621_, v___x_3622_, v___x_3623_, v___x_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
stack->m_obj
 = v_res_4193_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed(lean_object** _args){
lean_object* v___x_4194_ = _args[0];
lean_object* v___x_4195_ = _args[1];
lean_object* v___f_4196_ = _args[2];
lean_object* v_a_4197_ = _args[3];
lean_object* v_inv_4198_ = _args[4];
lean_object* v_arg_4199_ = _args[5];
lean_object* v___x_4200_ = _args[6];
lean_object* v___x_4201_ = _args[7];
lean_object* v___x_4202_ = _args[8];
lean_object* v___x_4203_ = _args[9];
lean_object* v___x_4204_ = _args[10];
lean_object* v___x_4205_ = _args[11];
lean_object* v___x_4206_ = _args[12];
lean_object* v___y_4207_ = _args[13];
lean_object* v___y_4208_ = _args[14];
lean_object* v___y_4209_ = _args[15];
lean_object* v___y_4210_ = _args[16];
lean_object* v___y_4211_ = _args[17];
lean_object* v___y_4212_ = _args[18];
lean_object* v___y_4213_ = _args[19];
lean_object* v___y_4214_ = _args[20];
lean_object* v___y_4215_ = _args[21];
_start:
{
uint8_t v___x_80019__boxed_4216_; lean_object* v_res_4217_; 
v___x_80019__boxed_4216_ = lean_unbox(v___x_4201_);
v_res_4217_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(v___x_4194_, v___x_4195_, v___f_4196_, v_a_4197_, v_inv_4198_, v_arg_4199_, v___x_4200_, v___x_80019__boxed_4216_, v___x_4202_, v___x_4203_, v___x_4204_, v___x_4205_, v___x_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
lean_dec(v___y_4214_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4207_);
lean_dec_ref(v_a_4197_);
return v_res_4217_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(lean_object* v_msgData_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v___x_4224_; lean_object* v_env_4225_; uint8_t v___x_4226_; lean_object* v_env_4227_; lean_object* v___x_4228_; lean_object* v_toCold_4229_; lean_object* v_mctx_4230_; lean_object* v_lctx_4231_; lean_object* v_options_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; 
v___x_4224_ = lean_st_ref_get(v___y_4222_);
v_env_4225_ = lean_ctor_get(v___x_4224_, 0);
lean_inc_ref(v_env_4225_);
lean_dec(v___x_4224_);
v___x_4226_ = 0;
v_env_4227_ = l_Lean_Environment_setRecordingDeps(v_env_4225_, v___x_4226_);
v___x_4228_ = lean_st_ref_get(v___y_4220_);
v_toCold_4229_ = lean_ctor_get(v___y_4221_, 0);
v_mctx_4230_ = lean_ctor_get(v___x_4228_, 0);
lean_inc_ref(v_mctx_4230_);
lean_dec(v___x_4228_);
v_lctx_4231_ = lean_ctor_get(v___y_4219_, 2);
v_options_4232_ = lean_ctor_get(v_toCold_4229_, 2);
lean_inc_ref(v_options_4232_);
lean_inc_ref(v_lctx_4231_);
v___x_4233_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4233_, 0, v_env_4227_);
lean_ctor_set(v___x_4233_, 1, v_mctx_4230_);
lean_ctor_set(v___x_4233_, 2, v_lctx_4231_);
lean_ctor_set(v___x_4233_, 3, v_options_4232_);
v___x_4234_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4234_, 0, v___x_4233_);
lean_ctor_set(v___x_4234_, 1, v_msgData_4218_);
v___x_4235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4235_, 0, v___x_4234_);
return v___x_4235_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_4218_ = stack[0].m_obj;
lean_object* v___y_4219_ = stack[1].m_obj;
lean_object* v___y_4220_ = stack[2].m_obj;
lean_object* v___y_4221_ = stack[3].m_obj;
lean_object* v___y_4222_ = stack[4].m_obj;
lean_object* v_res_4236_;
v_res_4236_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msgData_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_);
stack->m_obj
 = v_res_4236_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1___boxed(lean_object* v_msgData_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
lean_object* v_res_4243_; 
v_res_4243_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msgData_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec(v___y_4239_);
lean_dec_ref(v___y_4238_);
return v_res_4243_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(lean_object* v_msg_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v_ref_4250_; lean_object* v___x_4251_; lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4260_; 
v_ref_4250_ = lean_ctor_get(v___y_4247_, 2);
v___x_4251_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msg_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_);
v_a_4252_ = lean_ctor_get(v___x_4251_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4251_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4254_ = v___x_4251_;
v_isShared_4255_ = v_isSharedCheck_4260_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_dec(v___x_4251_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4260_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4256_; lean_object* v___x_4258_; 
lean_inc(v_ref_4250_);
v___x_4256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4256_, 0, v_ref_4250_);
lean_ctor_set(v___x_4256_, 1, v_a_4252_);
if (v_isShared_4255_ == 0)
{
lean_ctor_set_tag(v___x_4254_, 1);
lean_ctor_set(v___x_4254_, 0, v___x_4256_);
v___x_4258_ = v___x_4254_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v___x_4256_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4244_ = stack[0].m_obj;
lean_object* v___y_4245_ = stack[1].m_obj;
lean_object* v___y_4246_ = stack[2].m_obj;
lean_object* v___y_4247_ = stack[3].m_obj;
lean_object* v___y_4248_ = stack[4].m_obj;
lean_object* v_res_4261_;
v_res_4261_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_);
stack->m_obj
 = v_res_4261_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg___boxed(lean_object* v_msg_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_){
_start:
{
lean_object* v_res_4268_; 
v_res_4268_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
lean_dec(v___y_4266_);
lean_dec_ref(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
return v_res_4268_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(lean_object* v_as_4275_, size_t v_i_4276_, size_t v_stop_4277_, lean_object* v_b_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_){
_start:
{
lean_object* v_a_4289_; lean_object* v_a_4294_; uint8_t v___x_4296_; 
v___x_4296_ = lean_usize_dec_eq(v_i_4276_, v_stop_4277_);
if (v___x_4296_ == 0)
{
lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4297_ = lean_array_uget_borrowed(v_as_4275_, v_i_4276_);
v___x_4298_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_4280_, v___y_4282_, v___y_4284_, v___y_4286_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_object* v_a_4299_; lean_object* v___y_4301_; uint8_t v___y_4302_; lean_object* v___y_4317_; lean_object* v_a_4318_; lean_object* v_ref_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
v_a_4299_ = lean_ctor_get(v___x_4298_, 0);
lean_inc(v_a_4299_);
lean_dec_ref_known(v___x_4298_, 1);
v_ref_4321_ = lean_ctor_get(v___y_4285_, 2);
v___x_4322_ = l_Lean_SourceInfo_fromRef(v_ref_4321_, v___x_4296_);
v___x_4323_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__0));
v___x_4324_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__1));
lean_inc(v___x_4322_);
v___x_4325_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4325_, 0, v___x_4322_);
lean_ctor_set(v___x_4325_, 1, v___x_4323_);
v___x_4326_ = l_Lean_Syntax_node1(v___x_4322_, v___x_4324_, v___x_4325_);
lean_inc(v___x_4297_);
v___x_4327_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v___x_4297_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_object* v_a_4328_; lean_object* v___x_4329_; 
v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
lean_inc(v_a_4328_);
lean_dec_ref_known(v___x_4327_, 1);
v___x_4329_ = l_Lean_Elab_Tactic_evalTacticAt(v___x_4326_, v_a_4328_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4329_) == 0)
{
lean_object* v_a_4330_; lean_object* v___x_4331_; 
lean_dec(v_a_4299_);
v_a_4330_ = lean_ctor_get(v___x_4329_, 0);
lean_inc(v_a_4330_);
lean_dec_ref_known(v___x_4329_, 1);
v___x_4331_ = lean_array_mk(v_a_4330_);
v_a_4294_ = v___x_4331_;
goto v___jp_4293_;
}
else
{
lean_object* v_a_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4339_; 
v_a_4332_ = lean_ctor_get(v___x_4329_, 0);
v_isSharedCheck_4339_ = !lean_is_exclusive(v___x_4329_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4334_ = v___x_4329_;
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_a_4332_);
lean_dec(v___x_4329_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___x_4337_; 
lean_inc(v_a_4332_);
if (v_isShared_4335_ == 0)
{
v___x_4337_ = v___x_4334_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v_a_4332_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
v___y_4317_ = v___x_4337_;
v_a_4318_ = v_a_4332_;
goto v___jp_4316_;
}
}
}
}
else
{
lean_object* v_a_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4347_; 
lean_dec(v___x_4326_);
v_a_4340_ = lean_ctor_get(v___x_4327_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4342_ = v___x_4327_;
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_a_4340_);
lean_dec(v___x_4327_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4345_; 
lean_inc(v_a_4340_);
if (v_isShared_4343_ == 0)
{
v___x_4345_ = v___x_4342_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_a_4340_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
v___y_4317_ = v___x_4345_;
v_a_4318_ = v_a_4340_;
goto v___jp_4316_;
}
}
}
v___jp_4300_:
{
if (v___y_4302_ == 0)
{
lean_object* v___x_4303_; 
lean_dec_ref(v___y_4301_);
v___x_4303_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_4299_, v___y_4302_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
lean_dec_ref_known(v___x_4303_, 1);
v___x_4304_ = lean_unsigned_to_nat(1u);
v___x_4305_ = lean_mk_empty_array_with_capacity(v___x_4304_);
lean_inc(v___x_4297_);
v___x_4306_ = lean_array_push(v___x_4305_, v___x_4297_);
v_a_4294_ = v___x_4306_;
goto v___jp_4293_;
}
else
{
lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4314_; 
lean_dec_ref(v_b_4278_);
v_a_4307_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4309_ = v___x_4303_;
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v___x_4303_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4312_; 
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
return v___x_4312_;
}
}
}
}
else
{
lean_dec(v_a_4299_);
lean_dec_ref(v_b_4278_);
if (lean_obj_tag(v___y_4301_) == 0)
{
lean_object* v_a_4315_; 
v_a_4315_ = lean_ctor_get(v___y_4301_, 0);
lean_inc(v_a_4315_);
lean_dec_ref_known(v___y_4301_, 1);
v_a_4289_ = v_a_4315_;
goto v___jp_4288_;
}
else
{
return v___y_4301_;
}
}
}
v___jp_4316_:
{
uint8_t v___x_4319_; 
v___x_4319_ = l_Lean_Exception_isInterrupt(v_a_4318_);
if (v___x_4319_ == 0)
{
uint8_t v___x_4320_; 
v___x_4320_ = l_Lean_Exception_isRuntime(v_a_4318_);
v___y_4301_ = v___y_4317_;
v___y_4302_ = v___x_4320_;
goto v___jp_4300_;
}
else
{
lean_dec_ref(v_a_4318_);
v___y_4301_ = v___y_4317_;
v___y_4302_ = v___x_4319_;
goto v___jp_4300_;
}
}
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4355_; 
lean_dec_ref(v_b_4278_);
v_a_4348_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4350_ = v___x_4298_;
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4298_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4353_; 
if (v_isShared_4351_ == 0)
{
v___x_4353_ = v___x_4350_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
else
{
lean_object* v___x_4356_; 
v___x_4356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4356_, 0, v_b_4278_);
return v___x_4356_;
}
v___jp_4288_:
{
size_t v___x_4290_; size_t v___x_4291_; 
v___x_4290_ = ((size_t)1ULL);
v___x_4291_ = lean_usize_add(v_i_4276_, v___x_4290_);
v_i_4276_ = v___x_4291_;
v_b_4278_ = v_a_4289_;
goto _start;
}
v___jp_4293_:
{
lean_object* v___x_4295_; 
v___x_4295_ = l_Array_append___redArg(v_b_4278_, v_a_4294_);
lean_dec_ref(v_a_4294_);
v_a_4289_ = v___x_4295_;
goto v___jp_4288_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4275_ = stack[0].m_obj;
size_t v_i_4276_ = stack[1].m_num;
size_t v_stop_4277_ = stack[2].m_num;
lean_object* v_b_4278_ = stack[3].m_obj;
lean_object* v___y_4279_ = stack[4].m_obj;
lean_object* v___y_4280_ = stack[5].m_obj;
lean_object* v___y_4281_ = stack[6].m_obj;
lean_object* v___y_4282_ = stack[7].m_obj;
lean_object* v___y_4283_ = stack[8].m_obj;
lean_object* v___y_4284_ = stack[9].m_obj;
lean_object* v___y_4285_ = stack[10].m_obj;
lean_object* v___y_4286_ = stack[11].m_obj;
lean_object* v_res_4357_;
v_res_4357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_as_4275_, v_i_4276_, v_stop_4277_, v_b_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
stack->m_obj
 = v_res_4357_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___boxed(lean_object* v_as_4358_, lean_object* v_i_4359_, lean_object* v_stop_4360_, lean_object* v_b_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
size_t v_i_boxed_4371_; size_t v_stop_boxed_4372_; lean_object* v_res_4373_; 
v_i_boxed_4371_ = lean_unbox_usize(v_i_4359_);
lean_dec(v_i_4359_);
v_stop_boxed_4372_ = lean_unbox_usize(v_stop_4360_);
lean_dec(v_stop_4360_);
v_res_4373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_as_4358_, v_i_boxed_4371_, v_stop_boxed_4372_, v_b_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v___y_4367_);
lean_dec_ref(v___y_4366_);
lean_dec(v___y_4365_);
lean_dec_ref(v___y_4364_);
lean_dec(v___y_4363_);
lean_dec_ref(v___y_4362_);
lean_dec_ref(v_as_4358_);
return v_res_4373_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1(void){
_start:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4375_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__0));
v___x_4376_ = l_Lean_stringToMessageData(v___x_4375_);
return v___x_4376_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant(lean_object* v_vcs_4392_, lean_object* v_inv_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_){
_start:
{
lean_object* v___x_4403_; 
lean_inc(v_inv_4393_);
v___x_4403_ = l_Lean_MVarId_getType(v_inv_4393_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v_a_4404_; lean_object* v___x_4405_; lean_object* v_a_4406_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___x_4420_; uint8_t v___x_4421_; 
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
lean_inc(v_a_4404_);
lean_dec_ref_known(v___x_4403_, 1);
v___x_4405_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_a_4404_, v_a_4399_);
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc_n(v_a_4406_, 2);
lean_dec_ref(v___x_4405_);
v___x_4420_ = l_Lean_Expr_cleanupAnnotations(v_a_4406_);
v___x_4421_ = l_Lean_Expr_isApp(v___x_4420_);
if (v___x_4421_ == 0)
{
lean_dec_ref(v___x_4420_);
lean_dec(v_inv_4393_);
v___y_4408_ = v_a_4394_;
v___y_4409_ = v_a_4395_;
v___y_4410_ = v_a_4396_;
v___y_4411_ = v_a_4397_;
v___y_4412_ = v_a_4398_;
v___y_4413_ = v_a_4399_;
v___y_4414_ = v_a_4400_;
v___y_4415_ = v_a_4401_;
goto v___jp_4407_;
}
else
{
lean_object* v___x_4422_; uint8_t v___x_4423_; 
v___x_4422_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4420_);
v___x_4423_ = l_Lean_Expr_isApp(v___x_4422_);
if (v___x_4423_ == 0)
{
lean_dec_ref(v___x_4422_);
lean_dec(v_inv_4393_);
v___y_4408_ = v_a_4394_;
v___y_4409_ = v_a_4395_;
v___y_4410_ = v_a_4396_;
v___y_4411_ = v_a_4397_;
v___y_4412_ = v_a_4398_;
v___y_4413_ = v_a_4399_;
v___y_4414_ = v_a_4400_;
v___y_4415_ = v_a_4401_;
goto v___jp_4407_;
}
else
{
lean_object* v_arg_4424_; lean_object* v___x_4425_; uint8_t v___x_4426_; 
v_arg_4424_ = lean_ctor_get(v___x_4422_, 1);
lean_inc_ref(v_arg_4424_);
v___x_4425_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4422_);
v___x_4426_ = l_Lean_Expr_isApp(v___x_4425_);
if (v___x_4426_ == 0)
{
lean_dec_ref(v___x_4425_);
lean_dec_ref(v_arg_4424_);
lean_dec(v_inv_4393_);
v___y_4408_ = v_a_4394_;
v___y_4409_ = v_a_4395_;
v___y_4410_ = v_a_4396_;
v___y_4411_ = v_a_4397_;
v___y_4412_ = v_a_4398_;
v___y_4413_ = v_a_4399_;
v___y_4414_ = v_a_4400_;
v___y_4415_ = v_a_4401_;
goto v___jp_4407_;
}
else
{
lean_object* v_arg_4427_; lean_object* v___x_4428_; uint8_t v___x_4429_; 
v_arg_4427_ = lean_ctor_get(v___x_4425_, 1);
lean_inc_ref(v_arg_4427_);
v___x_4428_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4425_);
v___x_4429_ = l_Lean_Expr_isApp(v___x_4428_);
if (v___x_4429_ == 0)
{
lean_dec_ref(v___x_4428_);
lean_dec_ref(v_arg_4427_);
lean_dec_ref(v_arg_4424_);
lean_dec(v_inv_4393_);
v___y_4408_ = v_a_4394_;
v___y_4409_ = v_a_4395_;
v___y_4410_ = v_a_4396_;
v___y_4411_ = v_a_4397_;
v___y_4412_ = v_a_4398_;
v___y_4413_ = v_a_4399_;
v___y_4414_ = v_a_4400_;
v___y_4415_ = v_a_4401_;
goto v___jp_4407_;
}
else
{
lean_object* v_arg_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; uint8_t v___x_4436_; 
v_arg_4430_ = lean_ctor_get(v___x_4428_, 1);
lean_inc_ref(v_arg_4430_);
v___x_4431_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4428_);
v___x_4432_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1));
v___x_4433_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3));
v___x_4434_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__2));
v___x_4435_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__3));
v___x_4436_ = l_Lean_Expr_isConstOf(v___x_4431_, v___x_4435_);
if (v___x_4436_ == 0)
{
lean_dec_ref(v___x_4431_);
lean_dec_ref(v_arg_4430_);
lean_dec_ref(v_arg_4427_);
lean_dec_ref(v_arg_4424_);
lean_dec(v_inv_4393_);
v___y_4408_ = v_a_4394_;
v___y_4409_ = v_a_4395_;
v___y_4410_ = v_a_4396_;
v___y_4411_ = v_a_4397_;
v___y_4412_ = v_a_4398_;
v___y_4413_ = v_a_4399_;
v___y_4414_ = v_a_4400_;
v___y_4415_ = v_a_4401_;
goto v___jp_4407_;
}
else
{
lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v_a_4443_; lean_object* v___x_4454_; lean_object* v___x_4455_; uint8_t v___x_4456_; 
lean_dec(v_a_4406_);
v___x_4437_ = lean_unsigned_to_nat(1u);
v___x_4438_ = l_Lean_Expr_constLevels_x21(v___x_4431_);
lean_dec_ref(v___x_4431_);
v___x_4439_ = lean_unsigned_to_nat(0u);
v___x_4440_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__4));
lean_inc(v___x_4438_);
v___x_4441_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v___x_4438_, v___x_4438_, v___x_4437_, v___x_4440_);
lean_dec(v___x_4438_);
v___x_4454_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__8));
v___x_4455_ = lean_array_get_size(v_vcs_4392_);
v___x_4456_ = lean_nat_dec_lt(v___x_4439_, v___x_4455_);
if (v___x_4456_ == 0)
{
v_a_4443_ = v___x_4454_;
goto v___jp_4442_;
}
else
{
size_t v___x_4457_; size_t v___x_4458_; lean_object* v___x_4459_; 
v___x_4457_ = ((size_t)0ULL);
v___x_4458_ = lean_usize_of_nat(v___x_4455_);
v___x_4459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_vcs_4392_, v___x_4457_, v___x_4458_, v___x_4454_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_object* v_a_4460_; 
v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
lean_inc(v_a_4460_);
lean_dec_ref_known(v___x_4459_, 1);
v_a_4443_ = v_a_4460_;
goto v___jp_4442_;
}
else
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
lean_dec(v___x_4441_);
lean_dec_ref(v_arg_4430_);
lean_dec_ref(v_arg_4427_);
lean_dec_ref(v_arg_4424_);
lean_dec(v_inv_4393_);
v_a_4461_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4459_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4459_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4466_; 
if (v_isShared_4464_ == 0)
{
v___x_4466_ = v___x_4463_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_a_4461_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
}
}
v___jp_4442_:
{
lean_object* v___x_4444_; lean_object* v___f_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___f_4452_; lean_object* v___x_4453_; 
v___x_4444_ = lean_box(v___x_4436_);
lean_inc_ref(v_arg_4424_);
lean_inc_n(v_inv_4393_, 2);
lean_inc_ref(v_a_4443_);
v___f_4445_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed), 15, 5);
lean_closure_set(v___f_4445_, 0, v_a_4443_);
lean_closure_set(v___f_4445_, 1, v_inv_4393_);
lean_closure_set(v___f_4445_, 2, v___x_4444_);
lean_closure_set(v___f_4445_, 3, v___x_4437_);
lean_closure_set(v___f_4445_, 4, v_arg_4424_);
v___x_4446_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__5));
v___x_4447_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__6));
v___x_4448_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__7));
v___x_4449_ = l_Lean_mkConst(v___x_4448_, v___x_4441_);
v___x_4450_ = l_Lean_mkAppB(v___x_4449_, v_arg_4430_, v_arg_4427_);
v___x_4451_ = lean_box(v___x_4436_);
v___f_4452_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed), 22, 13);
lean_closure_set(v___f_4452_, 0, v___x_4447_);
lean_closure_set(v___f_4452_, 1, v___x_4450_);
lean_closure_set(v___f_4452_, 2, v___f_4445_);
lean_closure_set(v___f_4452_, 3, v_a_4443_);
lean_closure_set(v___f_4452_, 4, v_inv_4393_);
lean_closure_set(v___f_4452_, 5, v_arg_4424_);
lean_closure_set(v___f_4452_, 6, v___x_4437_);
lean_closure_set(v___f_4452_, 7, v___x_4451_);
lean_closure_set(v___f_4452_, 8, v___x_4439_);
lean_closure_set(v___f_4452_, 9, v___x_4434_);
lean_closure_set(v___f_4452_, 10, v___x_4432_);
lean_closure_set(v___f_4452_, 11, v___x_4433_);
lean_closure_set(v___f_4452_, 12, v___x_4446_);
v___x_4453_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_inv_4393_, v___f_4452_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
return v___x_4453_;
}
}
}
}
}
}
v___jp_4407_:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4416_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1, &l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1);
v___x_4417_ = l_Lean_MessageData_ofExpr(v_a_4406_);
v___x_4418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4418_, 0, v___x_4416_);
lean_ctor_set(v___x_4418_, 1, v___x_4417_);
v___x_4419_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v___x_4418_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
return v___x_4419_;
}
}
else
{
lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4476_; 
lean_dec(v_inv_4393_);
v_a_4469_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4471_ = v___x_4403_;
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4403_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4474_; 
if (v_isShared_4472_ == 0)
{
v___x_4474_ = v___x_4471_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4469_);
v___x_4474_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
return v___x_4474_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_suggestInvariant_0interp(lean_interpreter_value* stack)
{
lean_object* v_vcs_4392_ = stack[0].m_obj;
lean_object* v_inv_4393_ = stack[1].m_obj;
lean_object* v_a_4394_ = stack[2].m_obj;
lean_object* v_a_4395_ = stack[3].m_obj;
lean_object* v_a_4396_ = stack[4].m_obj;
lean_object* v_a_4397_ = stack[5].m_obj;
lean_object* v_a_4398_ = stack[6].m_obj;
lean_object* v_a_4399_ = stack[7].m_obj;
lean_object* v_a_4400_ = stack[8].m_obj;
lean_object* v_a_4401_ = stack[9].m_obj;
lean_object* v_res_4477_;
v_res_4477_ = l_Lean_Elab_Tactic_Do_suggestInvariant(v_vcs_4392_, v_inv_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
stack->m_obj
 = v_res_4477_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___boxed(lean_object* v_vcs_4478_, lean_object* v_inv_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l_Lean_Elab_Tactic_Do_suggestInvariant(v_vcs_4478_, v_inv_4479_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_);
lean_dec(v_a_4487_);
lean_dec_ref(v_a_4486_);
lean_dec(v_a_4485_);
lean_dec_ref(v_a_4484_);
lean_dec(v_a_4483_);
lean_dec_ref(v_a_4482_);
lean_dec(v_a_4481_);
lean_dec_ref(v_a_4480_);
lean_dec_ref(v_vcs_4478_);
return v_res_4489_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(lean_object* v_00_u03b1_4490_, lean_object* v_msg_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_){
_start:
{
lean_object* v___x_4501_; 
v___x_4501_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4491_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4501_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4491_ = stack[1].m_obj;
lean_object* v___y_4492_ = stack[2].m_obj;
lean_object* v___y_4493_ = stack[3].m_obj;
lean_object* v___y_4494_ = stack[4].m_obj;
lean_object* v___y_4495_ = stack[5].m_obj;
lean_object* v___y_4496_ = stack[6].m_obj;
lean_object* v___y_4497_ = stack[7].m_obj;
lean_object* v___y_4498_ = stack[8].m_obj;
lean_object* v___y_4499_ = stack[9].m_obj;
lean_object* v_res_4502_;
v_res_4502_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(lean_box(0), v_msg_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
stack->m_obj
 = v_res_4502_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___boxed(lean_object* v_00_u03b1_4503_, lean_object* v_msg_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
lean_object* v_res_4514_; 
v_res_4514_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(v_00_u03b1_4503_, v_msg_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_);
lean_dec(v___y_4512_);
lean_dec_ref(v___y_4511_);
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
lean_dec(v___y_4506_);
lean_dec_ref(v___y_4505_);
return v_res_4514_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(lean_object* v_00_u03b1_4515_, lean_object* v_name_4516_, uint8_t v_bi_4517_, lean_object* v_type_4518_, lean_object* v_k_4519_, uint8_t v_kind_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
lean_object* v___x_4530_; 
v___x_4530_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_4516_, v_bi_4517_, v_type_4518_, v_k_4519_, v_kind_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
return v___x_4530_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_4516_ = stack[1].m_obj;
uint8_t v_bi_4517_ = stack[2].m_num;
lean_object* v_type_4518_ = stack[3].m_obj;
lean_object* v_k_4519_ = stack[4].m_obj;
uint8_t v_kind_4520_ = stack[5].m_num;
lean_object* v___y_4521_ = stack[6].m_obj;
lean_object* v___y_4522_ = stack[7].m_obj;
lean_object* v___y_4523_ = stack[8].m_obj;
lean_object* v___y_4524_ = stack[9].m_obj;
lean_object* v___y_4525_ = stack[10].m_obj;
lean_object* v___y_4526_ = stack[11].m_obj;
lean_object* v___y_4527_ = stack[12].m_obj;
lean_object* v___y_4528_ = stack[13].m_obj;
lean_object* v_res_4531_;
v_res_4531_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(lean_box(0), v_name_4516_, v_bi_4517_, v_type_4518_, v_k_4519_, v_kind_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
stack->m_obj
 = v_res_4531_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4532_, lean_object* v_name_4533_, lean_object* v_bi_4534_, lean_object* v_type_4535_, lean_object* v_k_4536_, lean_object* v_kind_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_){
_start:
{
uint8_t v_bi_boxed_4547_; uint8_t v_kind_boxed_4548_; lean_object* v_res_4549_; 
v_bi_boxed_4547_ = lean_unbox(v_bi_4534_);
v_kind_boxed_4548_ = lean_unbox(v_kind_4537_);
v_res_4549_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(v_00_u03b1_4532_, v_name_4533_, v_bi_boxed_4547_, v_type_4535_, v_k_4536_, v_kind_boxed_4548_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
return v_res_4549_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(lean_object* v_00_u03b1_4550_, lean_object* v_name_4551_, lean_object* v_type_4552_, lean_object* v_k_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
lean_object* v___x_4563_; 
v___x_4563_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_4551_, v_type_4552_, v_k_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
return v___x_4563_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_4551_ = stack[1].m_obj;
lean_object* v_type_4552_ = stack[2].m_obj;
lean_object* v_k_4553_ = stack[3].m_obj;
lean_object* v___y_4554_ = stack[4].m_obj;
lean_object* v___y_4555_ = stack[5].m_obj;
lean_object* v___y_4556_ = stack[6].m_obj;
lean_object* v___y_4557_ = stack[7].m_obj;
lean_object* v___y_4558_ = stack[8].m_obj;
lean_object* v___y_4559_ = stack[9].m_obj;
lean_object* v___y_4560_ = stack[10].m_obj;
lean_object* v___y_4561_ = stack[11].m_obj;
lean_object* v_res_4564_;
v_res_4564_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(lean_box(0), v_name_4551_, v_type_4552_, v_k_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
stack->m_obj
 = v_res_4564_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___boxed(lean_object* v_00_u03b1_4565_, lean_object* v_name_4566_, lean_object* v_type_4567_, lean_object* v_k_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
lean_object* v_res_4578_; 
v_res_4578_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(v_00_u03b1_4565_, v_name_4566_, v_type_4567_, v_k_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_);
lean_dec(v___y_4576_);
lean_dec_ref(v___y_4575_);
lean_dec(v___y_4574_);
lean_dec_ref(v___y_4573_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
return v_res_4578_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(lean_object* v_as_4579_, size_t v_sz_4580_, size_t v_i_4581_, lean_object* v_b_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_){
_start:
{
lean_object* v___x_4592_; 
v___x_4592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_4579_, v_sz_4580_, v_i_4581_, v_b_4582_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_);
return v___x_4592_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4579_ = stack[0].m_obj;
size_t v_sz_4580_ = stack[1].m_num;
size_t v_i_4581_ = stack[2].m_num;
lean_object* v_b_4582_ = stack[3].m_obj;
lean_object* v___y_4583_ = stack[4].m_obj;
lean_object* v___y_4584_ = stack[5].m_obj;
lean_object* v___y_4585_ = stack[6].m_obj;
lean_object* v___y_4586_ = stack[7].m_obj;
lean_object* v___y_4587_ = stack[8].m_obj;
lean_object* v___y_4588_ = stack[9].m_obj;
lean_object* v___y_4589_ = stack[10].m_obj;
lean_object* v___y_4590_ = stack[11].m_obj;
lean_object* v_res_4593_;
v_res_4593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(v_as_4579_, v_sz_4580_, v_i_4581_, v_b_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_);
stack->m_obj
 = v_res_4593_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___boxed(lean_object* v_as_4594_, lean_object* v_sz_4595_, lean_object* v_i_4596_, lean_object* v_b_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_){
_start:
{
size_t v_sz_boxed_4607_; size_t v_i_boxed_4608_; lean_object* v_res_4609_; 
v_sz_boxed_4607_ = lean_unbox_usize(v_sz_4595_);
lean_dec(v_sz_4595_);
v_i_boxed_4608_ = lean_unbox_usize(v_i_4596_);
lean_dec(v_i_4596_);
v_res_4609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(v_as_4594_, v_sz_boxed_4607_, v_i_boxed_4608_, v_b_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_);
lean_dec(v___y_4605_);
lean_dec_ref(v___y_4604_);
lean_dec(v___y_4603_);
lean_dec_ref(v___y_4602_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
lean_dec(v___y_4599_);
lean_dec_ref(v___y_4598_);
lean_dec_ref(v_as_4594_);
return v_res_4609_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(lean_object* v_as_4610_, size_t v_sz_4611_, size_t v_i_4612_, lean_object* v_b_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_){
_start:
{
lean_object* v___x_4623_; 
v___x_4623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_4610_, v_sz_4611_, v_i_4612_, v_b_4613_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_);
return v___x_4623_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4610_ = stack[0].m_obj;
size_t v_sz_4611_ = stack[1].m_num;
size_t v_i_4612_ = stack[2].m_num;
lean_object* v_b_4613_ = stack[3].m_obj;
lean_object* v___y_4614_ = stack[4].m_obj;
lean_object* v___y_4615_ = stack[5].m_obj;
lean_object* v___y_4616_ = stack[6].m_obj;
lean_object* v___y_4617_ = stack[7].m_obj;
lean_object* v___y_4618_ = stack[8].m_obj;
lean_object* v___y_4619_ = stack[9].m_obj;
lean_object* v___y_4620_ = stack[10].m_obj;
lean_object* v___y_4621_ = stack[11].m_obj;
lean_object* v_res_4624_;
v_res_4624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(v_as_4610_, v_sz_4611_, v_i_4612_, v_b_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_);
stack->m_obj
 = v_res_4624_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___boxed(lean_object* v_as_4625_, lean_object* v_sz_4626_, lean_object* v_i_4627_, lean_object* v_b_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_){
_start:
{
size_t v_sz_boxed_4638_; size_t v_i_boxed_4639_; lean_object* v_res_4640_; 
v_sz_boxed_4638_ = lean_unbox_usize(v_sz_4626_);
lean_dec(v_sz_4626_);
v_i_boxed_4639_ = lean_unbox_usize(v_i_4627_);
lean_dec(v_i_4627_);
v_res_4640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(v_as_4625_, v_sz_boxed_4638_, v_i_boxed_4639_, v_b_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_);
lean_dec(v___y_4636_);
lean_dec_ref(v___y_4635_);
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec(v___y_4630_);
lean_dec_ref(v___y_4629_);
lean_dec_ref(v_as_4625_);
return v_res_4640_;
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
