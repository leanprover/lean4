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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorIdx___impl(lean_object* v_x_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_tag_nat(v_x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorIdx___impl___boxed(lean_object* v_x_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorIdx___impl(v_x_130_);
lean_dec(v_x_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(lean_object* v_t_132_, lean_object* v_k_133_){
_start:
{
if (lean_obj_tag(v_t_132_) == 0)
{
lean_object* v_invariantUse_134_; lean_object* v___x_135_; 
v_invariantUse_134_ = lean_ctor_get(v_t_132_, 0);
lean_inc_ref(v_invariantUse_134_);
lean_dec_ref_known(v_t_132_, 1);
v___x_135_ = lean_apply_1(v_k_133_, v_invariantUse_134_);
return v___x_135_;
}
else
{
lean_dec(v_t_132_);
return v_k_133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim(lean_object* v_motive_136_, lean_object* v_ctorIdx_137_, lean_object* v_t_138_, lean_object* v_h_139_, lean_object* v_k_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_138_, v_k_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___boxed(lean_object* v_motive_142_, lean_object* v_ctorIdx_143_, lean_object* v_t_144_, lean_object* v_h_145_, lean_object* v_k_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim(v_motive_142_, v_ctorIdx_143_, v_t_144_, v_h_145_, v_k_146_);
lean_dec(v_ctorIdx_143_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_success_elim___redArg(lean_object* v_t_148_, lean_object* v_success_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_148_, v_success_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_success_elim(lean_object* v_motive_151_, lean_object* v_t_152_, lean_object* v_h_153_, lean_object* v_success_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_152_, v_success_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_notAnInvariantUse_elim___redArg(lean_object* v_t_156_, lean_object* v_notAnInvariantUse_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_156_, v_notAnInvariantUse_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_notAnInvariantUse_elim(lean_object* v_motive_159_, lean_object* v_t_160_, lean_object* v_h_161_, lean_object* v_notAnInvariantUse_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_160_, v_notAnInvariantUse_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_unknownInvariantUse_elim___redArg(lean_object* v_t_164_, lean_object* v_unknownInvariantUse_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_164_, v_unknownInvariantUse_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_unknownInvariantUse_elim(lean_object* v_motive_167_, lean_object* v_t_168_, lean_object* v_h_169_, lean_object* v_unknownInvariantUse_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_168_, v_unknownInvariantUse_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg(lean_object* v_a_177_){
_start:
{
lean_object* v_fst_178_; lean_object* v_snd_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_204_; 
v_fst_178_ = lean_ctor_get(v_a_177_, 0);
v_snd_179_ = lean_ctor_get(v_a_177_, 1);
v_isSharedCheck_204_ = !lean_is_exclusive(v_a_177_);
if (v_isSharedCheck_204_ == 0)
{
v___x_181_ = v_a_177_;
v_isShared_182_ = v_isSharedCheck_204_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_snd_179_);
lean_inc(v_fst_178_);
lean_dec(v_a_177_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_204_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_183_ = lean_unsigned_to_nat(4u);
v___x_184_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_185_ = l_Lean_Expr_isAppOfArity(v_fst_178_, v___x_184_, v___x_183_);
if (v___x_185_ == 0)
{
lean_object* v___x_187_; 
if (v_isShared_182_ == 0)
{
v___x_187_ = v___x_181_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_fst_178_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_snd_179_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
else
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_189_ = lean_unsigned_to_nat(2u);
v___x_190_ = lean_unsigned_to_nat(3u);
v___x_191_ = l_Lean_Expr_getAppNumArgs(v_fst_178_);
v___x_192_ = lean_nat_sub(v___x_191_, v___x_189_);
v___x_193_ = lean_unsigned_to_nat(1u);
v___x_194_ = lean_nat_sub(v___x_192_, v___x_193_);
lean_dec(v___x_192_);
v___x_195_ = l_Lean_Expr_getRevArg_x21(v_fst_178_, v___x_194_);
v___x_196_ = lean_array_push(v_snd_179_, v___x_195_);
v___x_197_ = lean_nat_sub(v___x_191_, v___x_190_);
lean_dec(v___x_191_);
v___x_198_ = lean_nat_sub(v___x_197_, v___x_193_);
lean_dec(v___x_197_);
v___x_199_ = l_Lean_Expr_getRevArg_x21(v_fst_178_, v___x_198_);
lean_dec(v_fst_178_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 1, v___x_196_);
lean_ctor_set(v___x_181_, 0, v___x_199_);
v___x_201_ = v___x_181_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v___x_196_);
v___x_201_ = v_reuseFailAlloc_203_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
v_a_177_ = v___x_201_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg(lean_object* v_inv_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_snd_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_252_; 
v_snd_213_ = lean_ctor_get(v_a_212_, 1);
v_isSharedCheck_252_ = !lean_is_exclusive(v_a_212_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; 
v_unused_253_ = lean_ctor_get(v_a_212_, 0);
lean_dec(v_unused_253_);
v___x_215_ = v_a_212_;
v_isShared_216_ = v_isSharedCheck_252_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_snd_213_);
lean_dec(v_a_212_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_252_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_fst_217_; lean_object* v_snd_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_251_; 
v_fst_217_ = lean_ctor_get(v_snd_213_, 0);
v_snd_218_ = lean_ctor_get(v_snd_213_, 1);
v_isSharedCheck_251_ = !lean_is_exclusive(v_snd_213_);
if (v_isSharedCheck_251_ == 0)
{
v___x_220_ = v_snd_213_;
v_isShared_221_ = v_isSharedCheck_251_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_snd_218_);
lean_inc(v_fst_217_);
lean_dec(v_snd_213_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_251_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_222_ = lean_box(0);
lean_inc(v_inv_211_);
v___x_223_ = l_Lean_mkMVar(v_inv_211_);
v___x_224_ = lean_expr_eqv(v_fst_217_, v___x_223_);
lean_dec_ref(v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_225_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__1));
v___x_226_ = lean_unsigned_to_nat(4u);
v___x_227_ = l_Lean_Expr_isAppOfArity(v_fst_217_, v___x_225_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_230_; 
lean_dec(v_inv_211_);
v___x_228_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__2));
if (v_isShared_221_ == 0)
{
v___x_230_ = v___x_220_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_fst_217_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_snd_218_);
v___x_230_ = v_reuseFailAlloc_234_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_232_; 
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 1, v___x_230_);
lean_ctor_set(v___x_215_, 0, v___x_228_);
v___x_232_ = v___x_215_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_235_ = lean_unsigned_to_nat(1u);
v___x_236_ = lean_nat_add(v_snd_218_, v___x_235_);
lean_dec(v_snd_218_);
v___x_237_ = l_Lean_Expr_getRevArg_x21(v_fst_217_, v___x_235_);
lean_dec(v_fst_217_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v___x_236_);
lean_ctor_set(v___x_220_, 0, v___x_237_);
v___x_239_ = v___x_220_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v___x_236_);
v___x_239_ = v_reuseFailAlloc_244_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_241_; 
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 1, v___x_239_);
lean_ctor_set(v___x_215_, 0, v___x_222_);
v___x_241_ = v___x_215_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_239_);
v___x_241_ = v_reuseFailAlloc_243_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
v_a_212_ = v___x_241_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_246_; 
lean_dec(v_inv_211_);
if (v_isShared_221_ == 0)
{
v___x_246_ = v___x_220_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_fst_217_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_snd_218_);
v___x_246_ = v_reuseFailAlloc_250_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_248_; 
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 1, v___x_246_);
lean_ctor_set(v___x_215_, 0, v___x_222_);
v___x_248_ = v___x_215_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(lean_object* v_assertion_266_, lean_object* v_inv_267_){
_start:
{
lean_object* v_assertion_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v_assertion_268_ = l_Lean_Expr_consumeMData(v_assertion_266_);
v___x_269_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__1));
v___x_270_ = l_Lean_Expr_isAppOf(v_assertion_268_, v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
lean_dec_ref(v_assertion_268_);
lean_dec(v_inv_267_);
v___x_271_ = lean_box(1);
return v___x_271_;
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v_head_277_; lean_object* v_conditionIdx_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v_fst_283_; 
v___x_272_ = lean_unsigned_to_nat(2u);
v___x_273_ = l_Lean_Expr_getAppNumArgs(v_assertion_268_);
v___x_274_ = lean_nat_sub(v___x_273_, v___x_272_);
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_nat_sub(v___x_274_, v___x_275_);
lean_dec(v___x_274_);
v_head_277_ = l_Lean_Expr_getRevArg_x21(v_assertion_268_, v___x_276_);
v_conditionIdx_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = lean_box(0);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v_head_277_);
lean_ctor_set(v___x_280_, 1, v_conditionIdx_278_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_279_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg(v_inv_267_, v___x_281_);
v_fst_283_ = lean_ctor_get(v___x_282_, 0);
if (lean_obj_tag(v_fst_283_) == 0)
{
lean_object* v_snd_284_; lean_object* v_dummy_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_snd_284_ = lean_ctor_get(v___x_282_, 1);
lean_inc(v_snd_284_);
lean_dec_ref(v___x_282_);
v_dummy_285_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0);
lean_inc(v___x_273_);
v___x_286_ = lean_mk_array(v___x_273_, v_dummy_285_);
v___x_287_ = lean_nat_sub(v___x_273_, v___x_275_);
lean_dec(v___x_273_);
v___x_288_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_assertion_268_, v___x_286_, v___x_287_);
v___x_289_ = lean_array_get_size(v___x_288_);
v___x_290_ = lean_unsigned_to_nat(4u);
v___x_291_ = lean_nat_dec_lt(v___x_289_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_292_ = l_Lean_instInhabitedExpr;
v___x_293_ = lean_unsigned_to_nat(3u);
v___x_294_ = lean_array_get_borrowed(v___x_292_, v___x_288_, v___x_293_);
lean_inc(v___x_294_);
v___x_295_ = l_Lean_Expr_cleanupAnnotations(v___x_294_);
v___x_296_ = l_Lean_Expr_isApp(v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
lean_dec_ref(v___x_295_);
lean_dec_ref(v___x_288_);
lean_dec(v_snd_284_);
v___x_297_ = lean_box(2);
return v___x_297_;
}
else
{
lean_object* v_arg_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v_arg_298_ = lean_ctor_get(v___x_295_, 1);
lean_inc_ref(v_arg_298_);
v___x_299_ = l_Lean_Expr_appFnCleanup___redArg(v___x_295_);
v___x_300_ = l_Lean_Expr_isApp(v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; 
lean_dec_ref(v___x_299_);
lean_dec_ref(v_arg_298_);
lean_dec_ref(v___x_288_);
lean_dec(v_snd_284_);
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
lean_dec_ref(v_arg_298_);
lean_dec_ref(v___x_288_);
lean_dec(v_snd_284_);
v___x_305_ = lean_box(2);
return v___x_305_;
}
else
{
lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_306_ = l_Lean_Expr_appFnCleanup___redArg(v___x_303_);
v___x_307_ = l_Lean_Expr_isApp(v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; 
lean_dec_ref(v___x_306_);
lean_dec_ref(v_arg_302_);
lean_dec_ref(v_arg_298_);
lean_dec_ref(v___x_288_);
lean_dec(v_snd_284_);
v___x_308_ = lean_box(2);
return v___x_308_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_309_ = l_Lean_Expr_appFnCleanup___redArg(v___x_306_);
v___x_310_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_311_ = l_Lean_Expr_isConstOf(v___x_309_, v___x_310_);
lean_dec_ref(v___x_309_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; 
lean_dec_ref(v_arg_302_);
lean_dec_ref(v_arg_298_);
lean_dec_ref(v___x_288_);
lean_dec(v_snd_284_);
v___x_312_ = lean_box(2);
return v___x_312_;
}
else
{
lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_313_ = l_Lean_Expr_cleanupAnnotations(v_arg_302_);
v___x_314_ = l_Lean_Expr_isApp(v___x_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; 
lean_dec_ref(v___x_313_);
lean_dec_ref(v_arg_298_);
lean_dec_ref(v___x_288_);
lean_dec(v_snd_284_);
v___x_315_ = lean_box(2);
return v___x_315_;
}
else
{
lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = l_Lean_Expr_appFnCleanup___redArg(v___x_313_);
v___x_317_ = l_Lean_Expr_isApp(v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; 
lean_dec_ref(v___x_316_);
lean_dec_ref(v_arg_298_);
lean_dec_ref(v___x_288_);
lean_dec(v_snd_284_);
v___x_318_ = lean_box(2);
return v___x_318_;
}
else
{
lean_object* v_arg_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v_arg_319_ = lean_ctor_get(v___x_316_, 1);
lean_inc_ref(v_arg_319_);
v___x_320_ = l_Lean_Expr_appFnCleanup___redArg(v___x_316_);
v___x_321_ = l_Lean_Expr_isApp(v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; 
lean_dec_ref(v___x_320_);
lean_dec_ref(v_arg_319_);
lean_dec_ref(v_arg_298_);
lean_dec_ref(v___x_288_);
lean_dec(v_snd_284_);
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
lean_dec_ref(v_arg_319_);
lean_dec_ref(v_arg_298_);
lean_dec_ref(v___x_288_);
lean_dec(v_snd_284_);
v___x_326_ = lean_box(2);
return v___x_326_;
}
else
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = l_Lean_Expr_appFnCleanup___redArg(v___x_324_);
v___x_328_ = l_Lean_Expr_isApp(v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
lean_dec_ref(v___x_327_);
lean_dec_ref(v_arg_323_);
lean_dec_ref(v_arg_319_);
lean_dec_ref(v_arg_298_);
lean_dec_ref(v___x_288_);
lean_dec(v_snd_284_);
v___x_329_ = lean_box(2);
return v___x_329_;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_330_ = l_Lean_Expr_appFnCleanup___redArg(v___x_327_);
v___x_331_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__4));
v___x_332_ = l_Lean_Expr_isConstOf(v___x_330_, v___x_331_);
lean_dec_ref(v___x_330_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
lean_dec_ref(v_arg_323_);
lean_dec_ref(v_arg_319_);
lean_dec_ref(v_arg_298_);
lean_dec_ref(v___x_288_);
lean_dec(v_snd_284_);
v___x_333_ = lean_box(2);
return v___x_333_;
}
else
{
lean_object* v_snd_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_350_; 
v_snd_334_ = lean_ctor_get(v_snd_284_, 1);
v_isSharedCheck_350_ = !lean_is_exclusive(v_snd_284_);
if (v_isSharedCheck_350_ == 0)
{
lean_object* v_unused_351_; 
v_unused_351_ = lean_ctor_get(v_snd_284_, 0);
lean_dec(v_unused_351_);
v___x_336_ = v_snd_284_;
v_isShared_337_ = v_isSharedCheck_350_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_snd_334_);
lean_dec(v_snd_284_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_350_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_338_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5));
lean_inc_ref(v_arg_298_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 1, v___x_338_);
lean_ctor_set(v___x_336_, 0, v_arg_298_);
v___x_340_ = v___x_336_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_arg_298_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v___x_338_);
v___x_340_ = v_reuseFailAlloc_349_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_341_; lean_object* v_fst_342_; lean_object* v_snd_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_341_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg(v___x_340_);
v_fst_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_fst_342_);
v_snd_343_ = lean_ctor_get(v___x_341_, 1);
lean_inc(v_snd_343_);
lean_dec_ref(v___x_341_);
v___x_344_ = l_Array_toSubarray___redArg(v___x_288_, v___x_290_, v___x_289_);
v___x_345_ = lean_array_push(v_snd_343_, v_fst_342_);
v___x_346_ = l_Subarray_copy___redArg(v___x_344_);
v___x_347_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_347_, 0, v_snd_334_);
lean_ctor_set(v___x_347_, 1, v_arg_323_);
lean_ctor_set(v___x_347_, 2, v_arg_319_);
lean_ctor_set(v___x_347_, 3, v___x_345_);
lean_ctor_set(v___x_347_, 4, v_arg_298_);
lean_ctor_set(v___x_347_, 5, v___x_346_);
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
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
lean_object* v___x_352_; 
lean_dec_ref(v___x_288_);
lean_dec(v_snd_284_);
v___x_352_ = lean_box(1);
return v___x_352_;
}
}
else
{
lean_object* v_val_353_; 
lean_inc_ref(v_fst_283_);
lean_dec_ref(v___x_282_);
lean_dec(v___x_273_);
lean_dec_ref(v_assertion_268_);
v_val_353_ = lean_ctor_get(v_fst_283_, 0);
lean_inc(v_val_353_);
lean_dec_ref_known(v_fst_283_, 1);
return v_val_353_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___boxed(lean_object* v_assertion_354_, lean_object* v_inv_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_assertion_354_, v_inv_355_);
lean_dec_ref(v_assertion_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0(lean_object* v_inv_357_, lean_object* v_inst_358_, lean_object* v_a_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg(v_inv_357_, v_a_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1(lean_object* v_inst_361_, lean_object* v_a_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg(v_a_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(lean_object* v_mvarId_364_, lean_object* v_x_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_364_, v_x_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
v_a_380_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_371_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_371_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg___boxed(lean_object* v_mvarId_388_, lean_object* v_x_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_mvarId_388_, v_x_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0(lean_object* v_00_u03b1_396_, lean_object* v_mvarId_397_, lean_object* v_x_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_mvarId_397_, v_x_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___boxed(lean_object* v_00_u03b1_405_, lean_object* v_mvarId_406_, lean_object* v_x_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0(v_00_u03b1_405_, v_mvarId_406_, v_x_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(lean_object* v_e_414_, lean_object* v___y_415_){
_start:
{
uint8_t v___x_417_; 
v___x_417_ = l_Lean_Expr_hasMVar(v_e_414_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; 
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v_e_414_);
return v___x_418_;
}
else
{
lean_object* v___x_419_; lean_object* v_mctx_420_; lean_object* v___x_421_; lean_object* v_fst_422_; lean_object* v_snd_423_; lean_object* v___x_424_; lean_object* v_cache_425_; lean_object* v_zetaDeltaFVarIds_426_; lean_object* v_postponed_427_; lean_object* v_diag_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_437_; 
v___x_419_ = lean_st_ref_get(v___y_415_);
v_mctx_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc_ref(v_mctx_420_);
lean_dec(v___x_419_);
v___x_421_ = l_Lean_instantiateMVarsCore(v_mctx_420_, v_e_414_);
v_fst_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_fst_422_);
v_snd_423_ = lean_ctor_get(v___x_421_, 1);
lean_inc(v_snd_423_);
lean_dec_ref(v___x_421_);
v___x_424_ = lean_st_ref_take(v___y_415_);
v_cache_425_ = lean_ctor_get(v___x_424_, 1);
v_zetaDeltaFVarIds_426_ = lean_ctor_get(v___x_424_, 2);
v_postponed_427_ = lean_ctor_get(v___x_424_, 3);
v_diag_428_ = lean_ctor_get(v___x_424_, 4);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; 
v_unused_438_ = lean_ctor_get(v___x_424_, 0);
lean_dec(v_unused_438_);
v___x_430_ = v___x_424_;
v_isShared_431_ = v_isSharedCheck_437_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_diag_428_);
lean_inc(v_postponed_427_);
lean_inc(v_zetaDeltaFVarIds_426_);
lean_inc(v_cache_425_);
lean_dec(v___x_424_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_437_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v_snd_423_);
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_snd_423_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_cache_425_);
lean_ctor_set(v_reuseFailAlloc_436_, 2, v_zetaDeltaFVarIds_426_);
lean_ctor_set(v_reuseFailAlloc_436_, 3, v_postponed_427_);
lean_ctor_set(v_reuseFailAlloc_436_, 4, v_diag_428_);
v___x_433_ = v_reuseFailAlloc_436_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_st_ref_put(v___y_415_, v___x_433_);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v_fst_422_);
return v___x_435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg___boxed(lean_object* v_e_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_e_439_, v___y_440_);
lean_dec(v___y_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1(lean_object* v_e_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_e_443_, v___y_445_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___boxed(lean_object* v_e_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1(v_e_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(lean_object* v_inv_474_, uint8_t v___x_475_, lean_object* v_as_476_, size_t v_sz_477_, size_t v_i_478_, lean_object* v_b_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_a_486_; uint8_t v___x_490_; 
v___x_490_ = lean_usize_dec_lt(v_i_478_, v_sz_477_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; 
lean_dec(v_inv_474_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v_b_479_);
return v___x_491_;
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v_a_494_; lean_object* v_a_496_; lean_object* v___x_533_; 
lean_dec_ref(v_b_479_);
v___x_492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__0));
v___x_493_ = l_Lean_instInhabitedExpr;
v_a_494_ = lean_array_uget_borrowed(v_as_476_, v_i_478_);
lean_inc(v_a_494_);
v___x_533_ = l_Lean_MVarId_getType(v_a_494_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v___x_535_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
lean_dec_ref_known(v___x_533_, 1);
v___x_535_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_a_534_, v___y_481_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v___x_537_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
lean_dec_ref_known(v___x_535_, 1);
v___x_537_ = l_Lean_Expr_consumeMData(v_a_536_);
lean_dec(v_a_536_);
v_a_496_ = v___x_537_;
goto v___jp_495_;
}
else
{
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_538_; 
v_a_538_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_538_);
lean_dec_ref_known(v___x_535_, 1);
v_a_496_ = v_a_538_;
goto v___jp_495_;
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec(v_inv_474_);
v_a_539_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_535_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_535_);
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
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec(v_inv_474_);
v_a_547_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_533_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_533_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
v___jp_495_:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed), 6, 1);
lean_closure_set(v___x_497_, 0, v_a_496_);
lean_inc(v_a_494_);
v___x_498_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_494_, v___x_497_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_524_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_524_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_524_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_524_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
if (lean_obj_tag(v_a_499_) == 1)
{
lean_object* v_val_503_; lean_object* v_snd_504_; lean_object* v_snd_505_; lean_object* v___x_506_; 
v_val_503_ = lean_ctor_get(v_a_499_, 0);
lean_inc(v_val_503_);
lean_dec_ref_known(v_a_499_, 1);
v_snd_504_ = lean_ctor_get(v_val_503_, 1);
lean_inc(v_snd_504_);
lean_dec(v_val_503_);
v_snd_505_ = lean_ctor_get(v_snd_504_, 1);
lean_inc(v_snd_505_);
lean_dec(v_snd_504_);
lean_inc(v_inv_474_);
v___x_506_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_snd_505_, v_inv_474_);
lean_dec(v_snd_505_);
switch(lean_obj_tag(v___x_506_))
{
case 0:
{
lean_object* v_invariantUse_507_; lean_object* v_cursorSuffix_508_; lean_object* v_letMuts_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v_invariantUse_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc_ref(v_invariantUse_507_);
lean_dec_ref_known(v___x_506_, 1);
v_cursorSuffix_508_ = lean_ctor_get(v_invariantUse_507_, 2);
lean_inc_ref(v_cursorSuffix_508_);
v_letMuts_509_ = lean_ctor_get(v_invariantUse_507_, 3);
lean_inc_ref(v_letMuts_509_);
lean_dec_ref(v_invariantUse_507_);
v___x_510_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2));
v___x_511_ = l_Lean_Expr_isAppOf(v_cursorSuffix_508_, v___x_510_);
lean_dec_ref(v_cursorSuffix_508_);
if (v___x_511_ == 0)
{
if (v___x_475_ == 0)
{
lean_dec_ref(v_letMuts_509_);
lean_del_object(v___x_501_);
v_a_486_ = v___x_492_;
goto v___jp_485_;
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = lean_array_get(v___x_493_, v_letMuts_509_, v___x_512_);
lean_dec_ref(v_letMuts_509_);
v___x_514_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5));
v___x_515_ = l_Lean_Expr_isAppOf(v___x_513_, v___x_514_);
lean_dec(v___x_513_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_518_; 
lean_dec(v_inv_474_);
v___x_516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7));
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_516_);
v___x_518_ = v___x_501_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
else
{
lean_del_object(v___x_501_);
v_a_486_ = v___x_492_;
goto v___jp_485_;
}
}
}
else
{
lean_dec_ref(v_letMuts_509_);
lean_del_object(v___x_501_);
v_a_486_ = v___x_492_;
goto v___jp_485_;
}
}
case 1:
{
lean_del_object(v___x_501_);
v_a_486_ = v___x_492_;
goto v___jp_485_;
}
default: 
{
lean_object* v___x_520_; lean_object* v___x_522_; 
lean_dec(v_inv_474_);
v___x_520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7));
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_520_);
v___x_522_ = v___x_501_;
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
}
}
else
{
lean_del_object(v___x_501_);
lean_dec(v_a_499_);
v_a_486_ = v___x_492_;
goto v___jp_485_;
}
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_inv_474_);
v_a_525_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_498_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_498_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
v___jp_485_:
{
size_t v___x_487_; size_t v___x_488_; 
v___x_487_ = ((size_t)1ULL);
v___x_488_ = lean_usize_add(v_i_478_, v___x_487_);
lean_inc_ref(v_a_486_);
v_i_478_ = v___x_488_;
v_b_479_ = v_a_486_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___boxed(lean_object* v_inv_555_, lean_object* v___x_556_, lean_object* v_as_557_, lean_object* v_sz_558_, lean_object* v_i_559_, lean_object* v_b_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
uint8_t v___x_4464__boxed_566_; size_t v_sz_boxed_567_; size_t v_i_boxed_568_; lean_object* v_res_569_; 
v___x_4464__boxed_566_ = lean_unbox(v___x_556_);
v_sz_boxed_567_ = lean_unbox_usize(v_sz_558_);
lean_dec(v_sz_558_);
v_i_boxed_568_ = lean_unbox_usize(v_i_559_);
lean_dec(v_i_559_);
v_res_569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(v_inv_555_, v___x_4464__boxed_566_, v_as_557_, v_sz_boxed_567_, v_i_boxed_568_, v_b_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec_ref(v_as_557_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(lean_object* v_vcs_574_, lean_object* v_inv_575_, lean_object* v_letMutsTy_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_588_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0));
v___x_589_ = l_Lean_Expr_isAppOf(v_letMutsTy_576_, v___x_588_);
if (v___x_589_ == 0)
{
lean_dec(v_inv_575_);
goto v___jp_582_;
}
else
{
lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_590_ = l_Lean_Expr_getAppNumArgs(v_letMutsTy_576_);
v___x_591_ = lean_unsigned_to_nat(2u);
v___x_592_ = lean_nat_dec_lt(v___x_590_, v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_593_ = lean_unsigned_to_nat(1u);
v___x_594_ = lean_nat_sub(v___x_590_, v___x_593_);
lean_dec(v___x_590_);
lean_inc(v___x_594_);
v___x_595_ = l_Lean_Expr_getRevArg_x21(v_letMutsTy_576_, v___x_594_);
v___x_596_ = l_Lean_Expr_cleanupAnnotations(v___x_595_);
v___x_597_ = l_Lean_Expr_isApp(v___x_596_);
if (v___x_597_ == 0)
{
lean_dec_ref(v___x_596_);
lean_dec(v___x_594_);
lean_dec(v_inv_575_);
goto v___jp_585_;
}
else
{
lean_object* v_arg_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v_arg_598_ = lean_ctor_get(v___x_596_, 1);
lean_inc_ref(v_arg_598_);
v___x_599_ = l_Lean_Expr_appFnCleanup___redArg(v___x_596_);
v___x_600_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1));
v___x_601_ = l_Lean_Expr_isConstOf(v___x_599_, v___x_600_);
lean_dec_ref(v___x_599_);
if (v___x_601_ == 0)
{
lean_dec_ref(v_arg_598_);
lean_dec(v___x_594_);
lean_dec(v_inv_575_);
goto v___jp_585_;
}
else
{
lean_object* v___x_602_; lean_object* v_00_u03c3_603_; lean_object* v___x_604_; size_t v_sz_605_; size_t v___x_606_; lean_object* v___x_607_; 
v___x_602_ = lean_nat_sub(v___x_594_, v___x_593_);
lean_dec(v___x_594_);
v_00_u03c3_603_ = l_Lean_Expr_getRevArg_x21(v_letMutsTy_576_, v___x_602_);
v___x_604_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__0));
v_sz_605_ = lean_array_size(v_vcs_574_);
v___x_606_ = ((size_t)0ULL);
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(v_inv_575_, v___x_601_, v_vcs_574_, v_sz_605_, v___x_606_, v___x_604_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_629_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_629_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_629_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_629_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v_fst_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_627_; 
v_fst_612_ = lean_ctor_get(v_a_608_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v_a_608_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v_a_608_, 1);
lean_dec(v_unused_628_);
v___x_614_ = v_a_608_;
v_isShared_615_ = v_isSharedCheck_627_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_fst_612_);
lean_dec(v_a_608_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_627_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
if (lean_obj_tag(v_fst_612_) == 0)
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v_00_u03c3_603_);
lean_ctor_set(v___x_614_, 0, v_arg_598_);
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_arg_598_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_00_u03c3_603_);
v___x_617_ = v_reuseFailAlloc_622_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_618_);
v___x_620_ = v___x_610_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
else
{
lean_object* v_val_623_; lean_object* v___x_625_; 
lean_del_object(v___x_614_);
lean_dec_ref(v_00_u03c3_603_);
lean_dec_ref(v_arg_598_);
v_val_623_ = lean_ctor_get(v_fst_612_, 0);
lean_inc(v_val_623_);
lean_dec_ref_known(v_fst_612_, 1);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v_val_623_);
v___x_625_ = v___x_610_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_val_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec_ref(v_00_u03c3_603_);
lean_dec_ref(v_arg_598_);
v_a_630_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_607_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_607_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
}
else
{
lean_dec(v___x_590_);
lean_dec(v_inv_575_);
goto v___jp_582_;
}
}
v___jp_582_:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_box(0);
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
v___jp_585_:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_box(0);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___boxed(lean_object* v_vcs_638_, lean_object* v_inv_639_, lean_object* v_letMutsTy_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(v_vcs_638_, v_inv_639_, v_letMutsTy_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
lean_dec_ref(v_letMutsTy_640_);
lean_dec_ref(v_vcs_638_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(lean_object* v_dontRevert_647_, lean_object* v_as_648_, size_t v_i_649_, size_t v_stop_650_, lean_object* v_b_651_){
_start:
{
lean_object* v___y_653_; uint8_t v___x_657_; 
v___x_657_ = lean_usize_dec_eq(v_i_649_, v_stop_650_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_658_ = lean_array_uget_borrowed(v_as_648_, v_i_649_);
lean_inc_ref(v_dontRevert_647_);
lean_inc(v___x_658_);
v___x_659_ = lean_apply_1(v_dontRevert_647_, v___x_658_);
v___x_660_ = lean_unbox(v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
lean_inc(v___x_658_);
v___x_661_ = lean_array_push(v_b_651_, v___x_658_);
v___y_653_ = v___x_661_;
goto v___jp_652_;
}
else
{
v___y_653_ = v_b_651_;
goto v___jp_652_;
}
}
else
{
lean_dec_ref(v_dontRevert_647_);
return v_b_651_;
}
v___jp_652_:
{
size_t v___x_654_; size_t v___x_655_; 
v___x_654_ = ((size_t)1ULL);
v___x_655_ = lean_usize_add(v_i_649_, v___x_654_);
v_i_649_ = v___x_655_;
v_b_651_ = v___y_653_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2___boxed(lean_object* v_dontRevert_662_, lean_object* v_as_663_, lean_object* v_i_664_, lean_object* v_stop_665_, lean_object* v_b_666_){
_start:
{
size_t v_i_boxed_667_; size_t v_stop_boxed_668_; lean_object* v_res_669_; 
v_i_boxed_667_ = lean_unbox_usize(v_i_664_);
lean_dec(v_i_664_);
v_stop_boxed_668_ = lean_unbox_usize(v_stop_665_);
lean_dec(v_stop_665_);
v_res_669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_662_, v_as_663_, v_i_boxed_667_, v_stop_boxed_668_, v_b_666_);
lean_dec_ref(v_as_663_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(size_t v_sz_670_, size_t v_i_671_, lean_object* v_bs_672_){
_start:
{
uint8_t v___x_673_; 
v___x_673_ = lean_usize_dec_lt(v_i_671_, v_sz_670_);
if (v___x_673_ == 0)
{
return v_bs_672_;
}
else
{
lean_object* v_v_674_; lean_object* v___x_675_; lean_object* v_bs_x27_676_; lean_object* v___x_677_; size_t v___x_678_; size_t v___x_679_; lean_object* v___x_680_; 
v_v_674_ = lean_array_uget(v_bs_672_, v_i_671_);
v___x_675_ = lean_unsigned_to_nat(0u);
v_bs_x27_676_ = lean_array_uset(v_bs_672_, v_i_671_, v___x_675_);
v___x_677_ = l_Lean_mkFVar(v_v_674_);
v___x_678_ = ((size_t)1ULL);
v___x_679_ = lean_usize_add(v_i_671_, v___x_678_);
v___x_680_ = lean_array_uset(v_bs_x27_676_, v_i_671_, v___x_677_);
v_i_671_ = v___x_679_;
v_bs_672_ = v___x_680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1___boxed(lean_object* v_sz_682_, lean_object* v_i_683_, lean_object* v_bs_684_){
_start:
{
size_t v_sz_boxed_685_; size_t v_i_boxed_686_; lean_object* v_res_687_; 
v_sz_boxed_685_ = lean_unbox_usize(v_sz_682_);
lean_dec(v_sz_682_);
v_i_boxed_686_ = lean_unbox_usize(v_i_683_);
lean_dec(v_i_683_);
v_res_687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_boxed_685_, v_i_boxed_686_, v_bs_684_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(size_t v_sz_688_, size_t v_i_689_, lean_object* v_bs_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
uint8_t v___x_696_; 
v___x_696_ = lean_usize_dec_lt(v_i_689_, v_sz_688_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; 
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v_bs_690_);
return v___x_697_;
}
else
{
lean_object* v_v_698_; lean_object* v___x_699_; lean_object* v_bs_x27_700_; lean_object* v___x_701_; 
v_v_698_ = lean_array_uget(v_bs_690_, v_i_689_);
v___x_699_ = lean_unsigned_to_nat(0u);
v_bs_x27_700_ = lean_array_uset(v_bs_690_, v_i_689_, v___x_699_);
lean_inc(v___y_694_);
lean_inc_ref(v___y_693_);
lean_inc(v___y_692_);
lean_inc_ref(v___y_691_);
v___x_701_ = lean_infer_type(v_v_698_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; size_t v___x_703_; size_t v___x_704_; lean_object* v___x_705_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v___x_701_, 1);
v___x_703_ = ((size_t)1ULL);
v___x_704_ = lean_usize_add(v_i_689_, v___x_703_);
v___x_705_ = lean_array_uset(v_bs_x27_700_, v_i_689_, v_a_702_);
v_i_689_ = v___x_704_;
v_bs_690_ = v___x_705_;
goto _start;
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec_ref(v_bs_x27_700_);
v_a_707_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_701_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_701_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0___boxed(lean_object* v_sz_715_, lean_object* v_i_716_, lean_object* v_bs_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
size_t v_sz_boxed_723_; size_t v_i_boxed_724_; lean_object* v_res_725_; 
v_sz_boxed_723_ = lean_unbox_usize(v_sz_715_);
lean_dec(v_sz_715_);
v_i_boxed_724_ = lean_unbox_usize(v_i_716_);
lean_dec(v_i_716_);
v_res_725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(v_sz_boxed_723_, v_i_boxed_724_, v_bs_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(lean_object* v_dontRevert_726_, lean_object* v_as_727_, size_t v_i_728_, size_t v_stop_729_, lean_object* v_b_730_){
_start:
{
lean_object* v___y_732_; uint8_t v___x_736_; 
v___x_736_ = lean_usize_dec_eq(v_i_728_, v_stop_729_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_737_ = lean_array_uget_borrowed(v_as_727_, v_i_728_);
v___x_738_ = l_Lean_Expr_fvarId_x21(v___x_737_);
lean_inc_ref(v_dontRevert_726_);
v___x_739_ = lean_apply_1(v_dontRevert_726_, v___x_738_);
v___x_740_ = lean_unbox(v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
lean_inc(v___x_737_);
v___x_741_ = lean_array_push(v_b_730_, v___x_737_);
v___y_732_ = v___x_741_;
goto v___jp_731_;
}
else
{
v___y_732_ = v_b_730_;
goto v___jp_731_;
}
}
else
{
lean_dec_ref(v_dontRevert_726_);
return v_b_730_;
}
v___jp_731_:
{
size_t v___x_733_; size_t v___x_734_; 
v___x_733_ = ((size_t)1ULL);
v___x_734_ = lean_usize_add(v_i_728_, v___x_733_);
v_i_728_ = v___x_734_;
v_b_730_ = v___y_732_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5___boxed(lean_object* v_dontRevert_742_, lean_object* v_as_743_, lean_object* v_i_744_, lean_object* v_stop_745_, lean_object* v_b_746_){
_start:
{
size_t v_i_boxed_747_; size_t v_stop_boxed_748_; lean_object* v_res_749_; 
v_i_boxed_747_ = lean_unbox_usize(v_i_744_);
lean_dec(v_i_744_);
v_stop_boxed_748_ = lean_unbox_usize(v_stop_745_);
lean_dec(v_stop_745_);
v_res_749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_742_, v_as_743_, v_i_boxed_747_, v_stop_boxed_748_, v_b_746_);
lean_dec_ref(v_as_743_);
return v_res_749_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(lean_object* v_a_750_, lean_object* v_x_751_){
_start:
{
if (lean_obj_tag(v_x_751_) == 0)
{
uint8_t v___x_752_; 
v___x_752_ = 0;
return v___x_752_;
}
else
{
lean_object* v_key_753_; lean_object* v_tail_754_; uint8_t v___x_755_; 
v_key_753_ = lean_ctor_get(v_x_751_, 0);
v_tail_754_ = lean_ctor_get(v_x_751_, 2);
v___x_755_ = lean_expr_eqv(v_key_753_, v_a_750_);
if (v___x_755_ == 0)
{
v_x_751_ = v_tail_754_;
goto _start;
}
else
{
return v___x_755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_a_757_, lean_object* v_x_758_){
_start:
{
uint8_t v_res_759_; lean_object* v_r_760_; 
v_res_759_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_757_, v_x_758_);
lean_dec(v_x_758_);
lean_dec_ref(v_a_757_);
v_r_760_ = lean_box(v_res_759_);
return v_r_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(lean_object* v_x_761_, lean_object* v_x_762_){
_start:
{
if (lean_obj_tag(v_x_762_) == 0)
{
return v_x_761_;
}
else
{
lean_object* v_key_763_; lean_object* v_value_764_; lean_object* v_tail_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_788_; 
v_key_763_ = lean_ctor_get(v_x_762_, 0);
v_value_764_ = lean_ctor_get(v_x_762_, 1);
v_tail_765_ = lean_ctor_get(v_x_762_, 2);
v_isSharedCheck_788_ = !lean_is_exclusive(v_x_762_);
if (v_isSharedCheck_788_ == 0)
{
v___x_767_ = v_x_762_;
v_isShared_768_ = v_isSharedCheck_788_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_tail_765_);
lean_inc(v_value_764_);
lean_inc(v_key_763_);
lean_dec(v_x_762_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_788_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; uint64_t v___x_770_; uint64_t v___x_771_; uint64_t v___x_772_; uint64_t v_fold_773_; uint64_t v___x_774_; uint64_t v___x_775_; uint64_t v___x_776_; size_t v___x_777_; size_t v___x_778_; size_t v___x_779_; size_t v___x_780_; size_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_769_ = lean_array_get_size(v_x_761_);
v___x_770_ = l_Lean_Expr_hash(v_key_763_);
v___x_771_ = 32ULL;
v___x_772_ = lean_uint64_shift_right(v___x_770_, v___x_771_);
v_fold_773_ = lean_uint64_xor(v___x_770_, v___x_772_);
v___x_774_ = 16ULL;
v___x_775_ = lean_uint64_shift_right(v_fold_773_, v___x_774_);
v___x_776_ = lean_uint64_xor(v_fold_773_, v___x_775_);
v___x_777_ = lean_uint64_to_usize(v___x_776_);
v___x_778_ = lean_usize_of_nat(v___x_769_);
v___x_779_ = ((size_t)1ULL);
v___x_780_ = lean_usize_sub(v___x_778_, v___x_779_);
v___x_781_ = lean_usize_land(v___x_777_, v___x_780_);
v___x_782_ = lean_array_uget_borrowed(v_x_761_, v___x_781_);
lean_inc(v___x_782_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 2, v___x_782_);
v___x_784_ = v___x_767_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_key_763_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_value_764_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v___x_782_);
v___x_784_ = v_reuseFailAlloc_787_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_785_; 
v___x_785_ = lean_array_uset(v_x_761_, v___x_781_, v___x_784_);
v_x_761_ = v___x_785_;
v_x_762_ = v_tail_765_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(lean_object* v_i_789_, lean_object* v_source_790_, lean_object* v_target_791_){
_start:
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = lean_array_get_size(v_source_790_);
v___x_793_ = lean_nat_dec_lt(v_i_789_, v___x_792_);
if (v___x_793_ == 0)
{
lean_dec_ref(v_source_790_);
lean_dec(v_i_789_);
return v_target_791_;
}
else
{
lean_object* v_es_794_; lean_object* v___x_795_; lean_object* v_source_796_; lean_object* v_target_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_es_794_ = lean_array_fget(v_source_790_, v_i_789_);
v___x_795_ = lean_box(0);
v_source_796_ = lean_array_fset(v_source_790_, v_i_789_, v___x_795_);
v_target_797_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(v_target_791_, v_es_794_);
v___x_798_ = lean_unsigned_to_nat(1u);
v___x_799_ = lean_nat_add(v_i_789_, v___x_798_);
lean_dec(v_i_789_);
v_i_789_ = v___x_799_;
v_source_790_ = v_source_796_;
v_target_791_ = v_target_797_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(lean_object* v_data_801_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v_nbuckets_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_802_ = lean_array_get_size(v_data_801_);
v___x_803_ = lean_unsigned_to_nat(2u);
v_nbuckets_804_ = lean_nat_mul(v___x_802_, v___x_803_);
v___x_805_ = lean_unsigned_to_nat(0u);
v___x_806_ = lean_box(0);
v___x_807_ = lean_mk_array(v_nbuckets_804_, v___x_806_);
v___x_808_ = lean_array_propagate_mark(v_data_801_, v___x_807_);
v___x_809_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(v___x_805_, v_data_801_, v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(lean_object* v_m_810_, lean_object* v_a_811_, lean_object* v_b_812_){
_start:
{
lean_object* v_size_813_; lean_object* v_buckets_814_; lean_object* v___x_815_; uint64_t v___x_816_; uint64_t v___x_817_; uint64_t v___x_818_; uint64_t v_fold_819_; uint64_t v___x_820_; uint64_t v___x_821_; uint64_t v___x_822_; size_t v___x_823_; size_t v___x_824_; size_t v___x_825_; size_t v___x_826_; size_t v___x_827_; lean_object* v_bkt_828_; uint8_t v___x_829_; 
v_size_813_ = lean_ctor_get(v_m_810_, 0);
v_buckets_814_ = lean_ctor_get(v_m_810_, 1);
v___x_815_ = lean_array_get_size(v_buckets_814_);
v___x_816_ = l_Lean_Expr_hash(v_a_811_);
v___x_817_ = 32ULL;
v___x_818_ = lean_uint64_shift_right(v___x_816_, v___x_817_);
v_fold_819_ = lean_uint64_xor(v___x_816_, v___x_818_);
v___x_820_ = 16ULL;
v___x_821_ = lean_uint64_shift_right(v_fold_819_, v___x_820_);
v___x_822_ = lean_uint64_xor(v_fold_819_, v___x_821_);
v___x_823_ = lean_uint64_to_usize(v___x_822_);
v___x_824_ = lean_usize_of_nat(v___x_815_);
v___x_825_ = ((size_t)1ULL);
v___x_826_ = lean_usize_sub(v___x_824_, v___x_825_);
v___x_827_ = lean_usize_land(v___x_823_, v___x_826_);
v_bkt_828_ = lean_array_uget_borrowed(v_buckets_814_, v___x_827_);
v___x_829_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_811_, v_bkt_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_850_; 
lean_inc_ref(v_buckets_814_);
lean_inc(v_size_813_);
v_isSharedCheck_850_ = !lean_is_exclusive(v_m_810_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; lean_object* v_unused_852_; 
v_unused_851_ = lean_ctor_get(v_m_810_, 1);
lean_dec(v_unused_851_);
v_unused_852_ = lean_ctor_get(v_m_810_, 0);
lean_dec(v_unused_852_);
v___x_831_ = v_m_810_;
v_isShared_832_ = v_isSharedCheck_850_;
goto v_resetjp_830_;
}
else
{
lean_dec(v_m_810_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_850_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v_size_x27_834_; lean_object* v___x_835_; lean_object* v_buckets_x27_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_833_ = lean_unsigned_to_nat(1u);
v_size_x27_834_ = lean_nat_add(v_size_813_, v___x_833_);
lean_dec(v_size_813_);
lean_inc(v_bkt_828_);
v___x_835_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_835_, 0, v_a_811_);
lean_ctor_set(v___x_835_, 1, v_b_812_);
lean_ctor_set(v___x_835_, 2, v_bkt_828_);
v_buckets_x27_836_ = lean_array_uset(v_buckets_814_, v___x_827_, v___x_835_);
v___x_837_ = lean_unsigned_to_nat(4u);
v___x_838_ = lean_nat_mul(v_size_x27_834_, v___x_837_);
v___x_839_ = lean_unsigned_to_nat(3u);
v___x_840_ = lean_nat_div(v___x_838_, v___x_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_array_get_size(v_buckets_x27_836_);
v___x_842_ = lean_nat_dec_le(v___x_840_, v___x_841_);
lean_dec(v___x_840_);
if (v___x_842_ == 0)
{
lean_object* v_val_843_; lean_object* v___x_845_; 
v_val_843_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(v_buckets_x27_836_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v_val_843_);
lean_ctor_set(v___x_831_, 0, v_size_x27_834_);
v___x_845_ = v___x_831_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_size_x27_834_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_val_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
else
{
lean_object* v___x_848_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v_buckets_x27_836_);
lean_ctor_set(v___x_831_, 0, v_size_x27_834_);
v___x_848_ = v___x_831_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_size_x27_834_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_buckets_x27_836_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
else
{
lean_dec(v_b_812_);
lean_dec_ref(v_a_811_);
return v_m_810_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(lean_object* v_as_853_, size_t v_sz_854_, size_t v_i_855_, lean_object* v_b_856_){
_start:
{
uint8_t v___x_857_; 
v___x_857_ = lean_usize_dec_lt(v_i_855_, v_sz_854_);
if (v___x_857_ == 0)
{
return v_b_856_;
}
else
{
lean_object* v_a_858_; lean_object* v___x_859_; lean_object* v_r_860_; size_t v___x_861_; size_t v___x_862_; 
v_a_858_ = lean_array_uget_borrowed(v_as_853_, v_i_855_);
v___x_859_ = lean_box(0);
lean_inc(v_a_858_);
v_r_860_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v_b_856_, v_a_858_, v___x_859_);
v___x_861_ = ((size_t)1ULL);
v___x_862_ = lean_usize_add(v_i_855_, v___x_861_);
v_i_855_ = v___x_862_;
v_b_856_ = v_r_860_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4___boxed(lean_object* v_as_864_, lean_object* v_sz_865_, lean_object* v_i_866_, lean_object* v_b_867_){
_start:
{
size_t v_sz_boxed_868_; size_t v_i_boxed_869_; lean_object* v_res_870_; 
v_sz_boxed_868_ = lean_unbox_usize(v_sz_865_);
lean_dec(v_sz_865_);
v_i_boxed_869_ = lean_unbox_usize(v_i_866_);
lean_dec(v_i_866_);
v_res_870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(v_as_864_, v_sz_boxed_868_, v_i_boxed_869_, v_b_867_);
lean_dec_ref(v_as_864_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(lean_object* v_m_871_, lean_object* v_l_872_){
_start:
{
size_t v_sz_873_; size_t v___x_874_; lean_object* v___x_875_; 
v_sz_873_ = lean_array_size(v_l_872_);
v___x_874_ = ((size_t)0ULL);
v___x_875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(v_l_872_, v_sz_873_, v___x_874_, v_m_871_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3___boxed(lean_object* v_m_876_, lean_object* v_l_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(v_m_876_, v_l_877_);
lean_dec_ref(v_l_877_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(lean_object* v_as_879_, size_t v_i_880_, size_t v_stop_881_, lean_object* v_b_882_){
_start:
{
uint8_t v___x_883_; 
v___x_883_ = lean_usize_dec_eq(v_i_880_, v_stop_881_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; size_t v___x_886_; size_t v___x_887_; 
v___x_884_ = lean_array_uget_borrowed(v_as_879_, v_i_880_);
lean_inc(v___x_884_);
v___x_885_ = l_Lean_collectFVars(v_b_882_, v___x_884_);
v___x_886_ = ((size_t)1ULL);
v___x_887_ = lean_usize_add(v_i_880_, v___x_886_);
v_i_880_ = v___x_887_;
v_b_882_ = v___x_885_;
goto _start;
}
else
{
return v_b_882_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4___boxed(lean_object* v_as_889_, lean_object* v_i_890_, lean_object* v_stop_891_, lean_object* v_b_892_){
_start:
{
size_t v_i_boxed_893_; size_t v_stop_boxed_894_; lean_object* v_res_895_; 
v_i_boxed_893_ = lean_unbox_usize(v_i_890_);
lean_dec(v_i_890_);
v_stop_boxed_894_ = lean_unbox_usize(v_stop_891_);
lean_dec(v_stop_891_);
v_res_895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_as_889_, v_i_boxed_893_, v_stop_boxed_894_, v_b_892_);
lean_dec_ref(v_as_889_);
return v_res_895_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = lean_box(0);
v___x_899_ = lean_unsigned_to_nat(16u);
v___x_900_ = lean_mk_array(v___x_899_, v___x_898_);
return v___x_900_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1);
v___x_902_ = lean_unsigned_to_nat(0u);
v___x_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
lean_ctor_set(v___x_903_, 1, v___x_901_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(lean_object* v_dontRevert_904_, lean_object* v_a_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; size_t v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___x_923_; lean_object* v___x_924_; size_t v___y_926_; lean_object* v___y_927_; lean_object* v_fvarIds_928_; size_t v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; uint8_t v___x_941_; uint8_t v___x_942_; lean_object* v___x_943_; 
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_923_ = lean_box(1);
v___x_924_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_941_ = 0;
v___x_942_ = 1;
lean_inc_ref(v_a_905_);
v___x_943_ = l_Lean_Meta_collectForwardDeps(v_a_905_, v___x_941_, v___x_942_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_987_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_987_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_987_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_987_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___y_949_; lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_978_ = lean_array_get_size(v_a_944_);
v___x_979_ = lean_nat_dec_lt(v___x_911_, v___x_978_);
if (v___x_979_ == 0)
{
lean_dec(v_a_944_);
v___y_949_ = v___x_924_;
goto v___jp_948_;
}
else
{
uint8_t v___x_980_; 
v___x_980_ = lean_nat_dec_le(v___x_978_, v___x_978_);
if (v___x_980_ == 0)
{
if (v___x_979_ == 0)
{
lean_dec(v_a_944_);
v___y_949_ = v___x_924_;
goto v___jp_948_;
}
else
{
size_t v___x_981_; size_t v___x_982_; lean_object* v___x_983_; 
v___x_981_ = ((size_t)0ULL);
v___x_982_ = lean_usize_of_nat(v___x_978_);
lean_inc_ref(v_dontRevert_904_);
v___x_983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_904_, v_a_944_, v___x_981_, v___x_982_, v___x_924_);
lean_dec(v_a_944_);
v___y_949_ = v___x_983_;
goto v___jp_948_;
}
}
else
{
size_t v___x_984_; size_t v___x_985_; lean_object* v___x_986_; 
v___x_984_ = ((size_t)0ULL);
v___x_985_ = lean_usize_of_nat(v___x_978_);
lean_inc_ref(v_dontRevert_904_);
v___x_986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_904_, v_a_944_, v___x_984_, v___x_985_, v___x_924_);
lean_dec(v_a_944_);
v___y_949_ = v___x_986_;
goto v___jp_948_;
}
}
v___jp_948_:
{
lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_950_ = lean_array_get_size(v___y_949_);
v___x_951_ = lean_array_get_size(v_a_905_);
lean_dec_ref(v_a_905_);
v___x_952_ = lean_nat_dec_eq(v___x_950_, v___x_951_);
if (v___x_952_ == 0)
{
size_t v_sz_953_; size_t v___x_954_; lean_object* v___x_955_; 
lean_del_object(v___x_946_);
v_sz_953_ = lean_array_size(v___y_949_);
v___x_954_ = ((size_t)0ULL);
lean_inc_ref(v___y_949_);
v___x_955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(v_sz_953_, v___x_954_, v___y_949_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref_known(v___x_955_, 1);
v___x_957_ = lean_array_get_size(v_a_956_);
v___x_958_ = lean_nat_dec_lt(v___x_911_, v___x_957_);
if (v___x_958_ == 0)
{
lean_dec(v_a_956_);
v___y_926_ = v___x_954_;
v___y_927_ = v___y_949_;
v_fvarIds_928_ = v___x_924_;
goto v___jp_925_;
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_959_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2);
v___x_960_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(v___x_959_, v___y_949_);
v___x_961_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___x_923_);
lean_ctor_set(v___x_961_, 2, v___x_924_);
v___x_962_ = lean_nat_dec_le(v___x_957_, v___x_957_);
if (v___x_962_ == 0)
{
if (v___x_958_ == 0)
{
lean_dec_ref_known(v___x_961_, 3);
lean_dec(v_a_956_);
v___y_926_ = v___x_954_;
v___y_927_ = v___y_949_;
v_fvarIds_928_ = v___x_924_;
goto v___jp_925_;
}
else
{
size_t v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_usize_of_nat(v___x_957_);
v___x_964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_a_956_, v___x_954_, v___x_963_, v___x_961_);
lean_dec(v_a_956_);
v___y_937_ = v___x_954_;
v___y_938_ = v___y_949_;
v___y_939_ = v___x_964_;
goto v___jp_936_;
}
}
else
{
size_t v___x_965_; lean_object* v___x_966_; 
v___x_965_ = lean_usize_of_nat(v___x_957_);
v___x_966_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_a_956_, v___x_954_, v___x_965_, v___x_961_);
lean_dec(v_a_956_);
v___y_937_ = v___x_954_;
v___y_938_ = v___y_949_;
v___y_939_ = v___x_966_;
goto v___jp_936_;
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec_ref(v___y_949_);
lean_dec_ref(v_dontRevert_904_);
v_a_967_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_955_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_955_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
else
{
lean_object* v___x_976_; 
lean_dec_ref(v_dontRevert_904_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___y_949_);
v___x_976_ = v___x_946_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___y_949_);
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
}
else
{
lean_dec_ref(v_a_905_);
lean_dec_ref(v_dontRevert_904_);
return v___x_943_;
}
v___jp_912_:
{
size_t v_sz_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v_sz_916_ = lean_array_size(v___y_915_);
lean_inc_ref(v___y_915_);
v___x_917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_916_, v___y_913_, v___y_915_);
v___x_918_ = l_Array_append___redArg(v___y_914_, v___x_917_);
lean_dec_ref(v___x_917_);
v___x_919_ = lean_array_get_size(v___y_915_);
lean_dec_ref(v___y_915_);
v___x_920_ = lean_nat_dec_eq(v___x_919_, v___x_911_);
if (v___x_920_ == 0)
{
v_a_905_ = v___x_918_;
goto _start;
}
else
{
lean_object* v___x_922_; 
lean_dec_ref(v_dontRevert_904_);
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_918_);
return v___x_922_;
}
}
v___jp_925_:
{
lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_929_ = lean_array_get_size(v_fvarIds_928_);
v___x_930_ = lean_nat_dec_lt(v___x_911_, v___x_929_);
if (v___x_930_ == 0)
{
lean_dec_ref(v_fvarIds_928_);
v___y_913_ = v___y_926_;
v___y_914_ = v___y_927_;
v___y_915_ = v___x_924_;
goto v___jp_912_;
}
else
{
uint8_t v___x_931_; 
v___x_931_ = lean_nat_dec_le(v___x_929_, v___x_929_);
if (v___x_931_ == 0)
{
if (v___x_930_ == 0)
{
lean_dec_ref(v_fvarIds_928_);
v___y_913_ = v___y_926_;
v___y_914_ = v___y_927_;
v___y_915_ = v___x_924_;
goto v___jp_912_;
}
else
{
size_t v___x_932_; lean_object* v___x_933_; 
v___x_932_ = lean_usize_of_nat(v___x_929_);
lean_inc_ref(v_dontRevert_904_);
v___x_933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_904_, v_fvarIds_928_, v___y_926_, v___x_932_, v___x_924_);
lean_dec_ref(v_fvarIds_928_);
v___y_913_ = v___y_926_;
v___y_914_ = v___y_927_;
v___y_915_ = v___x_933_;
goto v___jp_912_;
}
}
else
{
size_t v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_usize_of_nat(v___x_929_);
lean_inc_ref(v_dontRevert_904_);
v___x_935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_904_, v_fvarIds_928_, v___y_926_, v___x_934_, v___x_924_);
lean_dec_ref(v_fvarIds_928_);
v___y_913_ = v___y_926_;
v___y_914_ = v___y_927_;
v___y_915_ = v___x_935_;
goto v___jp_912_;
}
}
}
v___jp_936_:
{
lean_object* v_fvarIds_940_; 
v_fvarIds_940_ = lean_ctor_get(v___y_939_, 2);
lean_inc_ref(v_fvarIds_940_);
lean_dec_ref(v___y_939_);
v___y_926_ = v___y_937_;
v___y_927_ = v___y_938_;
v_fvarIds_928_ = v_fvarIds_940_;
goto v___jp_925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___boxed(lean_object* v_dontRevert_988_, lean_object* v_a_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_988_, v_a_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
return v_res_995_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_996_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_997_ = lean_box(1);
v___x_998_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2);
v___x_999_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v___x_997_);
lean_ctor_set(v___x_999_, 2, v___x_996_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(lean_object* v_e_1000_, lean_object* v_dontRevert_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v___y_1008_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v_fvarIds_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_1015_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0);
v___x_1016_ = l_Lean_collectFVars(v___x_1015_, v_e_1000_);
v_fvarIds_1017_ = lean_ctor_get(v___x_1016_, 2);
lean_inc_ref(v_fvarIds_1017_);
lean_dec_ref(v___x_1016_);
v___x_1018_ = lean_array_get_size(v_fvarIds_1017_);
v___x_1019_ = lean_nat_dec_lt(v___x_1013_, v___x_1018_);
if (v___x_1019_ == 0)
{
lean_dec_ref(v_fvarIds_1017_);
v___y_1008_ = v___x_1014_;
goto v___jp_1007_;
}
else
{
uint8_t v___x_1020_; 
v___x_1020_ = lean_nat_dec_le(v___x_1018_, v___x_1018_);
if (v___x_1020_ == 0)
{
if (v___x_1019_ == 0)
{
lean_dec_ref(v_fvarIds_1017_);
v___y_1008_ = v___x_1014_;
goto v___jp_1007_;
}
else
{
size_t v___x_1021_; size_t v___x_1022_; lean_object* v___x_1023_; 
v___x_1021_ = ((size_t)0ULL);
v___x_1022_ = lean_usize_of_nat(v___x_1018_);
lean_inc_ref(v_dontRevert_1001_);
v___x_1023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_1001_, v_fvarIds_1017_, v___x_1021_, v___x_1022_, v___x_1014_);
lean_dec_ref(v_fvarIds_1017_);
v___y_1008_ = v___x_1023_;
goto v___jp_1007_;
}
}
else
{
size_t v___x_1024_; size_t v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = ((size_t)0ULL);
v___x_1025_ = lean_usize_of_nat(v___x_1018_);
lean_inc_ref(v_dontRevert_1001_);
v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_1001_, v_fvarIds_1017_, v___x_1024_, v___x_1025_, v___x_1014_);
lean_dec_ref(v_fvarIds_1017_);
v___y_1008_ = v___x_1026_;
goto v___jp_1007_;
}
}
v___jp_1007_:
{
size_t v_sz_1009_; size_t v___x_1010_; lean_object* v_xs_1011_; lean_object* v___x_1012_; 
v_sz_1009_ = lean_array_size(v___y_1008_);
v___x_1010_ = ((size_t)0ULL);
v_xs_1011_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_1009_, v___x_1010_, v___y_1008_);
v___x_1012_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_1001_, v_xs_1011_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_);
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___boxed(lean_object* v_e_1027_, lean_object* v_dontRevert_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1027_, v_dontRevert_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(lean_object* v_dontRevert_1035_, lean_object* v_inst_1036_, lean_object* v_a_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_1035_, v_a_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___boxed(lean_object* v_dontRevert_1044_, lean_object* v_inst_1045_, lean_object* v_a_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(v_dontRevert_1044_, v_inst_1045_, v_a_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3(lean_object* v_00_u03b2_1053_, lean_object* v_m_1054_, lean_object* v_a_1055_, lean_object* v_b_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v_m_1054_, v_a_1055_, v_b_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_1058_, lean_object* v_a_1059_, lean_object* v_x_1060_){
_start:
{
uint8_t v___x_1061_; 
v___x_1061_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_1059_, v_x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1062_, lean_object* v_a_1063_, lean_object* v_x_1064_){
_start:
{
uint8_t v_res_1065_; lean_object* v_r_1066_; 
v_res_1065_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(v_00_u03b2_1062_, v_a_1063_, v_x_1064_);
lean_dec(v_x_1064_);
lean_dec_ref(v_a_1063_);
v_r_1066_ = lean_box(v_res_1065_);
return v_r_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5(lean_object* v_00_u03b2_1067_, lean_object* v_data_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(v_data_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_1070_, lean_object* v_i_1071_, lean_object* v_source_1072_, lean_object* v_target_1073_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(v_i_1071_, v_source_1072_, v_target_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11(lean_object* v_00_u03b2_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(v_x_1076_, v_x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(lean_object* v_a_1085_, lean_object* v___x_1086_, lean_object* v___x_1087_, lean_object* v_i_1088_, lean_object* v_a_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_zero_1095_; uint8_t v_isZero_1096_; 
v_zero_1095_ = lean_unsigned_to_nat(0u);
v_isZero_1096_ = lean_nat_dec_eq(v_i_1088_, v_zero_1095_);
if (v_isZero_1096_ == 1)
{
lean_object* v___x_1097_; 
lean_dec(v_i_1088_);
lean_dec(v___x_1087_);
lean_dec_ref(v___x_1086_);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v_a_1089_);
return v___x_1097_;
}
else
{
lean_object* v_one_1098_; lean_object* v_n_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v_one_1098_ = lean_unsigned_to_nat(1u);
v_n_1099_ = lean_nat_sub(v_i_1088_, v_one_1098_);
lean_dec(v_i_1088_);
v___x_1100_ = lean_array_fget_borrowed(v_a_1085_, v_n_1099_);
lean_inc_ref(v___x_1086_);
v___x_1101_ = l_Lean_LocalContext_getFVar_x21(v___x_1086_, v___x_1100_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_userName_1102_; lean_object* v_type_1103_; uint8_t v_bi_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v_userName_1102_ = lean_ctor_get(v___x_1101_, 2);
lean_inc(v_userName_1102_);
v_type_1103_ = lean_ctor_get(v___x_1101_, 3);
lean_inc_ref(v_type_1103_);
v_bi_1104_ = lean_ctor_get_uint8(v___x_1101_, sizeof(void*)*4);
lean_dec_ref_known(v___x_1101_, 4);
v___x_1105_ = l_Lean_Expr_headBeta(v_type_1103_);
v___x_1106_ = lean_expr_abstract_range(v___x_1105_, v_n_1099_, v_a_1085_);
lean_dec_ref(v___x_1105_);
lean_inc_ref(v___x_1106_);
v___x_1107_ = l_Lean_Meta_getLevel(v___x_1106_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
lean_dec_ref_known(v___x_1107_, 1);
v___x_1109_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_1110_ = lean_box(0);
lean_inc_n(v___x_1087_, 2);
v___x_1111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1087_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1112_, 0, v_a_1108_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = l_Lean_mkConst(v___x_1109_, v___x_1112_);
v___x_1114_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v___x_1087_);
lean_inc_ref(v___x_1106_);
v___x_1115_ = l_Lean_mkLambda(v_userName_1102_, v_bi_1104_, v___x_1106_, v_a_1089_);
v___x_1116_ = l_Lean_mkApp3(v___x_1113_, v___x_1106_, v___x_1114_, v___x_1115_);
v_i_1088_ = v_n_1099_;
v_a_1089_ = v___x_1116_;
goto _start;
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec_ref(v___x_1106_);
lean_dec(v_userName_1102_);
lean_dec(v_n_1099_);
lean_dec_ref(v_a_1089_);
lean_dec(v___x_1087_);
lean_dec_ref(v___x_1086_);
v_a_1118_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1107_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1107_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
else
{
uint8_t v_nondep_1126_; 
v_nondep_1126_ = lean_ctor_get_uint8(v___x_1101_, sizeof(void*)*5);
if (v_nondep_1126_ == 0)
{
lean_object* v_userName_1127_; lean_object* v_type_1128_; lean_object* v_value_1129_; uint8_t v___x_1130_; 
v_userName_1127_ = lean_ctor_get(v___x_1101_, 2);
lean_inc(v_userName_1127_);
v_type_1128_ = lean_ctor_get(v___x_1101_, 3);
lean_inc_ref(v_type_1128_);
v_value_1129_ = lean_ctor_get(v___x_1101_, 4);
lean_inc_ref(v_value_1129_);
lean_dec_ref_known(v___x_1101_, 5);
v___x_1130_ = lean_expr_has_loose_bvar(v_a_1089_, v_zero_1095_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; 
lean_dec_ref(v_value_1129_);
lean_dec_ref(v_type_1128_);
lean_dec(v_userName_1127_);
v___x_1131_ = lean_expr_lower_loose_bvars(v_a_1089_, v_one_1098_, v_one_1098_);
lean_dec_ref(v_a_1089_);
v_i_1088_ = v_n_1099_;
v_a_1089_ = v___x_1131_;
goto _start;
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1133_ = l_Lean_Expr_headBeta(v_type_1128_);
v___x_1134_ = lean_expr_abstract_range(v___x_1133_, v_n_1099_, v_a_1085_);
lean_dec_ref(v___x_1133_);
v___x_1135_ = lean_expr_abstract_range(v_value_1129_, v_n_1099_, v_a_1085_);
lean_dec_ref(v_value_1129_);
v___x_1136_ = l_Lean_Expr_letE___override(v_userName_1127_, v___x_1134_, v___x_1135_, v_a_1089_, v_nondep_1126_);
v_i_1088_ = v_n_1099_;
v_a_1089_ = v___x_1136_;
goto _start;
}
}
else
{
lean_object* v_userName_1138_; lean_object* v_type_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_userName_1138_ = lean_ctor_get(v___x_1101_, 2);
lean_inc(v_userName_1138_);
v_type_1139_ = lean_ctor_get(v___x_1101_, 3);
lean_inc_ref(v_type_1139_);
lean_dec_ref_known(v___x_1101_, 5);
v___x_1140_ = l_Lean_Expr_headBeta(v_type_1139_);
v___x_1141_ = lean_expr_abstract_range(v___x_1140_, v_n_1099_, v_a_1085_);
lean_dec_ref(v___x_1140_);
lean_inc_ref(v___x_1141_);
v___x_1142_ = l_Lean_Meta_getLevel(v___x_1141_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1142_, 1);
v___x_1144_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_1145_ = lean_box(0);
lean_inc_n(v___x_1087_, 2);
v___x_1146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1087_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1147_, 0, v_a_1143_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = l_Lean_mkConst(v___x_1144_, v___x_1147_);
v___x_1149_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v___x_1087_);
v___x_1150_ = 0;
lean_inc_ref(v___x_1141_);
v___x_1151_ = l_Lean_mkLambda(v_userName_1138_, v___x_1150_, v___x_1141_, v_a_1089_);
v___x_1152_ = l_Lean_mkApp3(v___x_1148_, v___x_1141_, v___x_1149_, v___x_1151_);
v_i_1088_ = v_n_1099_;
v_a_1089_ = v___x_1152_;
goto _start;
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec_ref(v___x_1141_);
lean_dec(v_userName_1138_);
lean_dec(v_n_1099_);
lean_dec_ref(v_a_1089_);
lean_dec(v___x_1087_);
lean_dec_ref(v___x_1086_);
v_a_1154_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1142_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1142_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___boxed(lean_object* v_a_1162_, lean_object* v___x_1163_, lean_object* v___x_1164_, lean_object* v_i_1165_, lean_object* v_a_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1162_, v___x_1163_, v___x_1164_, v_i_1165_, v_a_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec_ref(v_a_1162_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(lean_object* v_e_1177_, lean_object* v_dontRevert_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = lean_box(0);
lean_inc_ref(v_e_1177_);
v___x_1185_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1177_, v_dontRevert_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v_lctx_1187_; lean_object* v___x_1188_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
lean_dec_ref_known(v___x_1185_, 1);
v_lctx_1187_ = lean_ctor_get(v_a_1179_, 2);
lean_inc(v_a_1182_);
lean_inc_ref(v_a_1181_);
lean_inc(v_a_1180_);
lean_inc_ref(v_a_1179_);
lean_inc_ref(v_e_1177_);
v___x_1188_ = lean_infer_type(v_e_1177_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1210_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1191_ = v___x_1188_;
v_isShared_1192_ = v_isSharedCheck_1210_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1188_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1210_;
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
lean_ctor_set(v___x_1191_, 0, v_e_1177_);
v___x_1196_ = v___x_1191_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_e_1177_);
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
lean_ctor_set(v___x_1191_, 0, v_e_1177_);
v___x_1202_ = v___x_1191_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_e_1177_);
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
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_del_object(v___x_1191_);
v___x_1204_ = l_Lean_Expr_constLevels_x21(v___x_1198_);
lean_dec_ref(v___x_1198_);
v___x_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = l_List_get_x21Internal___redArg(v___x_1184_, v___x_1204_, v___x_1205_);
lean_dec(v___x_1204_);
v___x_1207_ = lean_array_get_size(v_a_1186_);
v___x_1208_ = lean_expr_abstract(v_e_1177_, v_a_1186_);
lean_dec_ref(v_e_1177_);
lean_inc_ref(v_lctx_1187_);
v___x_1209_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1186_, v_lctx_1187_, v___x_1206_, v___x_1207_, v___x_1208_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_);
lean_dec(v_a_1186_);
return v___x_1209_;
}
}
}
}
else
{
lean_dec(v_a_1186_);
lean_dec_ref(v_e_1177_);
return v___x_1188_;
}
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec_ref(v_e_1177_);
v_a_1211_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1185_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1185_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed(lean_object* v_e_1219_, lean_object* v_dontRevert_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(v_e_1219_, v_dontRevert_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(lean_object* v_a_1227_, lean_object* v___x_1228_, lean_object* v___x_1229_, lean_object* v_n_1230_, lean_object* v_i_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1227_, v___x_1228_, v___x_1229_, v_i_1231_, v_a_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___boxed(lean_object* v_a_1240_, lean_object* v___x_1241_, lean_object* v___x_1242_, lean_object* v_n_1243_, lean_object* v_i_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(v_a_1240_, v___x_1241_, v___x_1242_, v_n_1243_, v_i_1244_, v_a_1245_, v_a_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v_n_1243_);
lean_dec_ref(v_a_1240_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(lean_object* v_lvl_1259_, lean_object* v_lhs_1260_, lean_object* v_rhs_1261_){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1262_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
v___x_1263_ = lean_box(0);
lean_inc(v_lvl_1259_);
v___x_1264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1264_, 0, v_lvl_1259_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = l_Lean_mkConst(v___x_1262_, v___x_1264_);
v___x_1266_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_lvl_1259_);
v___x_1267_ = l_Lean_mkApp3(v___x_1265_, v___x_1266_, v_lhs_1260_, v_rhs_1261_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(lean_object* v_lvl_1274_, lean_object* v_lhs_1275_, lean_object* v_rhs_1276_){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1277_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(lean_object* v_p_1283_){
_start:
{
lean_object* v_lvl_1284_; lean_object* v_cursorPred_1285_; lean_object* v_letMutsPred_1286_; lean_object* v___x_1287_; 
v_lvl_1284_ = lean_ctor_get(v_p_1283_, 0);
lean_inc(v_lvl_1284_);
v_cursorPred_1285_ = lean_ctor_get(v_p_1283_, 1);
lean_inc_ref(v_cursorPred_1285_);
v_letMutsPred_1286_ = lean_ctor_get(v_p_1283_, 2);
lean_inc_ref(v_letMutsPred_1286_);
lean_dec_ref(v_p_1283_);
v___x_1287_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v_lvl_1284_, v_cursorPred_1285_, v_letMutsPred_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___impl(lean_object* v_x_1288_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = lean_obj_tag_nat(v_x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___impl___boxed(lean_object* v_x_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___impl(v_x_1290_);
lean_dec(v_x_1290_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(lean_object* v_t_1292_, lean_object* v_k_1293_){
_start:
{
if (lean_obj_tag(v_t_1292_) == 3)
{
lean_object* v_e_1294_; lean_object* v___x_1295_; 
v_e_1294_ = lean_ctor_get(v_t_1292_, 0);
lean_inc_ref(v_e_1294_);
lean_dec_ref_known(v_t_1292_, 1);
v___x_1295_ = lean_apply_1(v_k_1293_, v_e_1294_);
return v___x_1295_;
}
else
{
lean_dec(v_t_1292_);
return v_k_1293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(lean_object* v_motive_1296_, lean_object* v_ctorIdx_1297_, lean_object* v_t_1298_, lean_object* v_h_1299_, lean_object* v_k_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1298_, v_k_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___boxed(lean_object* v_motive_1302_, lean_object* v_ctorIdx_1303_, lean_object* v_t_1304_, lean_object* v_h_1305_, lean_object* v_k_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(v_motive_1302_, v_ctorIdx_1303_, v_t_1304_, v_h_1305_, v_k_1306_);
lean_dec(v_ctorIdx_1303_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim___redArg(lean_object* v_t_1308_, lean_object* v_punit_1309_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1308_, v_punit_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim(lean_object* v_motive_1311_, lean_object* v_t_1312_, lean_object* v_h_1313_, lean_object* v_punit_1314_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1312_, v_punit_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim___redArg(lean_object* v_t_1316_, lean_object* v_false_1317_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1316_, v_false_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim(lean_object* v_motive_1319_, lean_object* v_t_1320_, lean_object* v_h_1321_, lean_object* v_false_1322_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1320_, v_false_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim___redArg(lean_object* v_t_1324_, lean_object* v_true_1325_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1324_, v_true_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim(lean_object* v_motive_1327_, lean_object* v_t_1328_, lean_object* v_h_1329_, lean_object* v_true_1330_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1328_, v_true_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim___redArg(lean_object* v_t_1332_, lean_object* v_other_1333_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1332_, v_other_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim(lean_object* v_motive_1335_, lean_object* v_t_1336_, lean_object* v_h_1337_, lean_object* v_other_1338_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1336_, v_other_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(lean_object* v_a_1340_){
_start:
{
lean_object* v_snd_1342_; lean_object* v_fst_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1382_; 
v_snd_1342_ = lean_ctor_get(v_a_1340_, 1);
v_fst_1343_ = lean_ctor_get(v_a_1340_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_a_1340_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1345_ = v_a_1340_;
v_isShared_1346_ = v_isSharedCheck_1382_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_snd_1342_);
lean_inc(v_fst_1343_);
lean_dec(v_a_1340_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1382_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v_fst_1347_; lean_object* v_snd_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1381_; 
v_fst_1347_ = lean_ctor_get(v_snd_1342_, 0);
v_snd_1348_ = lean_ctor_get(v_snd_1342_, 1);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_snd_1342_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1350_ = v_snd_1342_;
v_isShared_1351_ = v_isSharedCheck_1381_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_snd_1348_);
lean_inc(v_fst_1347_);
lean_dec(v_snd_1342_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1381_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1352_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_1353_ = lean_unsigned_to_nat(4u);
v___x_1354_ = l_Lean_Expr_isAppOfArity(v_fst_1347_, v___x_1352_, v___x_1353_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1356_; 
if (v_isShared_1351_ == 0)
{
v___x_1356_ = v___x_1350_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_fst_1347_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_snd_1348_);
v___x_1356_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1358_; 
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 1, v___x_1356_);
v___x_1358_ = v___x_1345_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_fst_1343_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
return v___x_1359_;
}
}
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1362_ = lean_unsigned_to_nat(3u);
v___x_1363_ = lean_unsigned_to_nat(2u);
v___x_1364_ = l_Lean_Expr_getAppNumArgs(v_fst_1347_);
v___x_1365_ = lean_nat_sub(v___x_1364_, v___x_1363_);
v___x_1366_ = lean_unsigned_to_nat(1u);
v___x_1367_ = lean_nat_sub(v___x_1365_, v___x_1366_);
lean_dec(v___x_1365_);
v___x_1368_ = l_Lean_Expr_getRevArg_x21(v_fst_1347_, v___x_1367_);
v___x_1369_ = lean_array_push(v_snd_1348_, v___x_1368_);
v___x_1370_ = lean_nat_add(v_fst_1343_, v___x_1366_);
lean_dec(v_fst_1343_);
v___x_1371_ = lean_nat_sub(v___x_1364_, v___x_1362_);
lean_dec(v___x_1364_);
v___x_1372_ = lean_nat_sub(v___x_1371_, v___x_1366_);
lean_dec(v___x_1371_);
v___x_1373_ = l_Lean_Expr_getRevArg_x21(v_fst_1347_, v___x_1372_);
lean_dec(v_fst_1347_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 1, v___x_1369_);
lean_ctor_set(v___x_1350_, 0, v___x_1373_);
v___x_1375_ = v___x_1350_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v___x_1369_);
v___x_1375_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1377_; 
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 1, v___x_1375_);
lean_ctor_set(v___x_1345_, 0, v___x_1370_);
v___x_1377_ = v___x_1345_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
v_a_1340_ = v___x_1377_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg___boxed(lean_object* v_a_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_a_1383_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(lean_object* v_fst_1386_, lean_object* v_p_1387_){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_inc(v_fst_1386_);
v___x_1388_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_1386_);
v___x_1389_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_1386_, v___x_1388_, v_p_1387_);
return v___x_1389_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(lean_object* v_letMutsTuple_1390_, lean_object* v___x_1391_, uint8_t v___x_1392_, lean_object* v_fvarId_1393_){
_start:
{
lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1394_ = l_Lean_Expr_fvarId_x21(v_letMutsTuple_1390_);
v___x_1395_ = l_Lean_instBEqFVarId_beq(v_fvarId_1393_, v___x_1394_);
lean_dec(v___x_1394_);
if (v___x_1395_ == 0)
{
uint8_t v___x_1396_; 
v___x_1396_ = l_Lean_LocalContext_contains(v___x_1391_, v_fvarId_1393_);
return v___x_1396_;
}
else
{
return v___x_1392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0___boxed(lean_object* v_letMutsTuple_1397_, lean_object* v___x_1398_, lean_object* v___x_1399_, lean_object* v_fvarId_1400_){
_start:
{
uint8_t v___x_9660__boxed_1401_; uint8_t v_res_1402_; lean_object* v_r_1403_; 
v___x_9660__boxed_1401_ = lean_unbox(v___x_1399_);
v_res_1402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(v_letMutsTuple_1397_, v___x_1398_, v___x_9660__boxed_1401_, v_fvarId_1400_);
lean_dec(v_fvarId_1400_);
lean_dec_ref(v___x_1398_);
lean_dec_ref(v_letMutsTuple_1397_);
v_r_1403_ = lean_box(v_res_1402_);
return v_r_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(lean_object* v_inv_1423_, lean_object* v___x_1424_, lean_object* v_xs_1425_, lean_object* v_letMuts_1426_, lean_object* v_as_1427_, size_t v_sz_1428_, size_t v_i_1429_, lean_object* v_b_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_a_1437_; uint8_t v___x_1441_; 
v___x_1441_ = lean_usize_dec_lt(v_i_1429_, v_sz_1428_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; 
lean_dec_ref(v_letMuts_1426_);
lean_dec_ref(v_xs_1425_);
lean_dec_ref(v___x_1424_);
lean_dec(v_inv_1423_);
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_b_1430_);
return v___x_1442_;
}
else
{
lean_object* v_snd_1443_; lean_object* v_fst_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1789_; 
v_snd_1443_ = lean_ctor_get(v_b_1430_, 1);
v_fst_1444_ = lean_ctor_get(v_b_1430_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_b_1430_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1446_ = v_b_1430_;
v_isShared_1447_ = v_isSharedCheck_1789_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_snd_1443_);
lean_inc(v_fst_1444_);
lean_dec(v_b_1430_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1789_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v_fst_1448_; lean_object* v_snd_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1788_; 
v_fst_1448_ = lean_ctor_get(v_snd_1443_, 0);
v_snd_1449_ = lean_ctor_get(v_snd_1443_, 1);
v_isSharedCheck_1788_ = !lean_is_exclusive(v_snd_1443_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1451_ = v_snd_1443_;
v_isShared_1452_ = v_isSharedCheck_1788_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_snd_1449_);
lean_inc(v_fst_1448_);
lean_dec(v_snd_1443_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1788_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; uint8_t v___y_1467_; lean_object* v___y_1567_; lean_object* v_prefixPoint_x3f_1568_; lean_object* v_suffixPoint_x3f_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v_a_1595_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v_prefixPoint_x3f_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v_a_1688_; lean_object* v_a_1693_; lean_object* v___x_1766_; 
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5));
v___x_1455_ = lean_box(0);
v_a_1595_ = lean_array_uget_borrowed(v_as_1427_, v_i_1429_);
lean_inc(v_a_1595_);
v___x_1766_ = l_Lean_MVarId_getType(v_a_1595_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1768_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1768_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_a_1767_, v___y_1432_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1770_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref_known(v___x_1768_, 1);
v___x_1770_ = l_Lean_Expr_consumeMData(v_a_1769_);
lean_dec(v_a_1769_);
v_a_1693_ = v___x_1770_;
goto v___jp_1692_;
}
else
{
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1771_; 
v_a_1771_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1768_, 1);
v_a_1693_ = v_a_1771_;
goto v___jp_1692_;
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_del_object(v___x_1451_);
lean_dec(v_snd_1449_);
lean_dec(v_fst_1448_);
lean_del_object(v___x_1446_);
lean_dec(v_fst_1444_);
lean_dec_ref(v_letMuts_1426_);
lean_dec_ref(v_xs_1425_);
lean_dec_ref(v___x_1424_);
lean_dec(v_inv_1423_);
v_a_1772_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1768_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1768_);
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
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_del_object(v___x_1451_);
lean_dec(v_snd_1449_);
lean_dec(v_fst_1448_);
lean_del_object(v___x_1446_);
lean_dec(v_fst_1444_);
lean_dec_ref(v_letMuts_1426_);
lean_dec_ref(v_xs_1425_);
lean_dec_ref(v___x_1424_);
lean_dec(v_inv_1423_);
v_a_1780_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1766_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1766_);
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
v___jp_1456_:
{
if (v___y_1467_ == 0)
{
lean_object* v___x_1469_; 
lean_dec_ref(v___y_1460_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___y_1461_);
v___x_1469_ = v___x_1451_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___y_1461_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_snd_1449_);
v___x_1469_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1471_; 
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 1, v___x_1469_);
lean_ctor_set(v___x_1446_, 0, v___y_1463_);
v___x_1471_ = v___x_1446_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___y_1463_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
v_a_1437_ = v___x_1471_;
goto v___jp_1436_;
}
}
}
else
{
lean_object* v___x_1475_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 1, v___x_1454_);
lean_ctor_set(v___x_1451_, 0, v___y_1460_);
v___x_1475_ = v___x_1451_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___y_1460_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v___x_1454_);
v___x_1475_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1477_; 
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 1, v___x_1475_);
lean_ctor_set(v___x_1446_, 0, v___x_1453_);
v___x_1477_ = v___x_1446_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1478_; 
v___x_1478_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v___x_1477_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v_snd_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1554_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v___x_1478_, 1);
v_snd_1480_ = lean_ctor_get(v_a_1479_, 1);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_a_1479_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; 
v_unused_1555_ = lean_ctor_get(v_a_1479_, 0);
lean_dec(v_unused_1555_);
v___x_1482_ = v_a_1479_;
v_isShared_1483_ = v_isSharedCheck_1554_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_snd_1480_);
lean_dec(v_a_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1554_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v_fst_1484_; lean_object* v_snd_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1553_; 
v_fst_1484_ = lean_ctor_get(v_snd_1480_, 0);
v_snd_1485_ = lean_ctor_get(v_snd_1480_, 1);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_snd_1480_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1487_ = v_snd_1480_;
v_isShared_1488_ = v_isSharedCheck_1553_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_snd_1485_);
lean_inc(v_fst_1484_);
lean_dec(v_snd_1480_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1553_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v_points_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v_points_1489_ = lean_ctor_get(v_snd_1449_, 0);
v___x_1490_ = lean_array_get_size(v_points_1489_);
v___x_1491_ = lean_array_get_size(v_snd_1485_);
v___x_1492_ = lean_nat_dec_lt(v___x_1490_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1494_; 
lean_dec(v_snd_1485_);
lean_dec(v_fst_1484_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 1, v_snd_1449_);
lean_ctor_set(v___x_1487_, 0, v___y_1461_);
v___x_1494_ = v___x_1487_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___y_1461_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_snd_1449_);
v___x_1494_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1496_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 1, v___x_1494_);
lean_ctor_set(v___x_1482_, 0, v___y_1463_);
v___x_1496_ = v___x_1482_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___y_1463_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
v_a_1437_ = v___x_1496_;
goto v___jp_1436_;
}
}
}
else
{
lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1550_; 
v_isSharedCheck_1550_ = !lean_is_exclusive(v_snd_1449_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; lean_object* v_unused_1552_; 
v_unused_1551_ = lean_ctor_get(v_snd_1449_, 1);
lean_dec(v_unused_1551_);
v_unused_1552_ = lean_ctor_get(v_snd_1449_, 0);
lean_dec(v_unused_1552_);
v___x_1500_ = v_snd_1449_;
v_isShared_1501_ = v_isSharedCheck_1550_;
goto v_resetjp_1499_;
}
else
{
lean_dec(v_snd_1449_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1550_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1502_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__2));
v___x_1503_ = l_Lean_Expr_isConstOf(v_fst_1484_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; 
v___x_1504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__3));
lean_inc_ref(v___y_1462_);
lean_inc_ref(v___y_1465_);
lean_inc_ref(v___y_1457_);
v___x_1505_ = l_Lean_Name_mkStr4(v___y_1457_, v___y_1465_, v___y_1462_, v___x_1504_);
v___x_1506_ = lean_unsigned_to_nat(1u);
v___x_1507_ = l_Lean_Expr_isAppOfArity(v_fst_1484_, v___x_1505_, v___x_1506_);
lean_dec(v___x_1505_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; 
v___x_1508_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4));
lean_inc_ref(v___y_1462_);
lean_inc_ref(v___y_1465_);
lean_inc_ref(v___y_1457_);
v___x_1509_ = l_Lean_Name_mkStr4(v___y_1457_, v___y_1465_, v___y_1462_, v___x_1508_);
v___x_1510_ = l_Lean_Expr_isAppOfArity(v_fst_1484_, v___x_1509_, v___x_1506_);
lean_dec(v___x_1509_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1511_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1511_, 0, v_fst_1484_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v___x_1511_);
lean_ctor_set(v___x_1500_, 0, v_snd_1485_);
v___x_1513_ = v___x_1500_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_snd_1485_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1515_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 1, v___x_1513_);
lean_ctor_set(v___x_1487_, 0, v___y_1461_);
v___x_1515_ = v___x_1487_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___y_1461_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1517_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 1, v___x_1515_);
lean_ctor_set(v___x_1482_, 0, v___y_1463_);
v___x_1517_ = v___x_1482_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___y_1463_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
v_a_1437_ = v___x_1517_;
goto v___jp_1436_;
}
}
}
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1523_; 
lean_dec(v_fst_1484_);
v___x_1521_ = lean_box(2);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v___x_1521_);
lean_ctor_set(v___x_1500_, 0, v_snd_1485_);
v___x_1523_ = v___x_1500_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_snd_1485_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1525_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 1, v___x_1523_);
lean_ctor_set(v___x_1487_, 0, v___y_1461_);
v___x_1525_ = v___x_1487_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___y_1461_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1527_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 1, v___x_1525_);
lean_ctor_set(v___x_1482_, 0, v___y_1463_);
v___x_1527_ = v___x_1482_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___y_1463_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
v_a_1437_ = v___x_1527_;
goto v___jp_1436_;
}
}
}
}
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1533_; 
lean_dec(v_fst_1484_);
v___x_1531_ = lean_box(1);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v___x_1531_);
lean_ctor_set(v___x_1500_, 0, v_snd_1485_);
v___x_1533_ = v___x_1500_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_snd_1485_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1535_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 1, v___x_1533_);
lean_ctor_set(v___x_1487_, 0, v___y_1461_);
v___x_1535_ = v___x_1487_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___y_1461_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1537_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 1, v___x_1535_);
lean_ctor_set(v___x_1482_, 0, v___y_1463_);
v___x_1537_ = v___x_1482_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___y_1463_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
v_a_1437_ = v___x_1537_;
goto v___jp_1436_;
}
}
}
}
}
else
{
lean_object* v___x_1542_; 
lean_dec(v_fst_1484_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v___x_1455_);
lean_ctor_set(v___x_1500_, 0, v_snd_1485_);
v___x_1542_ = v___x_1500_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_snd_1485_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v___x_1455_);
v___x_1542_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1544_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 1, v___x_1542_);
lean_ctor_set(v___x_1487_, 0, v___y_1461_);
v___x_1544_ = v___x_1487_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___y_1461_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1546_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 1, v___x_1544_);
lean_ctor_set(v___x_1482_, 0, v___y_1463_);
v___x_1546_ = v___x_1482_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___y_1463_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
v_a_1437_ = v___x_1546_;
goto v___jp_1436_;
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
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v___y_1463_);
lean_dec(v___y_1461_);
lean_dec(v_snd_1449_);
lean_dec_ref(v_letMuts_1426_);
lean_dec_ref(v_xs_1425_);
lean_dec_ref(v___x_1424_);
lean_dec(v_inv_1423_);
v_a_1556_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1478_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1478_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
}
}
v___jp_1566_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; 
v___x_1574_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1));
v___x_1575_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3));
v___x_1576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5));
v___x_1577_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6));
v___x_1578_ = lean_unsigned_to_nat(3u);
v___x_1579_ = l_Lean_Expr_isAppOfArity(v___y_1567_, v___x_1577_, v___x_1578_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
lean_dec_ref(v___y_1567_);
lean_del_object(v___x_1451_);
lean_del_object(v___x_1446_);
v___x_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1580_, 0, v_suffixPoint_x3f_1569_);
lean_ctor_set(v___x_1580_, 1, v_snd_1449_);
v___x_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1581_, 0, v_prefixPoint_x3f_1568_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v_a_1437_ = v___x_1581_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1582_ = l_Lean_Expr_appFn_x21(v___y_1567_);
v___x_1583_ = l_Lean_Expr_appArg_x21(v___x_1582_);
lean_dec_ref(v___x_1582_);
v___x_1584_ = l_Lean_Expr_appArg_x21(v___y_1567_);
lean_dec_ref(v___y_1567_);
v___x_1585_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__1));
v___x_1586_ = l_Lean_Expr_isAppOfArity(v___x_1583_, v___x_1585_, v___x_1578_);
if (v___x_1586_ == 0)
{
lean_dec_ref(v___x_1583_);
v___y_1457_ = v___x_1574_;
v___y_1458_ = v___y_1571_;
v___y_1459_ = v___y_1573_;
v___y_1460_ = v___x_1584_;
v___y_1461_ = v_suffixPoint_x3f_1569_;
v___y_1462_ = v___x_1576_;
v___y_1463_ = v_prefixPoint_x3f_1568_;
v___y_1464_ = v___y_1572_;
v___y_1465_ = v___x_1575_;
v___y_1466_ = v___y_1570_;
v___y_1467_ = v___x_1586_;
goto v___jp_1456_;
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1587_ = lean_unsigned_to_nat(2u);
v___x_1588_ = l_Lean_Expr_getAppNumArgs(v___x_1583_);
v___x_1589_ = lean_nat_sub(v___x_1588_, v___x_1587_);
lean_dec(v___x_1588_);
v___x_1590_ = lean_unsigned_to_nat(1u);
v___x_1591_ = lean_nat_sub(v___x_1589_, v___x_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = l_Lean_Expr_getRevArg_x21(v___x_1583_, v___x_1591_);
lean_dec_ref(v___x_1583_);
lean_inc(v_inv_1423_);
v___x_1593_ = l_Lean_mkMVar(v_inv_1423_);
v___x_1594_ = lean_expr_eqv(v___x_1592_, v___x_1593_);
lean_dec_ref(v___x_1593_);
lean_dec_ref(v___x_1592_);
v___y_1457_ = v___x_1574_;
v___y_1458_ = v___y_1571_;
v___y_1459_ = v___y_1573_;
v___y_1460_ = v___x_1584_;
v___y_1461_ = v_suffixPoint_x3f_1569_;
v___y_1462_ = v___x_1576_;
v___y_1463_ = v_prefixPoint_x3f_1568_;
v___y_1464_ = v___y_1572_;
v___y_1465_ = v___x_1575_;
v___y_1466_ = v___y_1570_;
v___y_1467_ = v___x_1594_;
goto v___jp_1456_;
}
}
}
v___jp_1596_:
{
lean_object* v___x_1607_; 
lean_inc(v_inv_1423_);
v___x_1607_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v___y_1601_, v_inv_1423_);
lean_dec_ref(v___y_1601_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_invariantUse_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1680_; 
v_invariantUse_1608_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1610_ = v___x_1607_;
v_isShared_1611_ = v_isSharedCheck_1680_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_invariantUse_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1680_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v_conditionIdx_1612_; lean_object* v_cursorSuffix_1613_; lean_object* v_letMutsTuple_1614_; uint8_t v___x_1615_; 
v_conditionIdx_1612_ = lean_ctor_get(v_invariantUse_1608_, 0);
lean_inc(v_conditionIdx_1612_);
v_cursorSuffix_1613_ = lean_ctor_get(v_invariantUse_1608_, 2);
lean_inc_ref(v_cursorSuffix_1613_);
v_letMutsTuple_1614_ = lean_ctor_get(v_invariantUse_1608_, 4);
lean_inc_ref(v_letMutsTuple_1614_);
lean_dec_ref(v_invariantUse_1608_);
v___x_1615_ = lean_nat_dec_eq(v_conditionIdx_1612_, v___x_1453_);
lean_dec(v_conditionIdx_1612_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec_ref(v_letMutsTuple_1614_);
lean_dec_ref(v_cursorSuffix_1613_);
lean_del_object(v___x_1610_);
lean_dec_ref(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_del_object(v___x_1451_);
lean_del_object(v___x_1446_);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v_fst_1448_);
lean_ctor_set(v___x_1616_, 1, v_snd_1449_);
v___x_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1617_, 0, v_prefixPoint_x3f_1602_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
v_a_1437_ = v___x_1617_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2));
v___x_1619_ = l_Lean_Expr_isAppOf(v_cursorSuffix_1613_, v___x_1618_);
if (v___x_1619_ == 0)
{
lean_dec_ref(v_letMutsTuple_1614_);
lean_dec_ref(v_cursorSuffix_1613_);
lean_del_object(v___x_1610_);
lean_dec_ref(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1597_);
v___y_1567_ = v___y_1598_;
v_prefixPoint_x3f_1568_ = v_prefixPoint_x3f_1602_;
v_suffixPoint_x3f_1569_ = v_fst_1448_;
v___y_1570_ = v___y_1603_;
v___y_1571_ = v___y_1604_;
v___y_1572_ = v___y_1605_;
v___y_1573_ = v___y_1606_;
goto v___jp_1566_;
}
else
{
uint8_t v___x_1620_; 
v___x_1620_ = l_Lean_Expr_isFVar(v_letMutsTuple_1614_);
if (v___x_1620_ == 0)
{
lean_dec_ref(v_letMutsTuple_1614_);
lean_dec_ref(v_cursorSuffix_1613_);
lean_del_object(v___x_1610_);
lean_dec_ref(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1597_);
v___y_1567_ = v___y_1598_;
v_prefixPoint_x3f_1568_ = v_prefixPoint_x3f_1602_;
v_suffixPoint_x3f_1569_ = v_fst_1448_;
v___y_1570_ = v___y_1603_;
v___y_1571_ = v___y_1604_;
v___y_1572_ = v___y_1605_;
v___y_1573_ = v___y_1606_;
goto v___jp_1566_;
}
else
{
lean_object* v___x_1621_; lean_object* v___f_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1621_ = lean_box(v___x_1615_);
lean_inc_ref(v___x_1424_);
lean_inc_ref(v_letMutsTuple_1614_);
v___f_1622_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1622_, 0, v_letMutsTuple_1614_);
lean_closure_set(v___f_1622_, 1, v___x_1424_);
lean_closure_set(v___f_1622_, 2, v___x_1621_);
v___x_1623_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8));
lean_inc_ref(v_xs_1425_);
v___x_1624_ = l_Lean_Meta_mkProjection(v_xs_1425_, v___x_1623_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1626_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v___x_1626_ = l_Lean_Meta_mkEq(v_a_1625_, v_cursorSuffix_1613_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
v___x_1628_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed), 7, 2);
lean_closure_set(v___x_1628_, 0, v___y_1600_);
lean_closure_set(v___x_1628_, 1, v___f_1622_);
lean_inc(v_a_1595_);
v___x_1629_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_1595_, v___x_1628_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1631_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1629_, 1);
v___x_1631_ = l_Lean_Expr_replaceFVar(v_a_1630_, v_letMutsTuple_1614_, v_letMuts_1426_);
lean_dec(v_a_1630_);
if (lean_obj_tag(v_fst_1448_) == 1)
{
lean_object* v_val_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1650_; 
lean_dec(v_a_1627_);
lean_del_object(v___x_1610_);
lean_dec_ref(v___y_1599_);
v_val_1632_ = lean_ctor_get(v_fst_1448_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_fst_1448_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1634_ = v_fst_1448_;
v_isShared_1635_ = v_isSharedCheck_1650_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_val_1632_);
lean_dec(v_fst_1448_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1650_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v_lvl_1636_; lean_object* v_cursorPred_1637_; lean_object* v_letMutsPred_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1649_; 
v_lvl_1636_ = lean_ctor_get(v_val_1632_, 0);
v_cursorPred_1637_ = lean_ctor_get(v_val_1632_, 1);
v_letMutsPred_1638_ = lean_ctor_get(v_val_1632_, 2);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_val_1632_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1640_ = v_val_1632_;
v_isShared_1641_ = v_isSharedCheck_1649_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_letMutsPred_1638_);
lean_inc(v_cursorPred_1637_);
lean_inc(v_lvl_1636_);
lean_dec(v_val_1632_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1649_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1642_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v___y_1597_, v_letMutsPred_1638_, v___x_1631_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 2, v___x_1642_);
v___x_1644_ = v___x_1640_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_lvl_1636_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_cursorPred_1637_);
lean_ctor_set(v_reuseFailAlloc_1648_, 2, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1646_; 
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1644_);
v___x_1646_ = v___x_1634_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
v___y_1567_ = v___y_1598_;
v_prefixPoint_x3f_1568_ = v_prefixPoint_x3f_1602_;
v_suffixPoint_x3f_1569_ = v___x_1646_;
v___y_1570_ = v___y_1603_;
v___y_1571_ = v___y_1604_;
v___y_1572_ = v___y_1605_;
v___y_1573_ = v___y_1606_;
goto v___jp_1566_;
}
}
}
}
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1654_; 
lean_dec(v_fst_1448_);
v___x_1651_ = lean_apply_1(v___y_1599_, v_a_1627_);
v___x_1652_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1652_, 0, v___y_1597_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
lean_ctor_set(v___x_1652_, 2, v___x_1631_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set_tag(v___x_1610_, 1);
lean_ctor_set(v___x_1610_, 0, v___x_1652_);
v___x_1654_ = v___x_1610_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
v___y_1567_ = v___y_1598_;
v_prefixPoint_x3f_1568_ = v_prefixPoint_x3f_1602_;
v_suffixPoint_x3f_1569_ = v___x_1654_;
v___y_1570_ = v___y_1603_;
v___y_1571_ = v___y_1604_;
v___y_1572_ = v___y_1605_;
v___y_1573_ = v___y_1606_;
goto v___jp_1566_;
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec(v_a_1627_);
lean_dec_ref(v_letMutsTuple_1614_);
lean_del_object(v___x_1610_);
lean_dec(v_prefixPoint_x3f_1602_);
lean_dec_ref(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_del_object(v___x_1451_);
lean_dec(v_snd_1449_);
lean_dec(v_fst_1448_);
lean_del_object(v___x_1446_);
lean_dec_ref(v_letMuts_1426_);
lean_dec_ref(v_xs_1425_);
lean_dec_ref(v___x_1424_);
lean_dec(v_inv_1423_);
v_a_1656_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1629_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1629_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_dec_ref(v___f_1622_);
lean_dec_ref(v_letMutsTuple_1614_);
lean_del_object(v___x_1610_);
lean_dec(v_prefixPoint_x3f_1602_);
lean_dec_ref(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_del_object(v___x_1451_);
lean_dec(v_snd_1449_);
lean_dec(v_fst_1448_);
lean_del_object(v___x_1446_);
lean_dec_ref(v_letMuts_1426_);
lean_dec_ref(v_xs_1425_);
lean_dec_ref(v___x_1424_);
lean_dec(v_inv_1423_);
v_a_1664_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1626_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1626_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec_ref(v___f_1622_);
lean_dec_ref(v_letMutsTuple_1614_);
lean_dec_ref(v_cursorSuffix_1613_);
lean_del_object(v___x_1610_);
lean_dec(v_prefixPoint_x3f_1602_);
lean_dec_ref(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_del_object(v___x_1451_);
lean_dec(v_snd_1449_);
lean_dec(v_fst_1448_);
lean_del_object(v___x_1446_);
lean_dec_ref(v_letMuts_1426_);
lean_dec_ref(v_xs_1425_);
lean_dec_ref(v___x_1424_);
lean_dec(v_inv_1423_);
v_a_1672_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1624_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1624_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
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
lean_dec(v___x_1607_);
lean_dec_ref(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1597_);
v___y_1567_ = v___y_1598_;
v_prefixPoint_x3f_1568_ = v_prefixPoint_x3f_1602_;
v_suffixPoint_x3f_1569_ = v_fst_1448_;
v___y_1570_ = v___y_1603_;
v___y_1571_ = v___y_1604_;
v___y_1572_ = v___y_1605_;
v___y_1573_ = v___y_1606_;
goto v___jp_1566_;
}
}
v___jp_1681_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_inc_ref(v___y_1684_);
v___x_1689_ = lean_apply_1(v___y_1684_, v___y_1687_);
lean_inc(v___y_1682_);
v___x_1690_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1690_, 0, v___y_1682_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
lean_ctor_set(v___x_1690_, 2, v_a_1688_);
v___x_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
v___y_1597_ = v___y_1682_;
v___y_1598_ = v___y_1683_;
v___y_1599_ = v___y_1684_;
v___y_1600_ = v___y_1685_;
v___y_1601_ = v___y_1686_;
v_prefixPoint_x3f_1602_ = v___x_1691_;
v___y_1603_ = v___y_1431_;
v___y_1604_ = v___y_1432_;
v___y_1605_ = v___y_1433_;
v___y_1606_ = v___y_1434_;
goto v___jp_1596_;
}
v___jp_1692_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_inc_ref(v_a_1693_);
v___x_1694_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed), 6, 1);
lean_closure_set(v___x_1694_, 0, v_a_1693_);
lean_inc(v_a_1595_);
v___x_1695_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_1595_, v___x_1694_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v___x_1695_, 1);
if (lean_obj_tag(v_a_1696_) == 1)
{
lean_object* v_val_1697_; lean_object* v_snd_1698_; lean_object* v_fst_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1757_; 
v_val_1697_ = lean_ctor_get(v_a_1696_, 0);
lean_inc(v_val_1697_);
lean_dec_ref_known(v_a_1696_, 1);
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
lean_inc(v_inv_1423_);
v___x_1709_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_snd_1704_, v_inv_1423_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_invariantUse_1710_; lean_object* v_conditionIdx_1711_; lean_object* v_cursorPrefix_1712_; lean_object* v_letMutsTuple_1713_; uint8_t v___x_1714_; 
v_invariantUse_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc_ref(v_invariantUse_1710_);
lean_dec_ref_known(v___x_1709_, 1);
v_conditionIdx_1711_ = lean_ctor_get(v_invariantUse_1710_, 0);
lean_inc(v_conditionIdx_1711_);
v_cursorPrefix_1712_ = lean_ctor_get(v_invariantUse_1710_, 1);
lean_inc_ref(v_cursorPrefix_1712_);
v_letMutsTuple_1713_ = lean_ctor_get(v_invariantUse_1710_, 4);
lean_inc_ref(v_letMutsTuple_1713_);
lean_dec_ref(v_invariantUse_1710_);
v___x_1714_ = lean_nat_dec_eq(v_conditionIdx_1711_, v___x_1453_);
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
lean_del_object(v___x_1451_);
lean_del_object(v___x_1446_);
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 1, v_snd_1449_);
lean_ctor_set(v___x_1706_, 0, v_fst_1448_);
v___x_1716_ = v___x_1706_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_fst_1448_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_snd_1449_);
v___x_1716_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1718_; 
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 1, v___x_1716_);
lean_ctor_set(v___x_1701_, 0, v_fst_1444_);
v___x_1718_ = v___x_1701_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_fst_1444_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
v_a_1437_ = v___x_1718_;
goto v___jp_1436_;
}
}
}
else
{
lean_object* v___x_1721_; uint8_t v___x_1722_; 
lean_del_object(v___x_1706_);
lean_del_object(v___x_1701_);
v___x_1721_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2));
v___x_1722_ = l_Lean_Expr_isAppOf(v_cursorPrefix_1712_, v___x_1721_);
if (v___x_1722_ == 0)
{
lean_dec_ref(v_letMutsTuple_1713_);
lean_dec_ref(v_cursorPrefix_1712_);
v___y_1597_ = v_fst_1699_;
v___y_1598_ = v_a_1693_;
v___y_1599_ = v___f_1708_;
v___y_1600_ = v_snd_1704_;
v___y_1601_ = v_fst_1703_;
v_prefixPoint_x3f_1602_ = v_fst_1444_;
v___y_1603_ = v___y_1431_;
v___y_1604_ = v___y_1432_;
v___y_1605_ = v___y_1433_;
v___y_1606_ = v___y_1434_;
goto v___jp_1596_;
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_dec(v_fst_1444_);
v___x_1723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__10));
lean_inc_ref(v_xs_1425_);
v___x_1724_ = l_Lean_Meta_mkProjection(v_xs_1425_, v___x_1723_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1726_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1724_, 1);
v___x_1726_ = l_Lean_Meta_mkEq(v_a_1725_, v_cursorPrefix_1712_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1728_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1726_, 1);
lean_inc_ref(v_letMuts_1426_);
v___x_1728_ = l_Lean_Meta_mkEq(v_letMuts_1426_, v_letMutsTuple_1713_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1730_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref_known(v___x_1728_, 1);
lean_inc(v_fst_1699_);
v___x_1730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(v_fst_1699_, v_a_1729_);
v___y_1682_ = v_fst_1699_;
v___y_1683_ = v_a_1693_;
v___y_1684_ = v___f_1708_;
v___y_1685_ = v_snd_1704_;
v___y_1686_ = v_fst_1703_;
v___y_1687_ = v_a_1727_;
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
lean_dec_ref_known(v___x_1728_, 1);
v___y_1682_ = v_fst_1699_;
v___y_1683_ = v_a_1693_;
v___y_1684_ = v___f_1708_;
v___y_1685_ = v_snd_1704_;
v___y_1686_ = v_fst_1703_;
v___y_1687_ = v_a_1727_;
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
lean_del_object(v___x_1451_);
lean_dec(v_snd_1449_);
lean_dec(v_fst_1448_);
lean_del_object(v___x_1446_);
lean_dec_ref(v_letMuts_1426_);
lean_dec_ref(v_xs_1425_);
lean_dec_ref(v___x_1424_);
lean_dec(v_inv_1423_);
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
lean_del_object(v___x_1451_);
lean_dec(v_snd_1449_);
lean_dec(v_fst_1448_);
lean_del_object(v___x_1446_);
lean_dec_ref(v_letMuts_1426_);
lean_dec_ref(v_xs_1425_);
lean_dec_ref(v___x_1424_);
lean_dec(v_inv_1423_);
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
lean_del_object(v___x_1451_);
lean_dec(v_snd_1449_);
lean_dec(v_fst_1448_);
lean_del_object(v___x_1446_);
lean_dec_ref(v_letMuts_1426_);
lean_dec_ref(v_xs_1425_);
lean_dec_ref(v___x_1424_);
lean_dec(v_inv_1423_);
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
v___y_1597_ = v_fst_1699_;
v___y_1598_ = v_a_1693_;
v___y_1599_ = v___f_1708_;
v___y_1600_ = v_snd_1704_;
v___y_1601_ = v_fst_1703_;
v_prefixPoint_x3f_1602_ = v_fst_1444_;
v___y_1603_ = v___y_1431_;
v___y_1604_ = v___y_1432_;
v___y_1605_ = v___y_1433_;
v___y_1606_ = v___y_1434_;
goto v___jp_1596_;
}
}
}
}
else
{
lean_dec(v_a_1696_);
v___y_1567_ = v_a_1693_;
v_prefixPoint_x3f_1568_ = v_fst_1444_;
v_suffixPoint_x3f_1569_ = v_fst_1448_;
v___y_1570_ = v___y_1431_;
v___y_1571_ = v___y_1432_;
v___y_1572_ = v___y_1433_;
v___y_1573_ = v___y_1434_;
goto v___jp_1566_;
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_dec_ref(v_a_1693_);
lean_del_object(v___x_1451_);
lean_dec(v_snd_1449_);
lean_dec(v_fst_1448_);
lean_del_object(v___x_1446_);
lean_dec(v_fst_1444_);
lean_dec_ref(v_letMuts_1426_);
lean_dec_ref(v_xs_1425_);
lean_dec_ref(v___x_1424_);
lean_dec(v_inv_1423_);
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
v___jp_1436_:
{
size_t v___x_1438_; size_t v___x_1439_; 
v___x_1438_ = ((size_t)1ULL);
v___x_1439_ = lean_usize_add(v_i_1429_, v___x_1438_);
v_i_1429_ = v___x_1439_;
v_b_1430_ = v_a_1437_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___boxed(lean_object* v_inv_1790_, lean_object* v___x_1791_, lean_object* v_xs_1792_, lean_object* v_letMuts_1793_, lean_object* v_as_1794_, lean_object* v_sz_1795_, lean_object* v_i_1796_, lean_object* v_b_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
size_t v_sz_boxed_1803_; size_t v_i_boxed_1804_; lean_object* v_res_1805_; 
v_sz_boxed_1803_ = lean_unbox_usize(v_sz_1795_);
lean_dec(v_sz_1795_);
v_i_boxed_1804_ = lean_unbox_usize(v_i_1796_);
lean_dec(v_i_1796_);
v_res_1805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1790_, v___x_1791_, v_xs_1792_, v_letMuts_1793_, v_as_1794_, v_sz_boxed_1803_, v_i_boxed_1804_, v_b_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec_ref(v_as_1794_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(lean_object* v_vcs_1815_, lean_object* v_inv_1816_, lean_object* v_xs_1817_, lean_object* v_letMuts_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v_lctx_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; size_t v_sz_1827_; size_t v___x_1828_; lean_object* v___x_1829_; 
v_lctx_1824_ = lean_ctor_get(v_a_1819_, 2);
v___x_1825_ = lean_box(0);
v___x_1826_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__2));
v_sz_1827_ = lean_array_size(v_vcs_1815_);
v___x_1828_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1824_);
v___x_1829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1816_, v_lctx_1824_, v_xs_1817_, v_letMuts_1818_, v_vcs_1815_, v_sz_1827_, v___x_1828_, v___x_1826_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1873_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1832_ = v___x_1829_;
v_isShared_1833_ = v_isSharedCheck_1873_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1873_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v_snd_1838_; lean_object* v_fst_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1872_; 
v_snd_1838_ = lean_ctor_get(v_a_1830_, 1);
v_fst_1839_ = lean_ctor_get(v_a_1830_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_a_1830_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1841_ = v_a_1830_;
v_isShared_1842_ = v_isSharedCheck_1872_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_snd_1838_);
lean_inc(v_fst_1839_);
lean_dec(v_a_1830_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1872_;
goto v_resetjp_1840_;
}
v___jp_1834_:
{
lean_object* v___x_1836_; 
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1825_);
v___x_1836_ = v___x_1832_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1825_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
v_resetjp_1840_:
{
if (lean_obj_tag(v_fst_1839_) == 0)
{
lean_del_object(v___x_1841_);
lean_dec(v_snd_1838_);
goto v___jp_1834_;
}
else
{
lean_object* v_fst_1843_; 
v_fst_1843_ = lean_ctor_get(v_snd_1838_, 0);
lean_inc(v_fst_1843_);
if (lean_obj_tag(v_fst_1843_) == 0)
{
lean_dec_ref_known(v_fst_1839_, 1);
lean_del_object(v___x_1841_);
lean_dec(v_snd_1838_);
goto v___jp_1834_;
}
else
{
lean_object* v_snd_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1870_; 
lean_del_object(v___x_1832_);
v_snd_1844_ = lean_ctor_get(v_snd_1838_, 1);
v_isSharedCheck_1870_ = !lean_is_exclusive(v_snd_1838_);
if (v_isSharedCheck_1870_ == 0)
{
lean_object* v_unused_1871_; 
v_unused_1871_ = lean_ctor_get(v_snd_1838_, 0);
lean_dec(v_unused_1871_);
v___x_1846_ = v_snd_1838_;
v_isShared_1847_ = v_isSharedCheck_1870_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_snd_1844_);
lean_dec(v_snd_1838_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1870_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v_val_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1869_; 
v_val_1848_ = lean_ctor_get(v_fst_1839_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_fst_1839_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1850_ = v_fst_1839_;
v_isShared_1851_ = v_isSharedCheck_1869_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_val_1848_);
lean_dec(v_fst_1839_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1869_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v_val_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1868_; 
v_val_1852_ = lean_ctor_get(v_fst_1843_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v_fst_1843_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1854_ = v_fst_1843_;
v_isShared_1855_ = v_isSharedCheck_1868_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_val_1852_);
lean_dec(v_fst_1843_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1868_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v_val_1852_);
v___x_1857_ = v___x_1846_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_val_1852_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_snd_1844_);
v___x_1857_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1859_; 
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 1, v___x_1857_);
lean_ctor_set(v___x_1841_, 0, v_val_1848_);
v___x_1859_ = v___x_1841_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_val_1848_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1861_; 
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v___x_1859_);
v___x_1861_ = v___x_1854_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1863_; 
if (v_isShared_1851_ == 0)
{
lean_ctor_set_tag(v___x_1850_, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1861_);
v___x_1863_ = v___x_1850_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
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
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
v_a_1874_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1829_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1829_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___boxed(lean_object* v_vcs_1882_, lean_object* v_inv_1883_, lean_object* v_xs_1884_, lean_object* v_letMuts_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_vcs_1882_, v_inv_1883_, v_xs_1884_, v_letMuts_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
lean_dec(v_a_1889_);
lean_dec_ref(v_a_1888_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec_ref(v_vcs_1882_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(lean_object* v_inst_1892_, lean_object* v_a_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_a_1893_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___boxed(lean_object* v_inst_1900_, lean_object* v_a_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(v_inst_1900_, v_a_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(lean_object* v_m_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_MVarId_getDecl(v_m_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v_userName_1916_; lean_object* v_lctx_1917_; lean_object* v_type_1918_; lean_object* v_localInstances_1919_; uint8_t v_kind_1920_; lean_object* v_numScopeArgs_1921_; lean_object* v___x_1922_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref_known(v___x_1914_, 1);
v_userName_1916_ = lean_ctor_get(v_a_1915_, 0);
lean_inc(v_userName_1916_);
v_lctx_1917_ = lean_ctor_get(v_a_1915_, 1);
lean_inc_ref(v_lctx_1917_);
v_type_1918_ = lean_ctor_get(v_a_1915_, 2);
lean_inc_ref(v_type_1918_);
v_localInstances_1919_ = lean_ctor_get(v_a_1915_, 4);
lean_inc_ref(v_localInstances_1919_);
v_kind_1920_ = lean_ctor_get_uint8(v_a_1915_, sizeof(void*)*7);
v_numScopeArgs_1921_ = lean_ctor_get(v_a_1915_, 5);
lean_inc(v_numScopeArgs_1921_);
lean_dec(v_a_1915_);
v___x_1922_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_1917_, v_localInstances_1919_, v_type_1918_, v_kind_1920_, v_userName_1916_, v_numScopeArgs_1921_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1931_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1925_ = v___x_1922_;
v_isShared_1926_ = v_isSharedCheck_1931_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1922_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1931_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1927_; lean_object* v___x_1929_; 
v___x_1927_ = l_Lean_Expr_mvarId_x21(v_a_1923_);
lean_dec(v_a_1923_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 0, v___x_1927_);
v___x_1929_ = v___x_1925_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
v_a_1932_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1922_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1922_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
v_a_1940_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1914_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1914_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar___boxed(lean_object* v_m_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v_m_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__1(lean_object* v_msg_1955_){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = l_String_instInhabitedSlice;
v___x_1957_ = lean_panic_fn_borrowed(v___x_1956_, v_msg_1955_);
return v___x_1957_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(lean_object* v_s_1958_, lean_object* v_a_1959_, uint8_t v_b_1960_){
_start:
{
lean_object* v_str_1961_; lean_object* v_startInclusive_1962_; lean_object* v_endExclusive_1963_; lean_object* v___x_1964_; uint8_t v_decide_1965_; 
v_str_1961_ = lean_ctor_get(v_s_1958_, 0);
v_startInclusive_1962_ = lean_ctor_get(v_s_1958_, 1);
v_endExclusive_1963_ = lean_ctor_get(v_s_1958_, 2);
v___x_1964_ = lean_nat_sub(v_endExclusive_1963_, v_startInclusive_1962_);
v_decide_1965_ = lean_nat_dec_eq(v_a_1959_, v___x_1964_);
lean_dec(v___x_1964_);
if (v_decide_1965_ == 0)
{
uint32_t v___x_1966_; lean_object* v___x_1967_; uint32_t v___x_1968_; uint8_t v___x_1969_; 
v___x_1966_ = 64;
v___x_1967_ = lean_nat_add(v_startInclusive_1962_, v_a_1959_);
lean_dec(v_a_1959_);
v___x_1968_ = lean_string_utf8_get_fast(v_str_1961_, v___x_1967_);
v___x_1969_ = lean_uint32_dec_eq(v___x_1968_, v___x_1966_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = lean_string_utf8_next_fast(v_str_1961_, v___x_1967_);
lean_dec(v___x_1967_);
v___x_1971_ = lean_nat_sub(v___x_1970_, v_startInclusive_1962_);
v_a_1959_ = v___x_1971_;
v_b_1960_ = v___x_1969_;
goto _start;
}
else
{
lean_dec(v___x_1967_);
return v___x_1969_;
}
}
else
{
lean_dec(v_a_1959_);
return v_b_1960_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg___boxed(lean_object* v_s_1973_, lean_object* v_a_1974_, lean_object* v_b_1975_){
_start:
{
uint8_t v_b_boxed_1976_; uint8_t v_res_1977_; lean_object* v_r_1978_; 
v_b_boxed_1976_ = lean_unbox(v_b_1975_);
v_res_1977_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_1973_, v_a_1974_, v_b_boxed_1976_);
lean_dec_ref(v_s_1973_);
v_r_1978_ = lean_box(v_res_1977_);
return v_r_1978_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(lean_object* v_s_1979_){
_start:
{
lean_object* v_searcher_1980_; uint8_t v___x_1981_; uint8_t v___x_1982_; 
v_searcher_1980_ = lean_unsigned_to_nat(0u);
v___x_1981_ = 0;
v___x_1982_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_1979_, v_searcher_1980_, v___x_1981_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2___boxed(lean_object* v_s_1983_){
_start:
{
uint8_t v_res_1984_; lean_object* v_r_1985_; 
v_res_1984_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v_s_1983_);
lean_dec_ref(v_s_1983_);
v_r_1985_ = lean_box(v_res_1984_);
return v_r_1985_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1989_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__2));
v___x_1990_ = lean_unsigned_to_nat(14u);
v___x_1991_ = lean_unsigned_to_nat(22u);
v___x_1992_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__1));
v___x_1993_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__0));
v___x_1994_ = l_mkPanicMessageWithDecl(v___x_1993_, v___x_1992_, v___x_1991_, v___x_1990_, v___x_1989_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(lean_object* v_x_1995_){
_start:
{
switch(lean_obj_tag(v_x_1995_))
{
case 1:
{
lean_object* v_info_1996_; lean_object* v_kind_1997_; lean_object* v_args_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2008_; 
v_info_1996_ = lean_ctor_get(v_x_1995_, 0);
v_kind_1997_ = lean_ctor_get(v_x_1995_, 1);
v_args_1998_ = lean_ctor_get(v_x_1995_, 2);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_x_1995_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2000_ = v_x_1995_;
v_isShared_2001_ = v_isSharedCheck_2008_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_args_1998_);
lean_inc(v_kind_1997_);
lean_inc(v_info_1996_);
lean_dec(v_x_1995_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2008_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
size_t v_sz_2002_; size_t v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
v_sz_2002_ = lean_array_size(v_args_1998_);
v___x_2003_ = ((size_t)0ULL);
v___x_2004_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(v_sz_2002_, v___x_2003_, v_args_1998_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 2, v___x_2004_);
v___x_2006_ = v___x_2000_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_info_1996_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_kind_1997_);
lean_ctor_set(v_reuseFailAlloc_2007_, 2, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
case 3:
{
lean_object* v_info_2009_; lean_object* v_rawVal_2010_; lean_object* v_val_2011_; lean_object* v_preresolved_2012_; uint8_t v___y_2014_; lean_object* v_str_2027_; lean_object* v_startPos_2028_; lean_object* v_stopPos_2029_; uint8_t v___y_2031_; uint8_t v___x_2037_; 
v_info_2009_ = lean_ctor_get(v_x_1995_, 0);
v_rawVal_2010_ = lean_ctor_get(v_x_1995_, 1);
v_val_2011_ = lean_ctor_get(v_x_1995_, 2);
v_preresolved_2012_ = lean_ctor_get(v_x_1995_, 3);
v_str_2027_ = lean_ctor_get(v_rawVal_2010_, 0);
v_startPos_2028_ = lean_ctor_get(v_rawVal_2010_, 1);
v_stopPos_2029_ = lean_ctor_get(v_rawVal_2010_, 2);
v___x_2037_ = lean_string_is_valid_pos(v_str_2027_, v_startPos_2028_);
if (v___x_2037_ == 0)
{
v___y_2031_ = v___x_2037_;
goto v___jp_2030_;
}
else
{
uint8_t v___x_2038_; 
v___x_2038_ = lean_string_is_valid_pos(v_str_2027_, v_stopPos_2029_);
if (v___x_2038_ == 0)
{
v___y_2031_ = v___x_2038_;
goto v___jp_2030_;
}
else
{
uint8_t v___x_2039_; 
v___x_2039_ = lean_nat_dec_le(v_startPos_2028_, v_stopPos_2029_);
v___y_2031_ = v___x_2039_;
goto v___jp_2030_;
}
}
v___jp_2013_:
{
if (v___y_2014_ == 0)
{
lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2022_; 
lean_inc(v_preresolved_2012_);
lean_inc(v_val_2011_);
lean_inc_ref(v_rawVal_2010_);
lean_inc(v_info_2009_);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_x_1995_);
if (v_isSharedCheck_2022_ == 0)
{
lean_object* v_unused_2023_; lean_object* v_unused_2024_; lean_object* v_unused_2025_; lean_object* v_unused_2026_; 
v_unused_2023_ = lean_ctor_get(v_x_1995_, 3);
lean_dec(v_unused_2023_);
v_unused_2024_ = lean_ctor_get(v_x_1995_, 2);
lean_dec(v_unused_2024_);
v_unused_2025_ = lean_ctor_get(v_x_1995_, 1);
lean_dec(v_unused_2025_);
v_unused_2026_ = lean_ctor_get(v_x_1995_, 0);
lean_dec(v_unused_2026_);
v___x_2016_ = v_x_1995_;
v_isShared_2017_ = v_isSharedCheck_2022_;
goto v_resetjp_2015_;
}
else
{
lean_dec(v_x_1995_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2022_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___x_2018_ = l_Lean_Name_eraseMacroScopes(v_val_2011_);
lean_dec(v_val_2011_);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 2, v___x_2018_);
v___x_2020_ = v___x_2016_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_info_2009_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_rawVal_2010_);
lean_ctor_set(v_reuseFailAlloc_2021_, 2, v___x_2018_);
lean_ctor_set(v_reuseFailAlloc_2021_, 3, v_preresolved_2012_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
else
{
return v_x_1995_;
}
}
v___jp_2030_:
{
if (v___y_2031_ == 0)
{
lean_object* v___x_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2032_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3);
v___x_2033_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__1(v___x_2032_);
v___x_2034_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v___x_2033_);
lean_dec_ref(v___x_2033_);
v___y_2014_ = v___x_2034_;
goto v___jp_2013_;
}
else
{
lean_object* v___x_2035_; uint8_t v___x_2036_; 
lean_inc(v_stopPos_2029_);
lean_inc(v_startPos_2028_);
lean_inc_ref(v_str_2027_);
v___x_2035_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2035_, 0, v_str_2027_);
lean_ctor_set(v___x_2035_, 1, v_startPos_2028_);
lean_ctor_set(v___x_2035_, 2, v_stopPos_2029_);
v___x_2036_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v___x_2035_);
lean_dec_ref_known(v___x_2035_, 3);
v___y_2014_ = v___x_2036_;
goto v___jp_2013_;
}
}
}
default: 
{
return v_x_1995_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(size_t v_sz_2040_, size_t v_i_2041_, lean_object* v_bs_2042_){
_start:
{
uint8_t v___x_2043_; 
v___x_2043_ = lean_usize_dec_lt(v_i_2041_, v_sz_2040_);
if (v___x_2043_ == 0)
{
return v_bs_2042_;
}
else
{
lean_object* v_v_2044_; lean_object* v___x_2045_; lean_object* v_bs_x27_2046_; lean_object* v___x_2047_; size_t v___x_2048_; size_t v___x_2049_; lean_object* v___x_2050_; 
v_v_2044_ = lean_array_uget(v_bs_2042_, v_i_2041_);
v___x_2045_ = lean_unsigned_to_nat(0u);
v_bs_x27_2046_ = lean_array_uset(v_bs_2042_, v_i_2041_, v___x_2045_);
v___x_2047_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_v_2044_);
v___x_2048_ = ((size_t)1ULL);
v___x_2049_ = lean_usize_add(v_i_2041_, v___x_2048_);
v___x_2050_ = lean_array_uset(v_bs_x27_2046_, v_i_2041_, v___x_2047_);
v_i_2041_ = v___x_2049_;
v_bs_2042_ = v___x_2050_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0___boxed(lean_object* v_sz_2052_, lean_object* v_i_2053_, lean_object* v_bs_2054_){
_start:
{
size_t v_sz_boxed_2055_; size_t v_i_boxed_2056_; lean_object* v_res_2057_; 
v_sz_boxed_2055_ = lean_unbox_usize(v_sz_2052_);
lean_dec(v_sz_2052_);
v_i_boxed_2056_ = lean_unbox_usize(v_i_2053_);
lean_dec(v_i_2053_);
v_res_2057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(v_sz_boxed_2055_, v_i_boxed_2056_, v_bs_2054_);
return v_res_2057_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2(lean_object* v_s_2058_, lean_object* v_inst_2059_, lean_object* v_R_2060_, lean_object* v_a_2061_, uint8_t v_b_2062_, lean_object* v_c_2063_){
_start:
{
uint8_t v___x_2064_; 
v___x_2064_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_2058_, v_a_2061_, v_b_2062_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___boxed(lean_object* v_s_2065_, lean_object* v_inst_2066_, lean_object* v_R_2067_, lean_object* v_a_2068_, lean_object* v_b_2069_, lean_object* v_c_2070_){
_start:
{
uint8_t v_b_boxed_2071_; uint8_t v_res_2072_; lean_object* v_r_2073_; 
v_b_boxed_2071_ = lean_unbox(v_b_2069_);
v_res_2072_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2(v_s_2065_, v_inst_2066_, v_R_2067_, v_a_2068_, v_b_boxed_2071_, v_c_2070_);
lean_dec_ref(v_s_2065_);
v_r_2073_ = lean_box(v_res_2072_);
return v_r_2073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter___redArg(lean_object* v_x_2074_, lean_object* v_h__1_2075_, lean_object* v_h__2_2076_, lean_object* v_h__3_2077_, lean_object* v_h__4_2078_){
_start:
{
switch(lean_obj_tag(v_x_2074_))
{
case 0:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
lean_dec(v_h__3_2077_);
lean_dec(v_h__2_2076_);
lean_dec(v_h__1_2075_);
v___x_2079_ = lean_box(0);
v___x_2080_ = lean_apply_1(v_h__4_2078_, v___x_2079_);
return v___x_2080_;
}
case 1:
{
lean_object* v_info_2081_; lean_object* v_kind_2082_; lean_object* v_args_2083_; lean_object* v___x_2084_; 
lean_dec(v_h__4_2078_);
lean_dec(v_h__3_2077_);
lean_dec(v_h__1_2075_);
v_info_2081_ = lean_ctor_get(v_x_2074_, 0);
lean_inc(v_info_2081_);
v_kind_2082_ = lean_ctor_get(v_x_2074_, 1);
lean_inc(v_kind_2082_);
v_args_2083_ = lean_ctor_get(v_x_2074_, 2);
lean_inc_ref(v_args_2083_);
lean_dec_ref_known(v_x_2074_, 3);
v___x_2084_ = lean_apply_3(v_h__2_2076_, v_info_2081_, v_kind_2082_, v_args_2083_);
return v___x_2084_;
}
case 2:
{
lean_object* v_info_2085_; lean_object* v_val_2086_; lean_object* v___x_2087_; 
lean_dec(v_h__4_2078_);
lean_dec(v_h__2_2076_);
lean_dec(v_h__1_2075_);
v_info_2085_ = lean_ctor_get(v_x_2074_, 0);
lean_inc(v_info_2085_);
v_val_2086_ = lean_ctor_get(v_x_2074_, 1);
lean_inc_ref(v_val_2086_);
lean_dec_ref_known(v_x_2074_, 2);
v___x_2087_ = lean_apply_2(v_h__3_2077_, v_info_2085_, v_val_2086_);
return v___x_2087_;
}
default: 
{
lean_object* v_info_2088_; lean_object* v_rawVal_2089_; lean_object* v_val_2090_; lean_object* v_preresolved_2091_; lean_object* v___x_2092_; 
lean_dec(v_h__4_2078_);
lean_dec(v_h__3_2077_);
lean_dec(v_h__2_2076_);
v_info_2088_ = lean_ctor_get(v_x_2074_, 0);
lean_inc(v_info_2088_);
v_rawVal_2089_ = lean_ctor_get(v_x_2074_, 1);
lean_inc_ref(v_rawVal_2089_);
v_val_2090_ = lean_ctor_get(v_x_2074_, 2);
lean_inc(v_val_2090_);
v_preresolved_2091_ = lean_ctor_get(v_x_2074_, 3);
lean_inc(v_preresolved_2091_);
lean_dec_ref_known(v_x_2074_, 4);
v___x_2092_ = lean_apply_4(v_h__1_2075_, v_info_2088_, v_rawVal_2089_, v_val_2090_, v_preresolved_2091_);
return v___x_2092_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter(lean_object* v_motive_2093_, lean_object* v_x_2094_, lean_object* v_h__1_2095_, lean_object* v_h__2_2096_, lean_object* v_h__3_2097_, lean_object* v_h__4_2098_){
_start:
{
switch(lean_obj_tag(v_x_2094_))
{
case 0:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
lean_dec(v_h__3_2097_);
lean_dec(v_h__2_2096_);
lean_dec(v_h__1_2095_);
v___x_2099_ = lean_box(0);
v___x_2100_ = lean_apply_1(v_h__4_2098_, v___x_2099_);
return v___x_2100_;
}
case 1:
{
lean_object* v_info_2101_; lean_object* v_kind_2102_; lean_object* v_args_2103_; lean_object* v___x_2104_; 
lean_dec(v_h__4_2098_);
lean_dec(v_h__3_2097_);
lean_dec(v_h__1_2095_);
v_info_2101_ = lean_ctor_get(v_x_2094_, 0);
lean_inc(v_info_2101_);
v_kind_2102_ = lean_ctor_get(v_x_2094_, 1);
lean_inc(v_kind_2102_);
v_args_2103_ = lean_ctor_get(v_x_2094_, 2);
lean_inc_ref(v_args_2103_);
lean_dec_ref_known(v_x_2094_, 3);
v___x_2104_ = lean_apply_3(v_h__2_2096_, v_info_2101_, v_kind_2102_, v_args_2103_);
return v___x_2104_;
}
case 2:
{
lean_object* v_info_2105_; lean_object* v_val_2106_; lean_object* v___x_2107_; 
lean_dec(v_h__4_2098_);
lean_dec(v_h__2_2096_);
lean_dec(v_h__1_2095_);
v_info_2105_ = lean_ctor_get(v_x_2094_, 0);
lean_inc(v_info_2105_);
v_val_2106_ = lean_ctor_get(v_x_2094_, 1);
lean_inc_ref(v_val_2106_);
lean_dec_ref_known(v_x_2094_, 2);
v___x_2107_ = lean_apply_2(v_h__3_2097_, v_info_2105_, v_val_2106_);
return v___x_2107_;
}
default: 
{
lean_object* v_info_2108_; lean_object* v_rawVal_2109_; lean_object* v_val_2110_; lean_object* v_preresolved_2111_; lean_object* v___x_2112_; 
lean_dec(v_h__4_2098_);
lean_dec(v_h__3_2097_);
lean_dec(v_h__2_2096_);
v_info_2108_ = lean_ctor_get(v_x_2094_, 0);
lean_inc(v_info_2108_);
v_rawVal_2109_ = lean_ctor_get(v_x_2094_, 1);
lean_inc_ref(v_rawVal_2109_);
v_val_2110_ = lean_ctor_get(v_x_2094_, 2);
lean_inc(v_val_2110_);
v_preresolved_2111_ = lean_ctor_get(v_x_2094_, 3);
lean_inc(v_preresolved_2111_);
lean_dec_ref_known(v_x_2094_, 4);
v___x_2112_ = lean_apply_4(v_h__1_2095_, v_info_2108_, v_rawVal_2109_, v_val_2110_, v_preresolved_2111_);
return v___x_2112_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_2113_, lean_object* v_h__1_2114_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = lean_apply_2(v_h__1_2114_, v_x_2113_, lean_box(0));
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_2116_, lean_object* v_P_2117_, lean_object* v_motive_2118_, lean_object* v_x_2119_, lean_object* v_h__1_2120_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = lean_apply_2(v_h__1_2120_, v_x_2119_, lean_box(0));
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___redArg(lean_object* v_syn_2122_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_syn_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(lean_object* v_name_2124_, lean_object* v_syn_2125_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_syn_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___boxed(lean_object* v_name_2127_, lean_object* v_syn_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(v_name_2127_, v_syn_2128_);
lean_dec(v_name_2127_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(lean_object* v_e_2136_){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; 
v___x_2163_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__1));
v___x_2164_ = lean_unsigned_to_nat(2u);
v___x_2165_ = l_Lean_Expr_isAppOfArity(v_e_2136_, v___x_2163_, v___x_2164_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2166_; lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2166_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
v___x_2167_ = lean_unsigned_to_nat(3u);
v___x_2168_ = l_Lean_Expr_isAppOfArity(v_e_2136_, v___x_2166_, v___x_2167_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2169_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
v___x_2170_ = l_Lean_Expr_isAppOfArity(v_e_2136_, v___x_2169_, v___x_2167_);
if (v___x_2170_ == 0)
{
lean_object* v___x_2171_; uint8_t v___x_2172_; 
v___x_2171_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_2172_ = l_Lean_Expr_isAppOfArity(v_e_2136_, v___x_2171_, v___x_2167_);
if (v___x_2172_ == 0)
{
goto v___jp_2137_;
}
else
{
lean_object* v___x_2173_; 
v___x_2173_ = l_Lean_Expr_appArg_x21(v_e_2136_);
if (lean_obj_tag(v___x_2173_) == 6)
{
lean_object* v_binderName_2174_; lean_object* v_binderType_2175_; lean_object* v_body_2176_; uint8_t v_binderInfo_2177_; lean_object* v___x_2178_; 
lean_dec_ref(v_e_2136_);
v_binderName_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_binderName_2174_);
v_binderType_2175_ = lean_ctor_get(v___x_2173_, 1);
lean_inc_ref(v_binderType_2175_);
v_body_2176_ = lean_ctor_get(v___x_2173_, 2);
lean_inc_ref(v_body_2176_);
v_binderInfo_2177_ = lean_ctor_get_uint8(v___x_2173_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_2173_, 3);
v___x_2178_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_2176_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_dec_ref(v_binderType_2175_);
lean_dec(v_binderName_2174_);
return v___x_2178_;
}
else
{
lean_object* v_val_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2196_; 
v_val_2179_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2196_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_val_2179_);
lean_dec(v___x_2178_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2196_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v_fst_2183_; lean_object* v_snd_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2195_; 
v_fst_2183_ = lean_ctor_get(v_val_2179_, 0);
v_snd_2184_ = lean_ctor_get(v_val_2179_, 1);
v_isSharedCheck_2195_ = !lean_is_exclusive(v_val_2179_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2186_ = v_val_2179_;
v_isShared_2187_ = v_isSharedCheck_2195_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_snd_2184_);
lean_inc(v_fst_2183_);
lean_dec(v_val_2179_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2195_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; lean_object* v___x_2190_; 
v___x_2188_ = l_Lean_mkForall(v_binderName_2174_, v_binderInfo_2177_, v_binderType_2175_, v_snd_2184_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 1, v___x_2188_);
v___x_2190_ = v___x_2186_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_fst_2183_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v___x_2188_);
v___x_2190_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
lean_object* v___x_2192_; 
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2190_);
v___x_2192_ = v___x_2181_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2173_);
goto v___jp_2137_;
}
}
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = l_Lean_Expr_appFn_x21(v_e_2136_);
v___x_2198_ = l_Lean_Expr_appArg_x21(v___x_2197_);
lean_dec_ref(v___x_2197_);
v___x_2199_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2198_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_dec_ref(v_e_2136_);
return v___x_2199_;
}
else
{
lean_object* v_val_2200_; lean_object* v_snd_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v_val_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_val_2200_);
lean_dec_ref_known(v___x_2199_, 1);
v_snd_2201_ = lean_ctor_get(v_val_2200_, 1);
lean_inc(v_snd_2201_);
lean_dec(v_val_2200_);
v___x_2202_ = l_Lean_Expr_appArg_x21(v_e_2136_);
lean_dec_ref(v_e_2136_);
v___x_2203_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2202_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_dec(v_snd_2201_);
return v___x_2203_;
}
else
{
lean_object* v_val_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2221_; 
v_val_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2221_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_val_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2221_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v_fst_2208_; lean_object* v_snd_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2220_; 
v_fst_2208_ = lean_ctor_get(v_val_2204_, 0);
v_snd_2209_ = lean_ctor_get(v_val_2204_, 1);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_val_2204_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2211_ = v_val_2204_;
v_isShared_2212_ = v_isSharedCheck_2220_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_snd_2209_);
lean_inc(v_fst_2208_);
lean_dec(v_val_2204_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2220_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2213_ = l_Lean_mkOr(v_snd_2201_, v_snd_2209_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 1, v___x_2213_);
v___x_2215_ = v___x_2211_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_fst_2208_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
lean_object* v___x_2217_; 
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2215_);
v___x_2217_ = v___x_2206_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
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
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = l_Lean_Expr_appFn_x21(v_e_2136_);
v___x_2223_ = l_Lean_Expr_appArg_x21(v___x_2222_);
lean_dec_ref(v___x_2222_);
v___x_2224_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2223_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_dec_ref(v_e_2136_);
return v___x_2224_;
}
else
{
lean_object* v_val_2225_; lean_object* v_snd_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v_val_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_val_2225_);
lean_dec_ref_known(v___x_2224_, 1);
v_snd_2226_ = lean_ctor_get(v_val_2225_, 1);
lean_inc(v_snd_2226_);
lean_dec(v_val_2225_);
v___x_2227_ = l_Lean_Expr_appArg_x21(v_e_2136_);
lean_dec_ref(v_e_2136_);
v___x_2228_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2227_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_dec(v_snd_2226_);
return v___x_2228_;
}
else
{
lean_object* v_val_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2246_; 
v_val_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2246_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_val_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2246_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v_fst_2233_; lean_object* v_snd_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2245_; 
v_fst_2233_ = lean_ctor_get(v_val_2229_, 0);
v_snd_2234_ = lean_ctor_get(v_val_2229_, 1);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_val_2229_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2236_ = v_val_2229_;
v_isShared_2237_ = v_isSharedCheck_2245_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_snd_2234_);
lean_inc(v_fst_2233_);
lean_dec(v_val_2229_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2245_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2238_; lean_object* v___x_2240_; 
v___x_2238_ = l_Lean_mkAnd(v_snd_2226_, v_snd_2234_);
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 1, v___x_2238_);
v___x_2240_ = v___x_2236_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_fst_2233_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
lean_object* v___x_2242_; 
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v___x_2240_);
v___x_2242_ = v___x_2231_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
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
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2247_ = lean_box(0);
v___x_2248_ = l_Lean_Expr_getAppFn(v_e_2136_);
v___x_2249_ = l_Lean_Expr_constLevels_x21(v___x_2248_);
lean_dec_ref(v___x_2248_);
v___x_2250_ = lean_unsigned_to_nat(0u);
v___x_2251_ = l_List_get_x21Internal___redArg(v___x_2247_, v___x_2249_, v___x_2250_);
lean_dec(v___x_2249_);
v___x_2252_ = lean_unsigned_to_nat(1u);
v___x_2253_ = l_Lean_Expr_getAppNumArgs(v_e_2136_);
v___x_2254_ = lean_nat_sub(v___x_2253_, v___x_2252_);
lean_dec(v___x_2253_);
v___x_2255_ = lean_nat_sub(v___x_2254_, v___x_2252_);
lean_dec(v___x_2254_);
v___x_2256_ = l_Lean_Expr_getRevArg_x21(v_e_2136_, v___x_2255_);
lean_dec_ref(v_e_2136_);
v___x_2257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2251_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
v___x_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
return v___x_2258_;
}
v___jp_2137_:
{
if (lean_obj_tag(v_e_2136_) == 8)
{
lean_object* v_declName_2138_; lean_object* v_type_2139_; lean_object* v_value_2140_; lean_object* v_body_2141_; uint8_t v_nondep_2142_; lean_object* v___x_2143_; 
v_declName_2138_ = lean_ctor_get(v_e_2136_, 0);
lean_inc(v_declName_2138_);
v_type_2139_ = lean_ctor_get(v_e_2136_, 1);
lean_inc_ref(v_type_2139_);
v_value_2140_ = lean_ctor_get(v_e_2136_, 2);
lean_inc_ref(v_value_2140_);
v_body_2141_ = lean_ctor_get(v_e_2136_, 3);
lean_inc_ref(v_body_2141_);
v_nondep_2142_ = lean_ctor_get_uint8(v_e_2136_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2136_, 4);
v___x_2143_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_2141_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_dec_ref(v_value_2140_);
lean_dec_ref(v_type_2139_);
lean_dec(v_declName_2138_);
return v___x_2143_;
}
else
{
lean_object* v_val_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2161_; 
v_val_2144_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2146_ = v___x_2143_;
v_isShared_2147_ = v_isSharedCheck_2161_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_val_2144_);
lean_dec(v___x_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2161_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v_fst_2148_; lean_object* v_snd_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2160_; 
v_fst_2148_ = lean_ctor_get(v_val_2144_, 0);
v_snd_2149_ = lean_ctor_get(v_val_2144_, 1);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_val_2144_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2151_ = v_val_2144_;
v_isShared_2152_ = v_isSharedCheck_2160_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_snd_2149_);
lean_inc(v_fst_2148_);
lean_dec(v_val_2144_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2160_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2153_; lean_object* v___x_2155_; 
v___x_2153_ = l_Lean_Expr_letE___override(v_declName_2138_, v_type_2139_, v_value_2140_, v_snd_2149_, v_nondep_2142_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 1, v___x_2153_);
v___x_2155_ = v___x_2151_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_fst_2148_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2157_; 
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2155_);
v___x_2157_ = v___x_2146_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
}
}
else
{
lean_object* v___x_2162_; 
lean_dec_ref(v_e_2136_);
v___x_2162_ = lean_box(0);
return v___x_2162_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(lean_object* v_e_2259_){
_start:
{
lean_object* v___x_2260_; 
lean_inc_ref(v_e_2259_);
v___x_2260_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_e_2259_);
if (lean_obj_tag(v___x_2260_) == 0)
{
return v_e_2259_;
}
else
{
lean_object* v_val_2261_; lean_object* v_fst_2262_; lean_object* v_snd_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
lean_dec_ref(v_e_2259_);
v_val_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_val_2261_);
lean_dec_ref_known(v___x_2260_, 1);
v_fst_2262_ = lean_ctor_get(v_val_2261_, 0);
lean_inc_n(v_fst_2262_, 2);
v_snd_2263_ = lean_ctor_get(v_val_2261_, 1);
lean_inc(v_snd_2263_);
lean_dec(v_val_2261_);
v___x_2264_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_2262_);
v___x_2265_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_2262_, v___x_2264_, v_snd_2263_);
return v___x_2265_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6(void){
_start:
{
lean_object* v___x_2276_; 
v___x_2276_ = l_Array_mkArray0___redArg();
return v___x_2276_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__23));
v___x_2315_ = l_String_toRawSubstring_x27(v___x_2314_);
return v___x_2315_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30(void){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29));
v___x_2332_ = l_String_toRawSubstring_x27(v___x_2331_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(lean_object* v_handlers_2347_, lean_object* v_default_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v___x_2354_; lean_object* v_handlers_2355_; 
v___x_2354_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v_handlers_2355_ = l_Lean_Syntax_SepArray_ofElems(v___x_2354_, v_handlers_2347_);
switch(lean_obj_tag(v_default_2348_))
{
case 0:
{
lean_object* v_ref_2356_; uint8_t v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v_ref_2356_ = lean_ctor_get(v_a_2351_, 2);
v___x_2357_ = 0;
v___x_2358_ = l_Lean_SourceInfo_fromRef(v_ref_2356_, v___x_2357_);
v___x_2359_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__2));
v___x_2360_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__3));
lean_inc_n(v___x_2358_, 3);
v___x_2361_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2358_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
v___x_2362_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2363_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2364_ = l_Array_append___redArg(v___x_2363_, v_handlers_2355_);
lean_dec_ref(v_handlers_2355_);
v___x_2365_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2358_);
lean_ctor_set(v___x_2365_, 1, v___x_2362_);
lean_ctor_set(v___x_2365_, 2, v___x_2364_);
v___x_2366_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2367_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2358_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = l_Lean_Syntax_node3(v___x_2358_, v___x_2359_, v___x_2361_, v___x_2365_, v___x_2367_);
v___x_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
return v___x_2369_;
}
case 1:
{
lean_object* v_toCold_2370_; lean_object* v_ref_2371_; lean_object* v_quotContext_2372_; lean_object* v_currMacroScope_2373_; uint8_t v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v_toCold_2370_ = lean_ctor_get(v_a_2351_, 0);
v_ref_2371_ = lean_ctor_get(v_a_2351_, 2);
v_quotContext_2372_ = lean_ctor_get(v_toCold_2370_, 8);
v_currMacroScope_2373_ = lean_ctor_get(v_toCold_2370_, 9);
v___x_2374_ = 0;
v___x_2375_ = l_Lean_SourceInfo_fromRef(v_ref_2371_, v___x_2374_);
v___x_2376_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2377_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2375_, 12);
v___x_2378_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2375_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
v___x_2379_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2380_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2381_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2382_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2383_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2384_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2375_);
lean_ctor_set(v___x_2384_, 1, v___x_2382_);
v___x_2385_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2386_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2375_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
v___x_2388_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2389_ = l_Array_append___redArg(v___x_2388_, v_handlers_2355_);
lean_dec_ref(v_handlers_2355_);
v___x_2390_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2375_);
lean_ctor_set(v___x_2390_, 1, v___x_2354_);
v___x_2391_ = lean_array_push(v___x_2389_, v___x_2390_);
v___x_2392_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24);
v___x_2393_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25));
lean_inc(v_currMacroScope_2373_);
lean_inc(v_quotContext_2372_);
v___x_2394_ = l_Lean_addMacroScope(v_quotContext_2372_, v___x_2393_, v_currMacroScope_2373_);
v___x_2395_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__28));
v___x_2396_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2375_);
lean_ctor_set(v___x_2396_, 1, v___x_2392_);
lean_ctor_set(v___x_2396_, 2, v___x_2394_);
lean_ctor_set(v___x_2396_, 3, v___x_2395_);
v___x_2397_ = lean_array_push(v___x_2391_, v___x_2396_);
v___x_2398_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2375_);
lean_ctor_set(v___x_2398_, 1, v___x_2381_);
lean_ctor_set(v___x_2398_, 2, v___x_2397_);
v___x_2399_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2400_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2375_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
v___x_2401_ = l_Lean_Syntax_node3(v___x_2375_, v___x_2385_, v___x_2387_, v___x_2398_, v___x_2400_);
v___x_2402_ = l_Lean_Syntax_node2(v___x_2375_, v___x_2383_, v___x_2384_, v___x_2401_);
v___x_2403_ = l_Lean_Syntax_node1(v___x_2375_, v___x_2381_, v___x_2402_);
v___x_2404_ = l_Lean_Syntax_node1(v___x_2375_, v___x_2380_, v___x_2403_);
v___x_2405_ = l_Lean_Syntax_node1(v___x_2375_, v___x_2379_, v___x_2404_);
v___x_2406_ = l_Lean_Syntax_node2(v___x_2375_, v___x_2376_, v___x_2378_, v___x_2405_);
v___x_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
return v___x_2407_;
}
case 2:
{
lean_object* v_toCold_2408_; lean_object* v_ref_2409_; lean_object* v_quotContext_2410_; lean_object* v_currMacroScope_2411_; uint8_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v_toCold_2408_ = lean_ctor_get(v_a_2351_, 0);
v_ref_2409_ = lean_ctor_get(v_a_2351_, 2);
v_quotContext_2410_ = lean_ctor_get(v_toCold_2408_, 8);
v_currMacroScope_2411_ = lean_ctor_get(v_toCold_2408_, 9);
v___x_2412_ = 0;
v___x_2413_ = l_Lean_SourceInfo_fromRef(v_ref_2409_, v___x_2412_);
v___x_2414_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2415_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2413_, 12);
v___x_2416_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2413_);
lean_ctor_set(v___x_2416_, 1, v___x_2415_);
v___x_2417_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2418_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2419_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2420_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2421_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2413_);
lean_ctor_set(v___x_2422_, 1, v___x_2420_);
v___x_2423_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2424_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2425_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2413_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
v___x_2426_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2427_ = l_Array_append___redArg(v___x_2426_, v_handlers_2355_);
lean_dec_ref(v_handlers_2355_);
v___x_2428_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2413_);
lean_ctor_set(v___x_2428_, 1, v___x_2354_);
v___x_2429_ = lean_array_push(v___x_2427_, v___x_2428_);
v___x_2430_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30);
v___x_2431_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31));
lean_inc(v_currMacroScope_2411_);
lean_inc(v_quotContext_2410_);
v___x_2432_ = l_Lean_addMacroScope(v_quotContext_2410_, v___x_2431_, v_currMacroScope_2411_);
v___x_2433_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__34));
v___x_2434_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2413_);
lean_ctor_set(v___x_2434_, 1, v___x_2430_);
lean_ctor_set(v___x_2434_, 2, v___x_2432_);
lean_ctor_set(v___x_2434_, 3, v___x_2433_);
v___x_2435_ = lean_array_push(v___x_2429_, v___x_2434_);
v___x_2436_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2413_);
lean_ctor_set(v___x_2436_, 1, v___x_2419_);
lean_ctor_set(v___x_2436_, 2, v___x_2435_);
v___x_2437_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2438_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2413_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = l_Lean_Syntax_node3(v___x_2413_, v___x_2423_, v___x_2425_, v___x_2436_, v___x_2438_);
v___x_2440_ = l_Lean_Syntax_node2(v___x_2413_, v___x_2421_, v___x_2422_, v___x_2439_);
v___x_2441_ = l_Lean_Syntax_node1(v___x_2413_, v___x_2419_, v___x_2440_);
v___x_2442_ = l_Lean_Syntax_node1(v___x_2413_, v___x_2418_, v___x_2441_);
v___x_2443_ = l_Lean_Syntax_node1(v___x_2413_, v___x_2417_, v___x_2442_);
v___x_2444_ = l_Lean_Syntax_node2(v___x_2413_, v___x_2414_, v___x_2416_, v___x_2443_);
v___x_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
return v___x_2445_;
}
default: 
{
lean_object* v_e_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v_e_2446_ = lean_ctor_get(v_default_2348_, 0);
lean_inc_ref(v_e_2446_);
lean_dec_ref_known(v_default_2348_, 1);
v___x_2447_ = lean_box(1);
v___x_2448_ = l_Lean_PrettyPrinter_delab(v_e_2446_, v___x_2447_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2485_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2451_ = v___x_2448_;
v_isShared_2452_ = v_isSharedCheck_2485_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2448_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2485_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v_ref_2453_; uint8_t v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2483_; 
v_ref_2453_ = lean_ctor_get(v_a_2351_, 2);
v___x_2454_ = 0;
v___x_2455_ = l_Lean_SourceInfo_fromRef(v_ref_2453_, v___x_2454_);
v___x_2456_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2457_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2455_, 11);
v___x_2458_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2455_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
v___x_2459_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2460_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2461_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2462_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2463_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2464_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2455_);
lean_ctor_set(v___x_2464_, 1, v___x_2462_);
v___x_2465_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2466_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2455_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
v___x_2468_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2469_ = l_Array_append___redArg(v___x_2468_, v_handlers_2355_);
lean_dec_ref(v_handlers_2355_);
v___x_2470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2455_);
lean_ctor_set(v___x_2470_, 1, v___x_2354_);
v___x_2471_ = lean_array_push(v___x_2469_, v___x_2470_);
v___x_2472_ = lean_array_push(v___x_2471_, v_a_2449_);
v___x_2473_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2455_);
lean_ctor_set(v___x_2473_, 1, v___x_2461_);
lean_ctor_set(v___x_2473_, 2, v___x_2472_);
v___x_2474_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2455_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = l_Lean_Syntax_node3(v___x_2455_, v___x_2465_, v___x_2467_, v___x_2473_, v___x_2475_);
v___x_2477_ = l_Lean_Syntax_node2(v___x_2455_, v___x_2463_, v___x_2464_, v___x_2476_);
v___x_2478_ = l_Lean_Syntax_node1(v___x_2455_, v___x_2461_, v___x_2477_);
v___x_2479_ = l_Lean_Syntax_node1(v___x_2455_, v___x_2460_, v___x_2478_);
v___x_2480_ = l_Lean_Syntax_node1(v___x_2455_, v___x_2459_, v___x_2479_);
v___x_2481_ = l_Lean_Syntax_node2(v___x_2455_, v___x_2456_, v___x_2458_, v___x_2480_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 0, v___x_2481_);
v___x_2483_ = v___x_2451_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2481_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
else
{
lean_dec_ref(v_handlers_2355_);
return v___x_2448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___boxed(lean_object* v_handlers_2486_, lean_object* v_default_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_handlers_2486_, v_default_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec_ref(v_handlers_2486_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(lean_object* v_e_2494_, lean_object* v___y_2495_){
_start:
{
uint8_t v___x_2497_; 
v___x_2497_ = l_Lean_Expr_hasMVar(v_e_2494_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; 
v___x_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2498_, 0, v_e_2494_);
return v___x_2498_;
}
else
{
lean_object* v___x_2499_; lean_object* v_mctx_2500_; lean_object* v___x_2501_; lean_object* v_fst_2502_; lean_object* v_snd_2503_; lean_object* v___x_2504_; lean_object* v_cache_2505_; lean_object* v_zetaDeltaFVarIds_2506_; lean_object* v_postponed_2507_; lean_object* v_diag_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2517_; 
v___x_2499_ = lean_st_ref_get(v___y_2495_);
v_mctx_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc_ref(v_mctx_2500_);
lean_dec(v___x_2499_);
v___x_2501_ = l_Lean_instantiateMVarsCore(v_mctx_2500_, v_e_2494_);
v_fst_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_fst_2502_);
v_snd_2503_ = lean_ctor_get(v___x_2501_, 1);
lean_inc(v_snd_2503_);
lean_dec_ref(v___x_2501_);
v___x_2504_ = lean_st_ref_take(v___y_2495_);
v_cache_2505_ = lean_ctor_get(v___x_2504_, 1);
v_zetaDeltaFVarIds_2506_ = lean_ctor_get(v___x_2504_, 2);
v_postponed_2507_ = lean_ctor_get(v___x_2504_, 3);
v_diag_2508_ = lean_ctor_get(v___x_2504_, 4);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2517_ == 0)
{
lean_object* v_unused_2518_; 
v_unused_2518_ = lean_ctor_get(v___x_2504_, 0);
lean_dec(v_unused_2518_);
v___x_2510_ = v___x_2504_;
v_isShared_2511_ = v_isSharedCheck_2517_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_diag_2508_);
lean_inc(v_postponed_2507_);
lean_inc(v_zetaDeltaFVarIds_2506_);
lean_inc(v_cache_2505_);
lean_dec(v___x_2504_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2517_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 0, v_snd_2503_);
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_snd_2503_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v_cache_2505_);
lean_ctor_set(v_reuseFailAlloc_2516_, 2, v_zetaDeltaFVarIds_2506_);
lean_ctor_set(v_reuseFailAlloc_2516_, 3, v_postponed_2507_);
lean_ctor_set(v_reuseFailAlloc_2516_, 4, v_diag_2508_);
v___x_2513_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = lean_st_ref_put(v___y_2495_, v___x_2513_);
v___x_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2515_, 0, v_fst_2502_);
return v___x_2515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg___boxed(lean_object* v_e_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2519_, v___y_2520_);
lean_dec(v___y_2520_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(lean_object* v_e_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2523_, v___y_2529_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___boxed(lean_object* v_e_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(v_e_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(lean_object* v_x_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v___x_2555_; 
lean_inc(v___y_2549_);
lean_inc_ref(v___y_2548_);
lean_inc(v___y_2547_);
lean_inc_ref(v___y_2546_);
v___x_2555_ = lean_apply_9(v_x_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, lean_box(0));
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed(lean_object* v_x_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(v_x_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(lean_object* v_mvarId_2567_, lean_object* v_x_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v___f_2578_; lean_object* v___x_2579_; 
lean_inc(v___y_2572_);
lean_inc_ref(v___y_2571_);
lean_inc(v___y_2570_);
lean_inc_ref(v___y_2569_);
v___f_2578_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2578_, 0, v_x_2568_);
lean_closure_set(v___f_2578_, 1, v___y_2569_);
lean_closure_set(v___f_2578_, 2, v___y_2570_);
lean_closure_set(v___f_2578_, 3, v___y_2571_);
lean_closure_set(v___f_2578_, 4, v___y_2572_);
v___x_2579_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2567_, v___f_2578_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2579_) == 0)
{
return v___x_2579_;
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2579_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2579_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___boxed(lean_object* v_mvarId_2588_, lean_object* v_x_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2588_, v_x_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(lean_object* v_00_u03b1_2600_, lean_object* v_mvarId_2601_, lean_object* v_x_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2601_, v_x_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___boxed(lean_object* v_00_u03b1_2613_, lean_object* v_mvarId_2614_, lean_object* v_x_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(v_00_u03b1_2613_, v_mvarId_2614_, v_x_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(lean_object* v_a_2626_, lean_object* v_inv_2627_, lean_object* v_xs_2628_, uint8_t v___x_2629_, lean_object* v___x_2630_, lean_object* v_letMuts_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2641_; 
lean_inc_ref(v_letMuts_2631_);
lean_inc_ref(v_xs_2628_);
v___x_2641_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_a_2626_, v_inv_2627_, v_xs_2628_, v_letMuts_2631_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2718_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2644_ = v___x_2641_;
v_isShared_2645_ = v_isSharedCheck_2718_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2641_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2718_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
if (lean_obj_tag(v_a_2642_) == 1)
{
lean_object* v_val_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2713_; 
lean_del_object(v___x_2644_);
v_val_2646_ = lean_ctor_get(v_a_2642_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v_a_2642_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2648_ = v_a_2642_;
v_isShared_2649_ = v_isSharedCheck_2713_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_val_2646_);
lean_dec(v_a_2642_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2713_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v_snd_2650_; lean_object* v_fst_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2712_; 
v_snd_2650_ = lean_ctor_get(v_val_2646_, 1);
v_fst_2651_ = lean_ctor_get(v_val_2646_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_val_2646_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2653_ = v_val_2646_;
v_isShared_2654_ = v_isSharedCheck_2712_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_snd_2650_);
lean_inc(v_fst_2651_);
lean_dec(v_val_2646_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2712_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v_fst_2655_; lean_object* v_snd_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2711_; 
v_fst_2655_ = lean_ctor_get(v_snd_2650_, 0);
v_snd_2656_ = lean_ctor_get(v_snd_2650_, 1);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_snd_2650_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2658_ = v_snd_2650_;
v_isShared_2659_ = v_isSharedCheck_2711_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_snd_2656_);
lean_inc(v_fst_2655_);
lean_dec(v_snd_2650_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2711_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v_lvl_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; uint8_t v___x_2670_; lean_object* v___x_2671_; 
v_lvl_2660_ = lean_ctor_get(v_fst_2651_, 0);
lean_inc(v_lvl_2660_);
v___x_2661_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2651_);
lean_inc(v_fst_2655_);
v___x_2662_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2655_);
v___x_2663_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(v_lvl_2660_, v___x_2661_, v___x_2662_);
v___x_2664_ = lean_unsigned_to_nat(2u);
v___x_2665_ = lean_mk_empty_array_with_capacity(v___x_2664_);
v___x_2666_ = lean_array_push(v___x_2665_, v_xs_2628_);
lean_inc_ref(v_letMuts_2631_);
v___x_2667_ = lean_array_push(v___x_2666_, v_letMuts_2631_);
v___x_2668_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v___x_2663_);
v___x_2669_ = 0;
v___x_2670_ = 1;
v___x_2671_ = l_Lean_Meta_mkLambdaFVars(v___x_2667_, v___x_2668_, v___x_2669_, v___x_2629_, v___x_2669_, v___x_2629_, v___x_2670_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec_ref(v___x_2667_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v_letMutsPred_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2672_);
lean_dec_ref_known(v___x_2671_, 1);
v_letMutsPred_2673_ = lean_ctor_get(v_fst_2655_, 2);
lean_inc_ref(v_letMutsPred_2673_);
lean_dec(v_fst_2655_);
v___x_2674_ = lean_mk_empty_array_with_capacity(v___x_2630_);
v___x_2675_ = lean_array_push(v___x_2674_, v_letMuts_2631_);
v___x_2676_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v_letMutsPred_2673_);
v___x_2677_ = l_Lean_Meta_mkLambdaFVars(v___x_2675_, v___x_2676_, v___x_2669_, v___x_2629_, v___x_2669_, v___x_2629_, v___x_2670_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec_ref(v___x_2675_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2694_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2680_ = v___x_2677_;
v_isShared_2681_ = v_isSharedCheck_2694_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2677_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2694_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v_a_2678_);
v___x_2683_ = v___x_2658_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2678_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v_snd_2656_);
v___x_2683_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2685_; 
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 1, v___x_2683_);
lean_ctor_set(v___x_2653_, 0, v_a_2672_);
v___x_2685_ = v___x_2653_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2672_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v___x_2683_);
v___x_2685_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
lean_object* v___x_2687_; 
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v___x_2685_);
v___x_2687_ = v___x_2648_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2685_);
v___x_2687_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
lean_object* v___x_2689_; 
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 0, v___x_2687_);
v___x_2689_ = v___x_2680_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2687_);
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
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_dec(v_a_2672_);
lean_del_object(v___x_2658_);
lean_dec(v_snd_2656_);
lean_del_object(v___x_2653_);
lean_del_object(v___x_2648_);
v_a_2695_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2677_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2677_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_del_object(v___x_2658_);
lean_dec(v_snd_2656_);
lean_dec(v_fst_2655_);
lean_del_object(v___x_2653_);
lean_del_object(v___x_2648_);
lean_dec_ref(v_letMuts_2631_);
v_a_2703_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2671_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2671_);
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
}
}
}
else
{
lean_object* v___x_2714_; lean_object* v___x_2716_; 
lean_dec(v_a_2642_);
lean_dec_ref(v_letMuts_2631_);
lean_dec_ref(v_xs_2628_);
v___x_2714_ = lean_box(0);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v___x_2714_);
v___x_2716_ = v___x_2644_;
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
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_dec_ref(v_letMuts_2631_);
lean_dec_ref(v_xs_2628_);
v_a_2719_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2641_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2641_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed(lean_object* v_a_2727_, lean_object* v_inv_2728_, lean_object* v_xs_2729_, lean_object* v___x_2730_, lean_object* v___x_2731_, lean_object* v_letMuts_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
uint8_t v___x_77205__boxed_2742_; lean_object* v_res_2743_; 
v___x_77205__boxed_2742_ = lean_unbox(v___x_2730_);
v_res_2743_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(v_a_2727_, v_inv_2728_, v_xs_2729_, v___x_77205__boxed_2742_, v___x_2731_, v_letMuts_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___x_2731_);
lean_dec_ref(v_a_2727_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(lean_object* v_k_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v_b_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v___x_2755_; 
lean_inc(v___y_2753_);
lean_inc_ref(v___y_2752_);
lean_inc(v___y_2751_);
lean_inc_ref(v___y_2750_);
lean_inc(v___y_2748_);
lean_inc_ref(v___y_2747_);
lean_inc(v___y_2746_);
lean_inc_ref(v___y_2745_);
v___x_2755_ = lean_apply_10(v_k_2744_, v_b_2749_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, lean_box(0));
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_k_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v_b_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(v_k_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v_b_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(lean_object* v_name_2768_, uint8_t v_bi_2769_, lean_object* v_type_2770_, lean_object* v_k_2771_, uint8_t v_kind_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v___f_2782_; lean_object* v___x_2783_; 
lean_inc(v___y_2776_);
lean_inc_ref(v___y_2775_);
lean_inc(v___y_2774_);
lean_inc_ref(v___y_2773_);
v___f_2782_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2782_, 0, v_k_2771_);
lean_closure_set(v___f_2782_, 1, v___y_2773_);
lean_closure_set(v___f_2782_, 2, v___y_2774_);
lean_closure_set(v___f_2782_, 3, v___y_2775_);
lean_closure_set(v___f_2782_, 4, v___y_2776_);
v___x_2783_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2768_, v_bi_2769_, v_type_2770_, v___f_2782_, v_kind_2772_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
if (lean_obj_tag(v___x_2783_) == 0)
{
return v___x_2783_;
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2783_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2783_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___boxed(lean_object* v_name_2792_, lean_object* v_bi_2793_, lean_object* v_type_2794_, lean_object* v_k_2795_, lean_object* v_kind_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
uint8_t v_bi_boxed_2806_; uint8_t v_kind_boxed_2807_; lean_object* v_res_2808_; 
v_bi_boxed_2806_ = lean_unbox(v_bi_2793_);
v_kind_boxed_2807_ = lean_unbox(v_kind_2796_);
v_res_2808_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2792_, v_bi_boxed_2806_, v_type_2794_, v_k_2795_, v_kind_boxed_2807_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(lean_object* v_name_2809_, lean_object* v_type_2810_, lean_object* v_k_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
uint8_t v___x_2821_; uint8_t v___x_2822_; lean_object* v___x_2823_; 
v___x_2821_ = 0;
v___x_2822_ = 0;
v___x_2823_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2809_, v___x_2821_, v_type_2810_, v_k_2811_, v___x_2822_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg___boxed(lean_object* v_name_2824_, lean_object* v_type_2825_, lean_object* v_k_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_2824_, v_type_2825_, v_k_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(lean_object* v_a_2840_, lean_object* v_inv_2841_, uint8_t v___x_2842_, lean_object* v___x_2843_, lean_object* v_arg_2844_, lean_object* v_xs_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v___x_2855_; lean_object* v___f_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2855_ = lean_box(v___x_2842_);
v___f_2856_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed), 15, 5);
lean_closure_set(v___f_2856_, 0, v_a_2840_);
lean_closure_set(v___f_2856_, 1, v_inv_2841_);
lean_closure_set(v___f_2856_, 2, v_xs_2845_);
lean_closure_set(v___f_2856_, 3, v___x_2855_);
lean_closure_set(v___f_2856_, 4, v___x_2843_);
v___x_2857_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_2858_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_2857_, v_arg_2844_, v___f_2856_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed(lean_object* v_a_2859_, lean_object* v_inv_2860_, lean_object* v___x_2861_, lean_object* v___x_2862_, lean_object* v_arg_2863_, lean_object* v_xs_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
uint8_t v___x_77525__boxed_2874_; lean_object* v_res_2875_; 
v___x_77525__boxed_2874_ = lean_unbox(v___x_2861_);
v_res_2875_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(v_a_2859_, v_inv_2860_, v___x_77525__boxed_2874_, v___x_2862_, v_arg_2863_, v_xs_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
return v_res_2875_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2879_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2880_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2);
v___x_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2880_);
return v___x_2881_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4(void){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2882_ = lean_unsigned_to_nat(32u);
v___x_2883_ = lean_mk_empty_array_with_capacity(v___x_2882_);
v___x_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(lean_object* v_fst_2885_, lean_object* v_xs_2886_, lean_object* v_fst_2887_, lean_object* v_r_2888_, lean_object* v___x_2889_, lean_object* v_fst_2890_, uint8_t v___x_2891_, lean_object* v___x_2892_, lean_object* v_letMuts_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v___x_2903_; 
lean_inc_ref(v_fst_2885_);
v___x_2903_ = l_Lean_Meta_mkNone(v_fst_2885_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v___x_2905_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_2906_ = lean_unsigned_to_nat(2u);
v___x_2907_ = lean_mk_empty_array_with_capacity(v___x_2906_);
lean_inc_ref(v___x_2907_);
v___x_2908_ = lean_array_push(v___x_2907_, v_a_2904_);
lean_inc_ref(v_letMuts_2893_);
v___x_2909_ = lean_array_push(v___x_2908_, v_letMuts_2893_);
v___x_2910_ = l_Lean_Meta_mkAppM(v___x_2905_, v___x_2909_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref_known(v___x_2910_, 1);
lean_inc_ref(v___x_2907_);
v___x_2912_ = lean_array_push(v___x_2907_, v_xs_2886_);
v___x_2913_ = lean_array_push(v___x_2912_, v_a_2911_);
v___x_2914_ = l_Lean_Expr_beta(v_fst_2887_, v___x_2913_);
v___x_2915_ = l_Lean_Meta_mkSome(v_fst_2885_, v_r_2888_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2916_);
lean_dec_ref_known(v___x_2915_, 1);
v___x_2917_ = lean_array_push(v___x_2907_, v_a_2916_);
v___x_2918_ = lean_array_push(v___x_2917_, v_letMuts_2893_);
v___x_2919_ = l_Lean_Meta_mkAppM(v___x_2905_, v___x_2918_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_a_2920_);
lean_dec_ref_known(v___x_2919_, 1);
v___x_2921_ = lean_mk_empty_array_with_capacity(v___x_2889_);
lean_inc_ref(v___x_2921_);
v___x_2922_ = lean_array_push(v___x_2921_, v_a_2920_);
v___x_2923_ = l_Lean_Expr_beta(v_fst_2890_, v___x_2922_);
v___x_2924_ = l_Lean_Meta_getSimpTheorems___redArg(v___y_2901_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2926_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2925_);
lean_dec_ref_known(v___x_2924_, 1);
v___x_2926_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_2901_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v___x_2928_; uint8_t v___x_2929_; uint8_t v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref_known(v___x_2926_, 1);
v___x_2928_ = lean_unsigned_to_nat(100000u);
v___x_2929_ = 0;
v___x_2930_ = 0;
v___x_2931_ = lean_box(0);
v___x_2932_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_2932_, 0, v___x_2928_);
lean_ctor_set(v___x_2932_, 1, v___x_2906_);
lean_ctor_set(v___x_2932_, 2, v___x_2931_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3, v___x_2929_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 1, v___x_2891_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 2, v___x_2929_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 3, v___x_2891_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 4, v___x_2891_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 5, v___x_2891_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 6, v___x_2930_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 7, v___x_2891_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 8, v___x_2891_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 9, v___x_2929_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 10, v___x_2929_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 11, v___x_2929_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 12, v___x_2891_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 13, v___x_2891_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 14, v___x_2929_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 15, v___x_2929_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 16, v___x_2929_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 17, v___x_2891_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 18, v___x_2891_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 19, v___x_2891_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 20, v___x_2891_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 21, v___x_2891_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 22, v___x_2891_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 23, v___x_2891_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 24, v___x_2891_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 25, v___x_2891_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 26, v___x_2929_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 27, v___x_2929_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3 + 28, v___x_2929_);
v___x_2933_ = lean_array_push(v___x_2921_, v_a_2925_);
v___x_2934_ = l_Lean_Options_empty;
v___x_2935_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2932_, v___x_2933_, v_a_2927_, v___x_2934_, v___y_2898_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_a_2936_);
lean_dec_ref_known(v___x_2935_, 1);
v___x_2937_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___x_2938_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__1));
v___x_2939_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_2937_, v___x_2938_, v___x_2929_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; size_t v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc_n(v_a_2940_, 2);
lean_dec_ref_known(v___x_2939_, 1);
v___x_2941_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3);
lean_inc_n(v___x_2892_, 2);
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v___x_2892_);
v___x_2943_ = lean_unsigned_to_nat(32u);
v___x_2944_ = lean_mk_empty_array_with_capacity(v___x_2943_);
v___x_2945_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4);
v___x_2946_ = ((size_t)5ULL);
v___x_2947_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2947_, 0, v___x_2945_);
lean_ctor_set(v___x_2947_, 1, v___x_2944_);
lean_ctor_set(v___x_2947_, 2, v___x_2892_);
lean_ctor_set(v___x_2947_, 3, v___x_2892_);
lean_ctor_set_usize(v___x_2947_, 4, v___x_2946_);
v___x_2948_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2941_);
lean_ctor_set(v___x_2948_, 1, v___x_2941_);
lean_ctor_set(v___x_2948_, 2, v___x_2941_);
lean_ctor_set(v___x_2948_, 3, v___x_2947_);
v___x_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2942_);
lean_ctor_set(v___x_2949_, 1, v___x_2948_);
lean_inc(v_a_2936_);
v___x_2950_ = l_Lean_Meta_simp(v___x_2914_, v_a_2936_, v_a_2940_, v___x_2931_, v___x_2949_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; lean_object* v_fst_2952_; lean_object* v___x_2953_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_a_2951_);
lean_dec_ref_known(v___x_2950_, 1);
v_fst_2952_ = lean_ctor_get(v_a_2951_, 0);
lean_inc(v_fst_2952_);
lean_dec(v_a_2951_);
v___x_2953_ = l_Lean_Meta_simp(v___x_2923_, v_a_2936_, v_a_2940_, v___x_2931_, v___x_2949_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
lean_dec_ref_known(v___x_2949_, 2);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v_fst_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2992_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2953_, 1);
v_fst_2955_ = lean_ctor_get(v_a_2954_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v_a_2954_);
if (v_isSharedCheck_2992_ == 0)
{
lean_object* v_unused_2993_; 
v_unused_2993_ = lean_ctor_get(v_a_2954_, 1);
lean_dec(v_unused_2993_);
v___x_2957_ = v_a_2954_;
v_isShared_2958_ = v_isSharedCheck_2992_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_fst_2955_);
lean_dec(v_a_2954_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2992_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v_expr_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v_expr_2959_ = lean_ctor_get(v_fst_2952_, 0);
lean_inc_ref(v_expr_2959_);
lean_dec(v_fst_2952_);
v___x_2960_ = lean_box(1);
v___x_2961_ = l_Lean_PrettyPrinter_delab(v_expr_2959_, v___x_2960_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v_expr_2963_; lean_object* v___x_2964_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref_known(v___x_2961_, 1);
v_expr_2963_ = lean_ctor_get(v_fst_2955_, 0);
lean_inc_ref(v_expr_2963_);
lean_dec(v_fst_2955_);
v___x_2964_ = l_Lean_PrettyPrinter_delab(v_expr_2963_, v___x_2960_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2975_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2967_ = v___x_2964_;
v_isShared_2968_ = v_isSharedCheck_2975_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2964_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2975_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 1, v_a_2965_);
lean_ctor_set(v___x_2957_, 0, v_a_2962_);
v___x_2970_ = v___x_2957_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2962_);
lean_ctor_set(v_reuseFailAlloc_2974_, 1, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2972_; 
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 0, v___x_2970_);
v___x_2972_ = v___x_2967_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_dec(v_a_2962_);
lean_del_object(v___x_2957_);
v_a_2976_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2964_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2964_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_del_object(v___x_2957_);
lean_dec(v_fst_2955_);
v_a_2984_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2961_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2961_);
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
}
else
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
lean_dec(v_fst_2952_);
v_a_2994_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2953_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2953_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
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
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
lean_dec_ref_known(v___x_2949_, 2);
lean_dec(v_a_2940_);
lean_dec(v_a_2936_);
lean_dec_ref(v___x_2923_);
v_a_3002_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_2950_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_2950_);
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
lean_dec(v_a_2936_);
lean_dec_ref(v___x_2923_);
lean_dec_ref(v___x_2914_);
lean_dec(v___x_2892_);
v_a_3010_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_2939_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_2939_);
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
lean_dec_ref(v___x_2923_);
lean_dec_ref(v___x_2914_);
lean_dec(v___x_2892_);
v_a_3018_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_2935_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_2935_);
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
lean_dec(v_a_2925_);
lean_dec_ref(v___x_2923_);
lean_dec_ref(v___x_2921_);
lean_dec_ref(v___x_2914_);
lean_dec(v___x_2892_);
v_a_3026_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_2926_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_2926_);
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
lean_dec_ref(v___x_2923_);
lean_dec_ref(v___x_2921_);
lean_dec_ref(v___x_2914_);
lean_dec(v___x_2892_);
v_a_3034_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_2924_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_2924_);
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
lean_dec_ref(v___x_2914_);
lean_dec(v___x_2892_);
lean_dec_ref(v_fst_2890_);
v_a_3042_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_2919_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_2919_);
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
lean_dec_ref(v___x_2914_);
lean_dec_ref(v___x_2907_);
lean_dec_ref(v_letMuts_2893_);
lean_dec(v___x_2892_);
lean_dec_ref(v_fst_2890_);
v_a_3050_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_2915_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_2915_);
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
lean_dec_ref(v___x_2907_);
lean_dec_ref(v_letMuts_2893_);
lean_dec(v___x_2892_);
lean_dec_ref(v_fst_2890_);
lean_dec_ref(v_r_2888_);
lean_dec_ref(v_fst_2887_);
lean_dec_ref(v_xs_2886_);
lean_dec_ref(v_fst_2885_);
v_a_3058_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_2910_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_2910_);
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
lean_dec_ref(v_letMuts_2893_);
lean_dec(v___x_2892_);
lean_dec_ref(v_fst_2890_);
lean_dec_ref(v_r_2888_);
lean_dec_ref(v_fst_2887_);
lean_dec_ref(v_xs_2886_);
lean_dec_ref(v_fst_2885_);
v_a_3066_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_2903_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_2903_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed(lean_object** _args){
lean_object* v_fst_3074_ = _args[0];
lean_object* v_xs_3075_ = _args[1];
lean_object* v_fst_3076_ = _args[2];
lean_object* v_r_3077_ = _args[3];
lean_object* v___x_3078_ = _args[4];
lean_object* v_fst_3079_ = _args[5];
lean_object* v___x_3080_ = _args[6];
lean_object* v___x_3081_ = _args[7];
lean_object* v_letMuts_3082_ = _args[8];
lean_object* v___y_3083_ = _args[9];
lean_object* v___y_3084_ = _args[10];
lean_object* v___y_3085_ = _args[11];
lean_object* v___y_3086_ = _args[12];
lean_object* v___y_3087_ = _args[13];
lean_object* v___y_3088_ = _args[14];
lean_object* v___y_3089_ = _args[15];
lean_object* v___y_3090_ = _args[16];
lean_object* v___y_3091_ = _args[17];
_start:
{
uint8_t v___x_77601__boxed_3092_; lean_object* v_res_3093_; 
v___x_77601__boxed_3092_ = lean_unbox(v___x_3080_);
v_res_3093_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(v_fst_3074_, v_xs_3075_, v_fst_3076_, v_r_3077_, v___x_3078_, v_fst_3079_, v___x_77601__boxed_3092_, v___x_3081_, v_letMuts_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___x_3078_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(lean_object* v_fst_3094_, lean_object* v_xs_3095_, lean_object* v_fst_3096_, lean_object* v___x_3097_, lean_object* v_fst_3098_, uint8_t v___x_3099_, lean_object* v___x_3100_, lean_object* v_snd_3101_, lean_object* v_r_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v___x_3112_; lean_object* v___f_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3112_ = lean_box(v___x_3099_);
v___f_3113_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed), 18, 8);
lean_closure_set(v___f_3113_, 0, v_fst_3094_);
lean_closure_set(v___f_3113_, 1, v_xs_3095_);
lean_closure_set(v___f_3113_, 2, v_fst_3096_);
lean_closure_set(v___f_3113_, 3, v_r_3102_);
lean_closure_set(v___f_3113_, 4, v___x_3097_);
lean_closure_set(v___f_3113_, 5, v_fst_3098_);
lean_closure_set(v___f_3113_, 6, v___x_3112_);
lean_closure_set(v___f_3113_, 7, v___x_3100_);
v___x_3114_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3115_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3114_, v_snd_3101_, v___f_3113_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed(lean_object** _args){
lean_object* v_fst_3116_ = _args[0];
lean_object* v_xs_3117_ = _args[1];
lean_object* v_fst_3118_ = _args[2];
lean_object* v___x_3119_ = _args[3];
lean_object* v_fst_3120_ = _args[4];
lean_object* v___x_3121_ = _args[5];
lean_object* v___x_3122_ = _args[6];
lean_object* v_snd_3123_ = _args[7];
lean_object* v_r_3124_ = _args[8];
lean_object* v___y_3125_ = _args[9];
lean_object* v___y_3126_ = _args[10];
lean_object* v___y_3127_ = _args[11];
lean_object* v___y_3128_ = _args[12];
lean_object* v___y_3129_ = _args[13];
lean_object* v___y_3130_ = _args[14];
lean_object* v___y_3131_ = _args[15];
lean_object* v___y_3132_ = _args[16];
lean_object* v___y_3133_ = _args[17];
_start:
{
uint8_t v___x_77997__boxed_3134_; lean_object* v_res_3135_; 
v___x_77997__boxed_3134_ = lean_unbox(v___x_3121_);
v_res_3135_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(v_fst_3116_, v_xs_3117_, v_fst_3118_, v___x_3119_, v_fst_3120_, v___x_77997__boxed_3134_, v___x_3122_, v_snd_3123_, v_r_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(lean_object* v_fst_3139_, lean_object* v_fst_3140_, lean_object* v___x_3141_, lean_object* v_fst_3142_, uint8_t v___x_3143_, lean_object* v___x_3144_, lean_object* v_snd_3145_, lean_object* v_xs_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v___x_3156_; lean_object* v___f_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3156_ = lean_box(v___x_3143_);
lean_inc_ref(v_fst_3139_);
v___f_3157_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed), 18, 8);
lean_closure_set(v___f_3157_, 0, v_fst_3139_);
lean_closure_set(v___f_3157_, 1, v_xs_3146_);
lean_closure_set(v___f_3157_, 2, v_fst_3140_);
lean_closure_set(v___f_3157_, 3, v___x_3141_);
lean_closure_set(v___f_3157_, 4, v_fst_3142_);
lean_closure_set(v___f_3157_, 5, v___x_3156_);
lean_closure_set(v___f_3157_, 6, v___x_3144_);
lean_closure_set(v___f_3157_, 7, v_snd_3145_);
v___x_3158_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_3159_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3158_, v_fst_3139_, v___f_3157_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed(lean_object** _args){
lean_object* v_fst_3160_ = _args[0];
lean_object* v_fst_3161_ = _args[1];
lean_object* v___x_3162_ = _args[2];
lean_object* v_fst_3163_ = _args[3];
lean_object* v___x_3164_ = _args[4];
lean_object* v___x_3165_ = _args[5];
lean_object* v_snd_3166_ = _args[6];
lean_object* v_xs_3167_ = _args[7];
lean_object* v___y_3168_ = _args[8];
lean_object* v___y_3169_ = _args[9];
lean_object* v___y_3170_ = _args[10];
lean_object* v___y_3171_ = _args[11];
lean_object* v___y_3172_ = _args[12];
lean_object* v___y_3173_ = _args[13];
lean_object* v___y_3174_ = _args[14];
lean_object* v___y_3175_ = _args[15];
lean_object* v___y_3176_ = _args[16];
_start:
{
uint8_t v___x_78060__boxed_3177_; lean_object* v_res_3178_; 
v___x_78060__boxed_3177_ = lean_unbox(v___x_3164_);
v_res_3178_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(v_fst_3160_, v_fst_3161_, v___x_3162_, v_fst_3163_, v___x_78060__boxed_3177_, v___x_3165_, v_snd_3166_, v_xs_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(lean_object* v_as_3179_, size_t v_sz_3180_, size_t v_i_3181_, lean_object* v_b_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
uint8_t v___x_3188_; 
v___x_3188_ = lean_usize_dec_lt(v_i_3181_, v_sz_3180_);
if (v___x_3188_ == 0)
{
lean_object* v___x_3189_; 
v___x_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3189_, 0, v_b_3182_);
return v___x_3189_;
}
else
{
lean_object* v___x_3190_; lean_object* v_a_3191_; lean_object* v___x_3192_; 
v___x_3190_ = lean_box(1);
v_a_3191_ = lean_array_uget_borrowed(v_as_3179_, v_i_3181_);
lean_inc(v_a_3191_);
v___x_3192_ = l_Lean_PrettyPrinter_delab(v_a_3191_, v___x_3190_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3194_; size_t v___x_3195_; size_t v___x_3196_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
lean_inc(v_a_3193_);
lean_dec_ref_known(v___x_3192_, 1);
v___x_3194_ = lean_array_push(v_b_3182_, v_a_3193_);
v___x_3195_ = ((size_t)1ULL);
v___x_3196_ = lean_usize_add(v_i_3181_, v___x_3195_);
v_i_3181_ = v___x_3196_;
v_b_3182_ = v___x_3194_;
goto _start;
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_dec_ref(v_b_3182_);
v_a_3198_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3192_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3192_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg___boxed(lean_object* v_as_3206_, lean_object* v_sz_3207_, lean_object* v_i_3208_, lean_object* v_b_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
size_t v_sz_boxed_3215_; size_t v_i_boxed_3216_; lean_object* v_res_3217_; 
v_sz_boxed_3215_ = lean_unbox_usize(v_sz_3207_);
lean_dec(v_sz_3207_);
v_i_boxed_3216_ = lean_unbox_usize(v_i_3208_);
lean_dec(v_i_3208_);
v_res_3217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_3206_, v_sz_boxed_3215_, v_i_boxed_3216_, v_b_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec_ref(v_as_3206_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(lean_object* v_xs_3238_, lean_object* v_fst_3239_, lean_object* v_snd_3240_, lean_object* v___x_3241_, lean_object* v___x_3242_, lean_object* v___x_3243_, lean_object* v___x_3244_, lean_object* v___x_3245_, lean_object* v___x_3246_, lean_object* v___x_3247_, lean_object* v___x_3248_, uint8_t v___x_3249_, lean_object* v_letMuts_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3260_ = lean_unsigned_to_nat(2u);
v___x_3261_ = lean_mk_empty_array_with_capacity(v___x_3260_);
v___x_3262_ = lean_array_push(v___x_3261_, v_xs_3238_);
v___x_3263_ = lean_array_push(v___x_3262_, v_letMuts_3250_);
v___x_3264_ = l_Lean_Expr_beta(v_fst_3239_, v___x_3263_);
v___x_3265_ = lean_box(1);
v___x_3266_ = l_Lean_PrettyPrinter_delab(v___x_3264_, v___x_3265_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3406_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3269_ = v___x_3266_;
v_isShared_3270_ = v_isSharedCheck_3406_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3266_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3406_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
uint8_t v___y_3272_; lean_object* v_points_3309_; lean_object* v_default_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3405_; 
v_points_3309_ = lean_ctor_get(v_snd_3240_, 0);
v_default_3310_ = lean_ctor_get(v_snd_3240_, 1);
v_isSharedCheck_3405_ = !lean_is_exclusive(v_snd_3240_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3312_ = v_snd_3240_;
v_isShared_3313_ = v_isSharedCheck_3405_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_default_3310_);
lean_inc(v_points_3309_);
lean_dec(v_snd_3240_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3405_;
goto v_resetjp_3311_;
}
v___jp_3271_:
{
lean_object* v_toCold_3273_; lean_object* v_ref_3274_; lean_object* v_quotContext_3275_; lean_object* v_currMacroScope_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3307_; 
v_toCold_3273_ = lean_ctor_get(v___y_3257_, 0);
v_ref_3274_ = lean_ctor_get(v___y_3257_, 2);
v_quotContext_3275_ = lean_ctor_get(v_toCold_3273_, 8);
v_currMacroScope_3276_ = lean_ctor_get(v_toCold_3273_, 9);
v___x_3277_ = l_Lean_SourceInfo_fromRef(v_ref_3274_, v___y_3272_);
v___x_3278_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_3279_ = l_Lean_Name_mkStr3(v___x_3247_, v___x_3248_, v___x_3278_);
v___x_3280_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_3281_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3277_, 11);
v___x_3282_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3277_);
lean_ctor_set(v___x_3282_, 1, v___x_3280_);
lean_ctor_set(v___x_3282_, 2, v___x_3281_);
v___x_3283_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_3284_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3277_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
v___x_3285_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3286_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3287_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_3288_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3277_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = l_String_toRawSubstring_x27(v___x_3241_);
lean_inc_n(v_currMacroScope_3276_, 2);
lean_inc_n(v_quotContext_3275_, 2);
v___x_3290_ = l_Lean_addMacroScope(v_quotContext_3275_, v___x_3242_, v_currMacroScope_3276_);
v___x_3291_ = lean_box(0);
v___x_3292_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3277_);
lean_ctor_set(v___x_3292_, 1, v___x_3289_);
lean_ctor_set(v___x_3292_, 2, v___x_3290_);
lean_ctor_set(v___x_3292_, 3, v___x_3291_);
v___x_3293_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3277_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
v___x_3295_ = l_String_toRawSubstring_x27(v___x_3243_);
v___x_3296_ = l_Lean_addMacroScope(v_quotContext_3275_, v___x_3244_, v_currMacroScope_3276_);
v___x_3297_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3277_);
lean_ctor_set(v___x_3297_, 1, v___x_3295_);
lean_ctor_set(v___x_3297_, 2, v___x_3296_);
lean_ctor_set(v___x_3297_, 3, v___x_3291_);
v___x_3298_ = l_Lean_Syntax_node3(v___x_3277_, v___x_3285_, v___x_3292_, v___x_3294_, v___x_3297_);
v___x_3299_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3300_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3277_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v___x_3301_ = l_Lean_Syntax_node3(v___x_3277_, v___x_3286_, v___x_3288_, v___x_3298_, v___x_3300_);
v___x_3302_ = l_Lean_Syntax_node1(v___x_3277_, v___x_3285_, v___x_3301_);
v___x_3303_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3277_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = l_Lean_Syntax_node5(v___x_3277_, v___x_3279_, v___x_3282_, v___x_3284_, v___x_3302_, v___x_3304_, v_a_3267_);
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 0, v___x_3305_);
v___x_3307_ = v___x_3269_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v___x_3305_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
v_resetjp_3311_:
{
uint8_t v___y_3315_; lean_object* v___x_3366_; uint8_t v___x_3367_; 
v___x_3366_ = lean_array_get_size(v_points_3309_);
v___x_3367_ = lean_nat_dec_eq(v___x_3366_, v___x_3246_);
if (v___x_3367_ == 0)
{
lean_del_object(v___x_3269_);
lean_dec_ref(v___x_3248_);
lean_dec_ref(v___x_3247_);
v___y_3315_ = v___x_3367_;
goto v___jp_3314_;
}
else
{
if (lean_obj_tag(v_default_3310_) == 3)
{
uint8_t v___x_3368_; 
lean_del_object(v___x_3269_);
lean_dec_ref(v___x_3248_);
lean_dec_ref(v___x_3247_);
v___x_3368_ = 0;
v___y_3315_ = v___x_3368_;
goto v___jp_3314_;
}
else
{
lean_del_object(v___x_3312_);
lean_dec_ref(v_points_3309_);
if (lean_obj_tag(v_default_3310_) == 2)
{
if (v___x_3249_ == 0)
{
v___y_3272_ = v___x_3249_;
goto v___jp_3271_;
}
else
{
lean_object* v_toCold_3369_; lean_object* v_ref_3370_; lean_object* v_quotContext_3371_; lean_object* v_currMacroScope_3372_; uint8_t v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_del_object(v___x_3269_);
v_toCold_3369_ = lean_ctor_get(v___y_3257_, 0);
v_ref_3370_ = lean_ctor_get(v___y_3257_, 2);
v_quotContext_3371_ = lean_ctor_get(v_toCold_3369_, 8);
v_currMacroScope_3372_ = lean_ctor_get(v_toCold_3369_, 9);
v___x_3373_ = 0;
v___x_3374_ = l_Lean_SourceInfo_fromRef(v_ref_3370_, v___x_3373_);
v___x_3375_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__9));
v___x_3376_ = l_Lean_Name_mkStr3(v___x_3247_, v___x_3248_, v___x_3375_);
v___x_3377_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_3378_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3374_, 11);
v___x_3379_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3374_);
lean_ctor_set(v___x_3379_, 1, v___x_3377_);
lean_ctor_set(v___x_3379_, 2, v___x_3378_);
v___x_3380_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__10));
v___x_3381_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3374_);
lean_ctor_set(v___x_3381_, 1, v___x_3380_);
v___x_3382_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3383_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3384_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_3385_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3374_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v___x_3386_ = l_String_toRawSubstring_x27(v___x_3241_);
lean_inc_n(v_currMacroScope_3372_, 2);
lean_inc_n(v_quotContext_3371_, 2);
v___x_3387_ = l_Lean_addMacroScope(v_quotContext_3371_, v___x_3242_, v_currMacroScope_3372_);
v___x_3388_ = lean_box(0);
v___x_3389_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3374_);
lean_ctor_set(v___x_3389_, 1, v___x_3386_);
lean_ctor_set(v___x_3389_, 2, v___x_3387_);
lean_ctor_set(v___x_3389_, 3, v___x_3388_);
v___x_3390_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3391_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3374_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
v___x_3392_ = l_String_toRawSubstring_x27(v___x_3243_);
v___x_3393_ = l_Lean_addMacroScope(v_quotContext_3371_, v___x_3244_, v_currMacroScope_3372_);
v___x_3394_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3374_);
lean_ctor_set(v___x_3394_, 1, v___x_3392_);
lean_ctor_set(v___x_3394_, 2, v___x_3393_);
lean_ctor_set(v___x_3394_, 3, v___x_3388_);
v___x_3395_ = l_Lean_Syntax_node3(v___x_3374_, v___x_3382_, v___x_3389_, v___x_3391_, v___x_3394_);
v___x_3396_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3397_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3374_);
lean_ctor_set(v___x_3397_, 1, v___x_3396_);
v___x_3398_ = l_Lean_Syntax_node3(v___x_3374_, v___x_3383_, v___x_3385_, v___x_3395_, v___x_3397_);
v___x_3399_ = l_Lean_Syntax_node1(v___x_3374_, v___x_3382_, v___x_3398_);
v___x_3400_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3374_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
v___x_3402_ = l_Lean_Syntax_node5(v___x_3374_, v___x_3376_, v___x_3379_, v___x_3381_, v___x_3399_, v___x_3401_, v_a_3267_);
v___x_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
return v___x_3403_;
}
}
else
{
uint8_t v___x_3404_; 
lean_dec(v_default_3310_);
v___x_3404_ = 0;
v___y_3272_ = v___x_3404_;
goto v___jp_3271_;
}
}
}
v___jp_3314_:
{
lean_object* v_toCold_3316_; lean_object* v_ref_3317_; lean_object* v_quotContext_3318_; lean_object* v_currMacroScope_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3324_; 
v_toCold_3316_ = lean_ctor_get(v___y_3257_, 0);
v_ref_3317_ = lean_ctor_get(v___y_3257_, 2);
v_quotContext_3318_ = lean_ctor_get(v_toCold_3316_, 8);
v_currMacroScope_3319_ = lean_ctor_get(v_toCold_3316_, 9);
v___x_3320_ = l_Lean_SourceInfo_fromRef(v_ref_3317_, v___y_3315_);
v___x_3321_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3322_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc(v___x_3320_);
if (v_isShared_3313_ == 0)
{
lean_ctor_set_tag(v___x_3312_, 2);
lean_ctor_set(v___x_3312_, 1, v___x_3321_);
lean_ctor_set(v___x_3312_, 0, v___x_3320_);
v___x_3324_ = v___x_3312_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3320_);
lean_ctor_set(v_reuseFailAlloc_3365_, 1, v___x_3321_);
v___x_3324_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; size_t v_sz_3352_; size_t v___x_3353_; lean_object* v___x_3354_; 
v___x_3325_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3326_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3327_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3328_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
lean_inc_n(v___x_3320_, 11);
v___x_3329_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3320_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
v___x_3330_ = l_String_toRawSubstring_x27(v___x_3241_);
lean_inc_n(v_currMacroScope_3319_, 2);
lean_inc_n(v_quotContext_3318_, 2);
v___x_3331_ = l_Lean_addMacroScope(v_quotContext_3318_, v___x_3242_, v_currMacroScope_3319_);
v___x_3332_ = lean_box(0);
v___x_3333_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3320_);
lean_ctor_set(v___x_3333_, 1, v___x_3330_);
lean_ctor_set(v___x_3333_, 2, v___x_3331_);
lean_ctor_set(v___x_3333_, 3, v___x_3332_);
v___x_3334_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3335_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3320_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v___x_3336_ = l_String_toRawSubstring_x27(v___x_3243_);
v___x_3337_ = l_Lean_addMacroScope(v_quotContext_3318_, v___x_3244_, v_currMacroScope_3319_);
v___x_3338_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3320_);
lean_ctor_set(v___x_3338_, 1, v___x_3336_);
lean_ctor_set(v___x_3338_, 2, v___x_3337_);
lean_ctor_set(v___x_3338_, 3, v___x_3332_);
v___x_3339_ = l_Lean_Syntax_node3(v___x_3320_, v___x_3326_, v___x_3333_, v___x_3335_, v___x_3338_);
v___x_3340_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3341_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3320_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
v___x_3342_ = l_Lean_Syntax_node3(v___x_3320_, v___x_3327_, v___x_3329_, v___x_3339_, v___x_3341_);
v___x_3343_ = l_Lean_Syntax_node1(v___x_3320_, v___x_3326_, v___x_3342_);
v___x_3344_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3345_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3320_);
lean_ctor_set(v___x_3345_, 1, v___x_3326_);
lean_ctor_set(v___x_3345_, 2, v___x_3344_);
v___x_3346_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3320_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
v___x_3348_ = l_Lean_Syntax_node4(v___x_3320_, v___x_3325_, v___x_3343_, v___x_3345_, v___x_3347_, v_a_3267_);
v___x_3349_ = l_Lean_Syntax_node2(v___x_3320_, v___x_3322_, v___x_3324_, v___x_3348_);
v___x_3350_ = lean_mk_empty_array_with_capacity(v___x_3245_);
v___x_3351_ = lean_array_push(v___x_3350_, v___x_3349_);
v_sz_3352_ = lean_array_size(v_points_3309_);
v___x_3353_ = ((size_t)0ULL);
v___x_3354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_points_3309_, v_sz_3352_, v___x_3353_, v___x_3351_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
lean_dec_ref(v_points_3309_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_a_3355_; lean_object* v___x_3356_; 
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_a_3355_);
lean_dec_ref_known(v___x_3354_, 1);
v___x_3356_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3355_, v_default_3310_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
lean_dec(v_a_3355_);
return v___x_3356_;
}
else
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
lean_dec(v_default_3310_);
v_a_3357_ = lean_ctor_get(v___x_3354_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___x_3354_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3354_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
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
lean_dec_ref(v___x_3248_);
lean_dec_ref(v___x_3247_);
lean_dec(v___x_3244_);
lean_dec_ref(v___x_3243_);
lean_dec(v___x_3242_);
lean_dec_ref(v___x_3241_);
lean_dec_ref(v_snd_3240_);
return v___x_3266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed(lean_object** _args){
lean_object* v_xs_3407_ = _args[0];
lean_object* v_fst_3408_ = _args[1];
lean_object* v_snd_3409_ = _args[2];
lean_object* v___x_3410_ = _args[3];
lean_object* v___x_3411_ = _args[4];
lean_object* v___x_3412_ = _args[5];
lean_object* v___x_3413_ = _args[6];
lean_object* v___x_3414_ = _args[7];
lean_object* v___x_3415_ = _args[8];
lean_object* v___x_3416_ = _args[9];
lean_object* v___x_3417_ = _args[10];
lean_object* v___x_3418_ = _args[11];
lean_object* v_letMuts_3419_ = _args[12];
lean_object* v___y_3420_ = _args[13];
lean_object* v___y_3421_ = _args[14];
lean_object* v___y_3422_ = _args[15];
lean_object* v___y_3423_ = _args[16];
lean_object* v___y_3424_ = _args[17];
lean_object* v___y_3425_ = _args[18];
lean_object* v___y_3426_ = _args[19];
lean_object* v___y_3427_ = _args[20];
lean_object* v___y_3428_ = _args[21];
_start:
{
uint8_t v___x_78267__boxed_3429_; lean_object* v_res_3430_; 
v___x_78267__boxed_3429_ = lean_unbox(v___x_3418_);
v_res_3430_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(v_xs_3407_, v_fst_3408_, v_snd_3409_, v___x_3410_, v___x_3411_, v___x_3412_, v___x_3413_, v___x_3414_, v___x_3415_, v___x_3416_, v___x_3417_, v___x_78267__boxed_3429_, v_letMuts_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___x_3415_);
lean_dec(v___x_3414_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(lean_object* v_fst_3431_, lean_object* v_snd_3432_, lean_object* v___x_3433_, lean_object* v___x_3434_, lean_object* v___x_3435_, lean_object* v___x_3436_, lean_object* v___x_3437_, lean_object* v___x_3438_, uint8_t v___x_3439_, lean_object* v_arg_3440_, lean_object* v_xs_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___f_3454_; lean_object* v___x_3455_; 
v___x_3451_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3452_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3453_ = lean_box(v___x_3439_);
v___f_3454_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed), 22, 12);
lean_closure_set(v___f_3454_, 0, v_xs_3441_);
lean_closure_set(v___f_3454_, 1, v_fst_3431_);
lean_closure_set(v___f_3454_, 2, v_snd_3432_);
lean_closure_set(v___f_3454_, 3, v___x_3433_);
lean_closure_set(v___f_3454_, 4, v___x_3434_);
lean_closure_set(v___f_3454_, 5, v___x_3451_);
lean_closure_set(v___f_3454_, 6, v___x_3452_);
lean_closure_set(v___f_3454_, 7, v___x_3435_);
lean_closure_set(v___f_3454_, 8, v___x_3436_);
lean_closure_set(v___f_3454_, 9, v___x_3437_);
lean_closure_set(v___f_3454_, 10, v___x_3438_);
lean_closure_set(v___f_3454_, 11, v___x_3453_);
v___x_3455_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3452_, v_arg_3440_, v___f_3454_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed(lean_object** _args){
lean_object* v_fst_3456_ = _args[0];
lean_object* v_snd_3457_ = _args[1];
lean_object* v___x_3458_ = _args[2];
lean_object* v___x_3459_ = _args[3];
lean_object* v___x_3460_ = _args[4];
lean_object* v___x_3461_ = _args[5];
lean_object* v___x_3462_ = _args[6];
lean_object* v___x_3463_ = _args[7];
lean_object* v___x_3464_ = _args[8];
lean_object* v_arg_3465_ = _args[9];
lean_object* v_xs_3466_ = _args[10];
lean_object* v___y_3467_ = _args[11];
lean_object* v___y_3468_ = _args[12];
lean_object* v___y_3469_ = _args[13];
lean_object* v___y_3470_ = _args[14];
lean_object* v___y_3471_ = _args[15];
lean_object* v___y_3472_ = _args[16];
lean_object* v___y_3473_ = _args[17];
lean_object* v___y_3474_ = _args[18];
lean_object* v___y_3475_ = _args[19];
_start:
{
uint8_t v___x_78614__boxed_3476_; lean_object* v_res_3477_; 
v___x_78614__boxed_3476_ = lean_unbox(v___x_3464_);
v_res_3477_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(v_fst_3456_, v_snd_3457_, v___x_3458_, v___x_3459_, v___x_3460_, v___x_3461_, v___x_3462_, v___x_3463_, v___x_78614__boxed_3476_, v_arg_3465_, v_xs_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(lean_object* v_as_3478_, size_t v_sz_3479_, size_t v_i_3480_, lean_object* v_b_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
uint8_t v___x_3487_; 
v___x_3487_ = lean_usize_dec_lt(v_i_3480_, v_sz_3479_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; 
v___x_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3488_, 0, v_b_3481_);
return v___x_3488_;
}
else
{
lean_object* v_a_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v_a_3489_ = lean_array_uget_borrowed(v_as_3478_, v_i_3480_);
v___x_3490_ = lean_box(1);
lean_inc(v_a_3489_);
v___x_3491_ = l_Lean_PrettyPrinter_delab(v_a_3489_, v___x_3490_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3493_; size_t v___x_3494_; size_t v___x_3495_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref_known(v___x_3491_, 1);
v___x_3493_ = lean_array_push(v_b_3481_, v_a_3492_);
v___x_3494_ = ((size_t)1ULL);
v___x_3495_ = lean_usize_add(v_i_3480_, v___x_3494_);
v_i_3480_ = v___x_3495_;
v_b_3481_ = v___x_3493_;
goto _start;
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_dec_ref(v_b_3481_);
v_a_3497_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3491_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3491_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg___boxed(lean_object* v_as_3505_, lean_object* v_sz_3506_, lean_object* v_i_3507_, lean_object* v_b_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
size_t v_sz_boxed_3514_; size_t v_i_boxed_3515_; lean_object* v_res_3516_; 
v_sz_boxed_3514_ = lean_unbox_usize(v_sz_3506_);
lean_dec(v_sz_3506_);
v_i_boxed_3515_ = lean_unbox_usize(v_i_3507_);
lean_dec(v_i_3507_);
v_res_3516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_3505_, v_sz_boxed_3514_, v_i_boxed_3515_, v_b_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v_as_3505_);
return v_res_3516_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3(void){
_start:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3524_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__2));
v___x_3525_ = l_String_toRawSubstring_x27(v___x_3524_);
return v___x_3525_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__8));
v___x_3536_ = l_String_toRawSubstring_x27(v___x_3535_);
return v___x_3536_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12(void){
_start:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3540_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__0));
v___x_3541_ = l_String_toRawSubstring_x27(v___x_3540_);
return v___x_3541_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13(void){
_start:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3543_ = l_String_toRawSubstring_x27(v___x_3542_);
return v___x_3543_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16(void){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3546_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__15));
v___x_3547_ = l_String_toRawSubstring_x27(v___x_3546_);
return v___x_3547_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19(void){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3551_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__18));
v___x_3552_ = l_String_toRawSubstring_x27(v___x_3551_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(lean_object* v___x_3562_, lean_object* v___x_3563_, lean_object* v___f_3564_, lean_object* v_a_3565_, lean_object* v_inv_3566_, lean_object* v_arg_3567_, lean_object* v___x_3568_, uint8_t v___x_3569_, lean_object* v___x_3570_, lean_object* v___x_3571_, lean_object* v___x_3572_, lean_object* v___x_3573_, lean_object* v___x_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
lean_object* v_a_3585_; lean_object* v___y_3589_; lean_object* v___x_3591_; 
lean_inc_ref(v___x_3563_);
lean_inc(v___x_3562_);
v___x_3591_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3562_, v___x_3563_, v___f_3564_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v_a_3592_; lean_object* v___x_3593_; 
v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_a_3592_);
lean_dec_ref_known(v___x_3591_, 1);
v___x_3593_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(v_a_3565_, v_inv_3566_, v_arg_3567_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_a_3594_; 
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_a_3594_);
lean_dec_ref_known(v___x_3593_, 1);
if (lean_obj_tag(v_a_3594_) == 1)
{
lean_object* v_val_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_4080_; 
lean_dec_ref(v_arg_3567_);
v_val_3595_ = lean_ctor_get(v_a_3594_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v_a_3594_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_3597_ = v_a_3594_;
v_isShared_3598_ = v_isSharedCheck_4080_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_val_3595_);
lean_dec(v_a_3594_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_4080_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
if (lean_obj_tag(v_a_3592_) == 1)
{
lean_object* v_val_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_4002_; 
lean_del_object(v___x_3597_);
v_val_3599_ = lean_ctor_get(v_a_3592_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v_a_3592_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3601_ = v_a_3592_;
v_isShared_3602_ = v_isSharedCheck_4002_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_val_3599_);
lean_dec(v_a_3592_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_4002_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v_snd_3603_; lean_object* v_fst_3604_; lean_object* v_snd_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_4001_; 
v_snd_3603_ = lean_ctor_get(v_val_3599_, 1);
lean_inc(v_snd_3603_);
v_fst_3604_ = lean_ctor_get(v_val_3595_, 0);
v_snd_3605_ = lean_ctor_get(v_val_3595_, 1);
v_isSharedCheck_4001_ = !lean_is_exclusive(v_val_3595_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3607_ = v_val_3595_;
v_isShared_3608_ = v_isSharedCheck_4001_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_snd_3605_);
lean_inc(v_fst_3604_);
lean_dec(v_val_3595_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_4001_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v_fst_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3999_; 
v_fst_3609_ = lean_ctor_get(v_val_3599_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v_val_3599_);
if (v_isSharedCheck_3999_ == 0)
{
lean_object* v_unused_4000_; 
v_unused_4000_ = lean_ctor_get(v_val_3599_, 1);
lean_dec(v_unused_4000_);
v___x_3611_ = v_val_3599_;
v_isShared_3612_ = v_isSharedCheck_3999_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_fst_3609_);
lean_dec(v_val_3599_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3999_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v_fst_3613_; lean_object* v_snd_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3998_; 
v_fst_3613_ = lean_ctor_get(v_snd_3603_, 0);
v_snd_3614_ = lean_ctor_get(v_snd_3603_, 1);
v_isSharedCheck_3998_ = !lean_is_exclusive(v_snd_3603_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3616_ = v_snd_3603_;
v_isShared_3617_ = v_isSharedCheck_3998_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_snd_3614_);
lean_inc(v_fst_3613_);
lean_dec(v_snd_3603_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3998_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3618_; lean_object* v___f_3619_; lean_object* v___x_3620_; 
v___x_3618_ = lean_box(v___x_3569_);
lean_inc(v___x_3570_);
v___f_3619_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed), 17, 7);
lean_closure_set(v___f_3619_, 0, v_fst_3604_);
lean_closure_set(v___f_3619_, 1, v_fst_3609_);
lean_closure_set(v___f_3619_, 2, v___x_3568_);
lean_closure_set(v___f_3619_, 3, v_fst_3613_);
lean_closure_set(v___f_3619_, 4, v___x_3618_);
lean_closure_set(v___f_3619_, 5, v___x_3570_);
lean_closure_set(v___f_3619_, 6, v_snd_3605_);
lean_inc(v___x_3562_);
v___x_3620_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3562_, v___x_3563_, v___f_3619_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; lean_object* v_fst_3622_; lean_object* v_snd_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3989_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_a_3621_);
lean_dec_ref_known(v___x_3620_, 1);
v_fst_3622_ = lean_ctor_get(v_a_3621_, 0);
v_snd_3623_ = lean_ctor_get(v_a_3621_, 1);
v_isSharedCheck_3989_ = !lean_is_exclusive(v_a_3621_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3625_ = v_a_3621_;
v_isShared_3626_ = v_isSharedCheck_3989_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_snd_3623_);
lean_inc(v_fst_3622_);
lean_dec(v_a_3621_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3989_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v_points_3627_; lean_object* v_default_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3988_; 
v_points_3627_ = lean_ctor_get(v_snd_3614_, 0);
v_default_3628_ = lean_ctor_get(v_snd_3614_, 1);
v_isSharedCheck_3988_ = !lean_is_exclusive(v_snd_3614_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3630_ = v_snd_3614_;
v_isShared_3631_ = v_isSharedCheck_3988_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_default_3628_);
lean_inc(v_points_3627_);
lean_dec(v_snd_3614_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3988_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3632_; uint8_t v___x_3633_; 
v___x_3632_ = lean_array_get_size(v_points_3627_);
v___x_3633_ = lean_nat_dec_eq(v___x_3632_, v___x_3570_);
if (v___x_3633_ == 0)
{
lean_object* v___x_3634_; size_t v_sz_3635_; size_t v___x_3636_; lean_object* v___x_3637_; 
lean_del_object(v___x_3601_);
v___x_3634_ = lean_mk_empty_array_with_capacity(v___x_3570_);
lean_dec(v___x_3570_);
v_sz_3635_ = lean_array_size(v_points_3627_);
v___x_3636_ = ((size_t)0ULL);
v___x_3637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_points_3627_, v_sz_3635_, v___x_3636_, v___x_3634_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
lean_dec_ref(v_points_3627_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; lean_object* v___x_3639_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
lean_dec_ref_known(v___x_3637_, 1);
v___x_3639_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3638_, v_default_3628_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
lean_dec(v_a_3638_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_toCold_3640_; lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3723_; 
v_toCold_3640_ = lean_ctor_get(v___y_3581_, 0);
lean_inc_ref(v_toCold_3640_);
v_a_3641_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3643_ = v___x_3639_;
v_isShared_3644_ = v_isSharedCheck_3723_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3639_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3723_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v_ref_3645_; lean_object* v_quotContext_3646_; lean_object* v_currMacroScope_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3657_; 
v_ref_3645_ = lean_ctor_get(v___y_3581_, 2);
lean_inc(v_ref_3645_);
lean_dec_ref(v___y_3581_);
v_quotContext_3646_ = lean_ctor_get(v_toCold_3640_, 8);
lean_inc_n(v_quotContext_3646_, 2);
v_currMacroScope_3647_ = lean_ctor_get(v_toCold_3640_, 9);
lean_inc_n(v_currMacroScope_3647_, 2);
lean_dec_ref(v_toCold_3640_);
v___x_3648_ = l_Lean_SourceInfo_fromRef(v_ref_3645_, v___x_3633_);
lean_dec(v_ref_3645_);
v___x_3649_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3650_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3651_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3571_);
v___x_3652_ = l_Lean_Name_mkStr2(v___x_3571_, v___x_3651_);
v___x_3653_ = l_Lean_addMacroScope(v_quotContext_3646_, v___x_3652_, v_currMacroScope_3647_);
v___x_3654_ = l_Lean_Name_mkStr4(v___x_3572_, v___x_3573_, v___x_3571_, v___x_3651_);
v___x_3655_ = lean_box(0);
lean_inc(v___x_3654_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 1);
lean_ctor_set(v___x_3630_, 1, v___x_3655_);
lean_ctor_set(v___x_3630_, 0, v___x_3654_);
v___x_3657_ = v___x_3630_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3654_);
lean_ctor_set(v_reuseFailAlloc_3722_, 1, v___x_3655_);
v___x_3657_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
lean_object* v___x_3659_; 
if (v_isShared_3644_ == 0)
{
lean_ctor_set(v___x_3643_, 0, v___x_3654_);
v___x_3659_ = v___x_3643_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3654_);
v___x_3659_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
lean_object* v___x_3661_; 
if (v_isShared_3626_ == 0)
{
lean_ctor_set_tag(v___x_3625_, 1);
lean_ctor_set(v___x_3625_, 1, v___x_3655_);
lean_ctor_set(v___x_3625_, 0, v___x_3659_);
v___x_3661_ = v___x_3625_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v___x_3659_);
lean_ctor_set(v_reuseFailAlloc_3720_, 1, v___x_3655_);
v___x_3661_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
lean_object* v___x_3663_; 
if (v_isShared_3617_ == 0)
{
lean_ctor_set_tag(v___x_3616_, 1);
lean_ctor_set(v___x_3616_, 1, v___x_3661_);
lean_ctor_set(v___x_3616_, 0, v___x_3657_);
v___x_3663_ = v___x_3616_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3657_);
lean_ctor_set(v_reuseFailAlloc_3719_, 1, v___x_3661_);
v___x_3663_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3669_; 
lean_inc_n(v___x_3648_, 2);
v___x_3664_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3648_);
lean_ctor_set(v___x_3664_, 1, v___x_3650_);
lean_ctor_set(v___x_3664_, 2, v___x_3653_);
lean_ctor_set(v___x_3664_, 3, v___x_3663_);
v___x_3665_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3666_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3667_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3612_ == 0)
{
lean_ctor_set_tag(v___x_3611_, 2);
lean_ctor_set(v___x_3611_, 1, v___x_3667_);
lean_ctor_set(v___x_3611_, 0, v___x_3648_);
v___x_3669_ = v___x_3611_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3648_);
lean_ctor_set(v_reuseFailAlloc_3718_, 1, v___x_3667_);
v___x_3669_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3676_; 
v___x_3670_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3671_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3647_);
lean_inc(v_quotContext_3646_);
v___x_3672_ = l_Lean_addMacroScope(v_quotContext_3646_, v___x_3671_, v_currMacroScope_3647_);
lean_inc_n(v___x_3648_, 2);
v___x_3673_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3648_);
lean_ctor_set(v___x_3673_, 1, v___x_3670_);
lean_ctor_set(v___x_3673_, 2, v___x_3672_);
lean_ctor_set(v___x_3673_, 3, v___x_3655_);
v___x_3674_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3608_ == 0)
{
lean_ctor_set_tag(v___x_3607_, 2);
lean_ctor_set(v___x_3607_, 1, v___x_3674_);
lean_ctor_set(v___x_3607_, 0, v___x_3648_);
v___x_3676_ = v___x_3607_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3648_);
lean_ctor_set(v_reuseFailAlloc_3717_, 1, v___x_3674_);
v___x_3676_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3677_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3678_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3648_, 19);
v___x_3679_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3648_);
lean_ctor_set(v___x_3679_, 1, v___x_3677_);
v___x_3680_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3681_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3682_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3647_, 4);
lean_inc_n(v_quotContext_3646_, 4);
v___x_3683_ = l_Lean_addMacroScope(v_quotContext_3646_, v___x_3682_, v_currMacroScope_3647_);
v___x_3684_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3684_, 0, v___x_3648_);
lean_ctor_set(v___x_3684_, 1, v___x_3681_);
lean_ctor_set(v___x_3684_, 2, v___x_3683_);
lean_ctor_set(v___x_3684_, 3, v___x_3655_);
v___x_3685_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3686_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3687_ = l_Lean_addMacroScope(v_quotContext_3646_, v___x_3686_, v_currMacroScope_3647_);
v___x_3688_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3648_);
lean_ctor_set(v___x_3688_, 1, v___x_3685_);
lean_ctor_set(v___x_3688_, 2, v___x_3687_);
lean_ctor_set(v___x_3688_, 3, v___x_3655_);
lean_inc_ref(v___x_3688_);
v___x_3689_ = l_Lean_Syntax_node2(v___x_3648_, v___x_3665_, v___x_3684_, v___x_3688_);
v___x_3690_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3691_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3648_);
lean_ctor_set(v___x_3691_, 1, v___x_3665_);
lean_ctor_set(v___x_3691_, 2, v___x_3690_);
v___x_3692_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3693_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3648_);
lean_ctor_set(v___x_3693_, 1, v___x_3692_);
lean_inc_ref(v___x_3693_);
lean_inc_ref(v___x_3691_);
v___x_3694_ = l_Lean_Syntax_node4(v___x_3648_, v___x_3680_, v___x_3689_, v___x_3691_, v___x_3693_, v_snd_3623_);
lean_inc_ref(v___x_3679_);
v___x_3695_ = l_Lean_Syntax_node2(v___x_3648_, v___x_3678_, v___x_3679_, v___x_3694_);
v___x_3696_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3648_);
lean_ctor_set(v___x_3697_, 1, v___x_3696_);
lean_inc_ref_n(v___x_3697_, 2);
lean_inc_ref_n(v___x_3676_, 2);
lean_inc_ref_n(v___x_3669_, 2);
v___x_3698_ = l_Lean_Syntax_node5(v___x_3648_, v___x_3666_, v___x_3669_, v___x_3673_, v___x_3676_, v___x_3695_, v___x_3697_);
v___x_3699_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3700_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3701_ = l_Lean_addMacroScope(v_quotContext_3646_, v___x_3700_, v_currMacroScope_3647_);
v___x_3702_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3648_);
lean_ctor_set(v___x_3702_, 1, v___x_3699_);
lean_ctor_set(v___x_3702_, 2, v___x_3701_);
lean_ctor_set(v___x_3702_, 3, v___x_3655_);
v___x_3703_ = l_String_toRawSubstring_x27(v___x_3574_);
v___x_3704_ = l_Lean_addMacroScope(v_quotContext_3646_, v___x_3562_, v_currMacroScope_3647_);
v___x_3705_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3648_);
lean_ctor_set(v___x_3705_, 1, v___x_3703_);
lean_ctor_set(v___x_3705_, 2, v___x_3704_);
lean_ctor_set(v___x_3705_, 3, v___x_3655_);
v___x_3706_ = l_Lean_Syntax_node2(v___x_3648_, v___x_3665_, v___x_3705_, v___x_3688_);
v___x_3707_ = l_Lean_Syntax_node4(v___x_3648_, v___x_3680_, v___x_3706_, v___x_3691_, v___x_3693_, v_fst_3622_);
v___x_3708_ = l_Lean_Syntax_node2(v___x_3648_, v___x_3678_, v___x_3679_, v___x_3707_);
v___x_3709_ = l_Lean_Syntax_node5(v___x_3648_, v___x_3666_, v___x_3669_, v___x_3702_, v___x_3676_, v___x_3708_, v___x_3697_);
v___x_3710_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3711_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3712_ = l_Lean_addMacroScope(v_quotContext_3646_, v___x_3711_, v_currMacroScope_3647_);
v___x_3713_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3648_);
lean_ctor_set(v___x_3713_, 1, v___x_3710_);
lean_ctor_set(v___x_3713_, 2, v___x_3712_);
lean_ctor_set(v___x_3713_, 3, v___x_3655_);
v___x_3714_ = l_Lean_Syntax_node5(v___x_3648_, v___x_3666_, v___x_3669_, v___x_3713_, v___x_3676_, v_a_3641_, v___x_3697_);
v___x_3715_ = l_Lean_Syntax_node3(v___x_3648_, v___x_3665_, v___x_3698_, v___x_3709_, v___x_3714_);
v___x_3716_ = l_Lean_Syntax_node2(v___x_3648_, v___x_3649_, v___x_3664_, v___x_3715_);
v_a_3585_ = v___x_3716_;
goto v___jp_3584_;
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
lean_del_object(v___x_3630_);
lean_del_object(v___x_3625_);
lean_dec(v_snd_3623_);
lean_dec(v_fst_3622_);
lean_del_object(v___x_3616_);
lean_del_object(v___x_3611_);
lean_del_object(v___x_3607_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v___x_3574_);
lean_dec_ref(v___x_3573_);
lean_dec_ref(v___x_3572_);
lean_dec_ref(v___x_3571_);
lean_dec(v___x_3562_);
v___y_3589_ = v___x_3639_;
goto v___jp_3588_;
}
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
lean_del_object(v___x_3630_);
lean_dec(v_default_3628_);
lean_del_object(v___x_3625_);
lean_dec(v_snd_3623_);
lean_dec(v_fst_3622_);
lean_del_object(v___x_3616_);
lean_del_object(v___x_3611_);
lean_del_object(v___x_3607_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v___x_3574_);
lean_dec_ref(v___x_3573_);
lean_dec_ref(v___x_3572_);
lean_dec_ref(v___x_3571_);
lean_dec(v___x_3562_);
v_a_3724_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3637_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3637_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
else
{
lean_dec_ref(v_points_3627_);
lean_dec(v___x_3570_);
switch(lean_obj_tag(v_default_3628_))
{
case 2:
{
lean_object* v_toCold_3732_; lean_object* v_ref_3733_; lean_object* v_quotContext_3734_; lean_object* v_currMacroScope_3735_; uint8_t v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3746_; 
v_toCold_3732_ = lean_ctor_get(v___y_3581_, 0);
lean_inc_ref(v_toCold_3732_);
v_ref_3733_ = lean_ctor_get(v___y_3581_, 2);
lean_inc(v_ref_3733_);
lean_dec_ref(v___y_3581_);
v_quotContext_3734_ = lean_ctor_get(v_toCold_3732_, 8);
lean_inc_n(v_quotContext_3734_, 2);
v_currMacroScope_3735_ = lean_ctor_get(v_toCold_3732_, 9);
lean_inc_n(v_currMacroScope_3735_, 2);
lean_dec_ref(v_toCold_3732_);
v___x_3736_ = 0;
v___x_3737_ = l_Lean_SourceInfo_fromRef(v_ref_3733_, v___x_3736_);
lean_dec(v_ref_3733_);
v___x_3738_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3739_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3740_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3571_);
v___x_3741_ = l_Lean_Name_mkStr2(v___x_3571_, v___x_3740_);
v___x_3742_ = l_Lean_addMacroScope(v_quotContext_3734_, v___x_3741_, v_currMacroScope_3735_);
lean_inc_ref(v___x_3573_);
lean_inc_ref(v___x_3572_);
v___x_3743_ = l_Lean_Name_mkStr4(v___x_3572_, v___x_3573_, v___x_3571_, v___x_3740_);
v___x_3744_ = lean_box(0);
lean_inc(v___x_3743_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 1);
lean_ctor_set(v___x_3630_, 1, v___x_3744_);
lean_ctor_set(v___x_3630_, 0, v___x_3743_);
v___x_3746_ = v___x_3630_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v___x_3743_);
lean_ctor_set(v_reuseFailAlloc_3822_, 1, v___x_3744_);
v___x_3746_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
lean_object* v___x_3748_; 
if (v_isShared_3602_ == 0)
{
lean_ctor_set_tag(v___x_3601_, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3743_);
v___x_3748_ = v___x_3601_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v___x_3743_);
v___x_3748_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
lean_object* v___x_3750_; 
if (v_isShared_3626_ == 0)
{
lean_ctor_set_tag(v___x_3625_, 1);
lean_ctor_set(v___x_3625_, 1, v___x_3744_);
lean_ctor_set(v___x_3625_, 0, v___x_3748_);
v___x_3750_ = v___x_3625_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3748_);
lean_ctor_set(v_reuseFailAlloc_3820_, 1, v___x_3744_);
v___x_3750_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
lean_object* v___x_3752_; 
if (v_isShared_3617_ == 0)
{
lean_ctor_set_tag(v___x_3616_, 1);
lean_ctor_set(v___x_3616_, 1, v___x_3750_);
lean_ctor_set(v___x_3616_, 0, v___x_3746_);
v___x_3752_ = v___x_3616_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3746_);
lean_ctor_set(v_reuseFailAlloc_3819_, 1, v___x_3750_);
v___x_3752_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3758_; 
lean_inc_n(v___x_3737_, 2);
v___x_3753_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3737_);
lean_ctor_set(v___x_3753_, 1, v___x_3739_);
lean_ctor_set(v___x_3753_, 2, v___x_3742_);
lean_ctor_set(v___x_3753_, 3, v___x_3752_);
v___x_3754_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3755_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3756_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3612_ == 0)
{
lean_ctor_set_tag(v___x_3611_, 2);
lean_ctor_set(v___x_3611_, 1, v___x_3756_);
lean_ctor_set(v___x_3611_, 0, v___x_3737_);
v___x_3758_ = v___x_3611_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v___x_3756_);
v___x_3758_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3765_; 
v___x_3759_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3760_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3735_);
lean_inc(v_quotContext_3734_);
v___x_3761_ = l_Lean_addMacroScope(v_quotContext_3734_, v___x_3760_, v_currMacroScope_3735_);
lean_inc_n(v___x_3737_, 2);
v___x_3762_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3737_);
lean_ctor_set(v___x_3762_, 1, v___x_3759_);
lean_ctor_set(v___x_3762_, 2, v___x_3761_);
lean_ctor_set(v___x_3762_, 3, v___x_3744_);
v___x_3763_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3608_ == 0)
{
lean_ctor_set_tag(v___x_3607_, 2);
lean_ctor_set(v___x_3607_, 1, v___x_3763_);
lean_ctor_set(v___x_3607_, 0, v___x_3737_);
v___x_3765_ = v___x_3607_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3817_, 1, v___x_3763_);
v___x_3765_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v___x_3766_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3767_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3737_, 22);
v___x_3768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3737_);
lean_ctor_set(v___x_3768_, 1, v___x_3766_);
v___x_3769_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3770_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3771_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3735_, 5);
lean_inc_n(v_quotContext_3734_, 5);
v___x_3772_ = l_Lean_addMacroScope(v_quotContext_3734_, v___x_3771_, v_currMacroScope_3735_);
v___x_3773_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3737_);
lean_ctor_set(v___x_3773_, 1, v___x_3770_);
lean_ctor_set(v___x_3773_, 2, v___x_3772_);
lean_ctor_set(v___x_3773_, 3, v___x_3744_);
v___x_3774_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3775_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3776_ = l_Lean_addMacroScope(v_quotContext_3734_, v___x_3775_, v_currMacroScope_3735_);
v___x_3777_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3737_);
lean_ctor_set(v___x_3777_, 1, v___x_3774_);
lean_ctor_set(v___x_3777_, 2, v___x_3776_);
lean_ctor_set(v___x_3777_, 3, v___x_3744_);
lean_inc_ref(v___x_3777_);
v___x_3778_ = l_Lean_Syntax_node2(v___x_3737_, v___x_3754_, v___x_3773_, v___x_3777_);
v___x_3779_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3780_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3737_);
lean_ctor_set(v___x_3780_, 1, v___x_3754_);
lean_ctor_set(v___x_3780_, 2, v___x_3779_);
v___x_3781_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3782_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3737_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
lean_inc_ref(v___x_3782_);
lean_inc_ref(v___x_3780_);
v___x_3783_ = l_Lean_Syntax_node4(v___x_3737_, v___x_3769_, v___x_3778_, v___x_3780_, v___x_3782_, v_snd_3623_);
lean_inc_ref(v___x_3768_);
v___x_3784_ = l_Lean_Syntax_node2(v___x_3737_, v___x_3767_, v___x_3768_, v___x_3783_);
v___x_3785_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3786_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3737_);
lean_ctor_set(v___x_3786_, 1, v___x_3785_);
lean_inc_ref_n(v___x_3786_, 2);
lean_inc_ref_n(v___x_3765_, 2);
lean_inc_ref_n(v___x_3758_, 2);
v___x_3787_ = l_Lean_Syntax_node5(v___x_3737_, v___x_3755_, v___x_3758_, v___x_3762_, v___x_3765_, v___x_3784_, v___x_3786_);
v___x_3788_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3789_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3790_ = l_Lean_addMacroScope(v_quotContext_3734_, v___x_3789_, v_currMacroScope_3735_);
v___x_3791_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3737_);
lean_ctor_set(v___x_3791_, 1, v___x_3788_);
lean_ctor_set(v___x_3791_, 2, v___x_3790_);
lean_ctor_set(v___x_3791_, 3, v___x_3744_);
v___x_3792_ = l_String_toRawSubstring_x27(v___x_3574_);
v___x_3793_ = l_Lean_addMacroScope(v_quotContext_3734_, v___x_3562_, v_currMacroScope_3735_);
v___x_3794_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3737_);
lean_ctor_set(v___x_3794_, 1, v___x_3792_);
lean_ctor_set(v___x_3794_, 2, v___x_3793_);
lean_ctor_set(v___x_3794_, 3, v___x_3744_);
v___x_3795_ = l_Lean_Syntax_node2(v___x_3737_, v___x_3754_, v___x_3794_, v___x_3777_);
v___x_3796_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3797_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3798_ = l_Lean_addMacroScope(v_quotContext_3734_, v___x_3797_, v_currMacroScope_3735_);
v___x_3799_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3737_);
lean_ctor_set(v___x_3799_, 1, v___x_3796_);
lean_ctor_set(v___x_3799_, 2, v___x_3798_);
lean_ctor_set(v___x_3799_, 3, v___x_3744_);
v___x_3800_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30);
v___x_3801_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5));
v___x_3802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4));
v___x_3803_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31));
v___x_3804_ = l_Lean_addMacroScope(v_quotContext_3734_, v___x_3803_, v_currMacroScope_3735_);
v___x_3805_ = l_Lean_Name_mkStr4(v___x_3572_, v___x_3573_, v___x_3801_, v___x_3802_);
v___x_3806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
lean_ctor_set(v___x_3806_, 1, v___x_3744_);
v___x_3807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3806_);
lean_ctor_set(v___x_3807_, 1, v___x_3744_);
v___x_3808_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3737_);
lean_ctor_set(v___x_3808_, 1, v___x_3800_);
lean_ctor_set(v___x_3808_, 2, v___x_3804_);
lean_ctor_set(v___x_3808_, 3, v___x_3807_);
v___x_3809_ = l_Lean_Syntax_node5(v___x_3737_, v___x_3755_, v___x_3758_, v___x_3799_, v___x_3765_, v___x_3808_, v___x_3786_);
v___x_3810_ = l_Lean_Syntax_node1(v___x_3737_, v___x_3754_, v___x_3809_);
v___x_3811_ = l_Lean_Syntax_node2(v___x_3737_, v___x_3738_, v_fst_3622_, v___x_3810_);
v___x_3812_ = l_Lean_Syntax_node4(v___x_3737_, v___x_3769_, v___x_3795_, v___x_3780_, v___x_3782_, v___x_3811_);
v___x_3813_ = l_Lean_Syntax_node2(v___x_3737_, v___x_3767_, v___x_3768_, v___x_3812_);
v___x_3814_ = l_Lean_Syntax_node5(v___x_3737_, v___x_3755_, v___x_3758_, v___x_3791_, v___x_3765_, v___x_3813_, v___x_3786_);
v___x_3815_ = l_Lean_Syntax_node2(v___x_3737_, v___x_3754_, v___x_3787_, v___x_3814_);
v___x_3816_ = l_Lean_Syntax_node2(v___x_3737_, v___x_3738_, v___x_3753_, v___x_3815_);
v_a_3585_ = v___x_3816_;
goto v___jp_3584_;
}
}
}
}
}
}
}
case 3:
{
lean_object* v_e_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
lean_del_object(v___x_3601_);
v_e_3823_ = lean_ctor_get(v_default_3628_, 0);
lean_inc_ref(v_e_3823_);
lean_dec_ref_known(v_default_3628_, 1);
v___x_3824_ = lean_box(1);
v___x_3825_ = l_Lean_PrettyPrinter_delab(v_e_3823_, v___x_3824_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v_toCold_3826_; lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3912_; 
v_toCold_3826_ = lean_ctor_get(v___y_3581_, 0);
lean_inc_ref(v_toCold_3826_);
v_a_3827_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3829_ = v___x_3825_;
v_isShared_3830_ = v_isSharedCheck_3912_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v___x_3825_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3912_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v_ref_3831_; lean_object* v_quotContext_3832_; lean_object* v_currMacroScope_3833_; uint8_t v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3844_; 
v_ref_3831_ = lean_ctor_get(v___y_3581_, 2);
lean_inc(v_ref_3831_);
lean_dec_ref(v___y_3581_);
v_quotContext_3832_ = lean_ctor_get(v_toCold_3826_, 8);
lean_inc_n(v_quotContext_3832_, 2);
v_currMacroScope_3833_ = lean_ctor_get(v_toCold_3826_, 9);
lean_inc_n(v_currMacroScope_3833_, 2);
lean_dec_ref(v_toCold_3826_);
v___x_3834_ = 0;
v___x_3835_ = l_Lean_SourceInfo_fromRef(v_ref_3831_, v___x_3834_);
lean_dec(v_ref_3831_);
v___x_3836_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3837_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3838_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3571_);
v___x_3839_ = l_Lean_Name_mkStr2(v___x_3571_, v___x_3838_);
v___x_3840_ = l_Lean_addMacroScope(v_quotContext_3832_, v___x_3839_, v_currMacroScope_3833_);
v___x_3841_ = l_Lean_Name_mkStr4(v___x_3572_, v___x_3573_, v___x_3571_, v___x_3838_);
v___x_3842_ = lean_box(0);
lean_inc(v___x_3841_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 1);
lean_ctor_set(v___x_3630_, 1, v___x_3842_);
lean_ctor_set(v___x_3630_, 0, v___x_3841_);
v___x_3844_ = v___x_3630_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3841_);
lean_ctor_set(v_reuseFailAlloc_3911_, 1, v___x_3842_);
v___x_3844_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
lean_object* v___x_3846_; 
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 0, v___x_3841_);
v___x_3846_ = v___x_3829_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3841_);
v___x_3846_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
lean_object* v___x_3848_; 
if (v_isShared_3626_ == 0)
{
lean_ctor_set_tag(v___x_3625_, 1);
lean_ctor_set(v___x_3625_, 1, v___x_3842_);
lean_ctor_set(v___x_3625_, 0, v___x_3846_);
v___x_3848_ = v___x_3625_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v___x_3846_);
lean_ctor_set(v_reuseFailAlloc_3909_, 1, v___x_3842_);
v___x_3848_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
lean_object* v___x_3850_; 
if (v_isShared_3617_ == 0)
{
lean_ctor_set_tag(v___x_3616_, 1);
lean_ctor_set(v___x_3616_, 1, v___x_3848_);
lean_ctor_set(v___x_3616_, 0, v___x_3844_);
v___x_3850_ = v___x_3616_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3844_);
lean_ctor_set(v_reuseFailAlloc_3908_, 1, v___x_3848_);
v___x_3850_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3856_; 
lean_inc_n(v___x_3835_, 2);
v___x_3851_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3835_);
lean_ctor_set(v___x_3851_, 1, v___x_3837_);
lean_ctor_set(v___x_3851_, 2, v___x_3840_);
lean_ctor_set(v___x_3851_, 3, v___x_3850_);
v___x_3852_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3853_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3854_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3612_ == 0)
{
lean_ctor_set_tag(v___x_3611_, 2);
lean_ctor_set(v___x_3611_, 1, v___x_3854_);
lean_ctor_set(v___x_3611_, 0, v___x_3835_);
v___x_3856_ = v___x_3611_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3835_);
lean_ctor_set(v_reuseFailAlloc_3907_, 1, v___x_3854_);
v___x_3856_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3863_; 
v___x_3857_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3858_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3833_);
lean_inc(v_quotContext_3832_);
v___x_3859_ = l_Lean_addMacroScope(v_quotContext_3832_, v___x_3858_, v_currMacroScope_3833_);
lean_inc_n(v___x_3835_, 2);
v___x_3860_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3835_);
lean_ctor_set(v___x_3860_, 1, v___x_3857_);
lean_ctor_set(v___x_3860_, 2, v___x_3859_);
lean_ctor_set(v___x_3860_, 3, v___x_3842_);
v___x_3861_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3608_ == 0)
{
lean_ctor_set_tag(v___x_3607_, 2);
lean_ctor_set(v___x_3607_, 1, v___x_3861_);
lean_ctor_set(v___x_3607_, 0, v___x_3835_);
v___x_3863_ = v___x_3607_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v___x_3835_);
lean_ctor_set(v_reuseFailAlloc_3906_, 1, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3864_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3865_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3835_, 21);
v___x_3866_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3866_, 0, v___x_3835_);
lean_ctor_set(v___x_3866_, 1, v___x_3864_);
v___x_3867_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3868_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3869_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3833_, 4);
lean_inc_n(v_quotContext_3832_, 4);
v___x_3870_ = l_Lean_addMacroScope(v_quotContext_3832_, v___x_3869_, v_currMacroScope_3833_);
v___x_3871_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3835_);
lean_ctor_set(v___x_3871_, 1, v___x_3868_);
lean_ctor_set(v___x_3871_, 2, v___x_3870_);
lean_ctor_set(v___x_3871_, 3, v___x_3842_);
v___x_3872_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3873_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3874_ = l_Lean_addMacroScope(v_quotContext_3832_, v___x_3873_, v_currMacroScope_3833_);
v___x_3875_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3835_);
lean_ctor_set(v___x_3875_, 1, v___x_3872_);
lean_ctor_set(v___x_3875_, 2, v___x_3874_);
lean_ctor_set(v___x_3875_, 3, v___x_3842_);
lean_inc_ref(v___x_3875_);
v___x_3876_ = l_Lean_Syntax_node2(v___x_3835_, v___x_3852_, v___x_3871_, v___x_3875_);
v___x_3877_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3878_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3835_);
lean_ctor_set(v___x_3878_, 1, v___x_3852_);
lean_ctor_set(v___x_3878_, 2, v___x_3877_);
v___x_3879_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3880_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3835_);
lean_ctor_set(v___x_3880_, 1, v___x_3879_);
lean_inc_ref(v___x_3880_);
lean_inc_ref(v___x_3878_);
v___x_3881_ = l_Lean_Syntax_node4(v___x_3835_, v___x_3867_, v___x_3876_, v___x_3878_, v___x_3880_, v_snd_3623_);
lean_inc_ref(v___x_3866_);
v___x_3882_ = l_Lean_Syntax_node2(v___x_3835_, v___x_3865_, v___x_3866_, v___x_3881_);
v___x_3883_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3884_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3835_);
lean_ctor_set(v___x_3884_, 1, v___x_3883_);
lean_inc_ref_n(v___x_3884_, 2);
lean_inc_ref_n(v___x_3863_, 2);
lean_inc_ref_n(v___x_3856_, 2);
v___x_3885_ = l_Lean_Syntax_node5(v___x_3835_, v___x_3853_, v___x_3856_, v___x_3860_, v___x_3863_, v___x_3882_, v___x_3884_);
v___x_3886_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3887_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3888_ = l_Lean_addMacroScope(v_quotContext_3832_, v___x_3887_, v_currMacroScope_3833_);
v___x_3889_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3835_);
lean_ctor_set(v___x_3889_, 1, v___x_3886_);
lean_ctor_set(v___x_3889_, 2, v___x_3888_);
lean_ctor_set(v___x_3889_, 3, v___x_3842_);
v___x_3890_ = l_String_toRawSubstring_x27(v___x_3574_);
v___x_3891_ = l_Lean_addMacroScope(v_quotContext_3832_, v___x_3562_, v_currMacroScope_3833_);
v___x_3892_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3835_);
lean_ctor_set(v___x_3892_, 1, v___x_3890_);
lean_ctor_set(v___x_3892_, 2, v___x_3891_);
lean_ctor_set(v___x_3892_, 3, v___x_3842_);
v___x_3893_ = l_Lean_Syntax_node2(v___x_3835_, v___x_3852_, v___x_3892_, v___x_3875_);
v___x_3894_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3895_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3896_ = l_Lean_addMacroScope(v_quotContext_3832_, v___x_3895_, v_currMacroScope_3833_);
v___x_3897_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3835_);
lean_ctor_set(v___x_3897_, 1, v___x_3894_);
lean_ctor_set(v___x_3897_, 2, v___x_3896_);
lean_ctor_set(v___x_3897_, 3, v___x_3842_);
v___x_3898_ = l_Lean_Syntax_node5(v___x_3835_, v___x_3853_, v___x_3856_, v___x_3897_, v___x_3863_, v_a_3827_, v___x_3884_);
v___x_3899_ = l_Lean_Syntax_node1(v___x_3835_, v___x_3852_, v___x_3898_);
v___x_3900_ = l_Lean_Syntax_node2(v___x_3835_, v___x_3836_, v_fst_3622_, v___x_3899_);
v___x_3901_ = l_Lean_Syntax_node4(v___x_3835_, v___x_3867_, v___x_3893_, v___x_3878_, v___x_3880_, v___x_3900_);
v___x_3902_ = l_Lean_Syntax_node2(v___x_3835_, v___x_3865_, v___x_3866_, v___x_3901_);
v___x_3903_ = l_Lean_Syntax_node5(v___x_3835_, v___x_3853_, v___x_3856_, v___x_3889_, v___x_3863_, v___x_3902_, v___x_3884_);
v___x_3904_ = l_Lean_Syntax_node2(v___x_3835_, v___x_3852_, v___x_3885_, v___x_3903_);
v___x_3905_ = l_Lean_Syntax_node2(v___x_3835_, v___x_3836_, v___x_3851_, v___x_3904_);
v_a_3585_ = v___x_3905_;
goto v___jp_3584_;
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
lean_del_object(v___x_3630_);
lean_del_object(v___x_3625_);
lean_dec(v_snd_3623_);
lean_dec(v_fst_3622_);
lean_del_object(v___x_3616_);
lean_del_object(v___x_3611_);
lean_del_object(v___x_3607_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v___x_3574_);
lean_dec_ref(v___x_3573_);
lean_dec_ref(v___x_3572_);
lean_dec_ref(v___x_3571_);
lean_dec(v___x_3562_);
v___y_3589_ = v___x_3825_;
goto v___jp_3588_;
}
}
default: 
{
lean_object* v_toCold_3913_; lean_object* v_ref_3914_; lean_object* v_quotContext_3915_; lean_object* v_currMacroScope_3916_; uint8_t v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3927_; 
lean_dec(v_default_3628_);
v_toCold_3913_ = lean_ctor_get(v___y_3581_, 0);
lean_inc_ref(v_toCold_3913_);
v_ref_3914_ = lean_ctor_get(v___y_3581_, 2);
lean_inc(v_ref_3914_);
lean_dec_ref(v___y_3581_);
v_quotContext_3915_ = lean_ctor_get(v_toCold_3913_, 8);
lean_inc_n(v_quotContext_3915_, 2);
v_currMacroScope_3916_ = lean_ctor_get(v_toCold_3913_, 9);
lean_inc_n(v_currMacroScope_3916_, 2);
lean_dec_ref(v_toCold_3913_);
v___x_3917_ = 0;
v___x_3918_ = l_Lean_SourceInfo_fromRef(v_ref_3914_, v___x_3917_);
lean_dec(v_ref_3914_);
v___x_3919_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3920_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3921_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3571_);
v___x_3922_ = l_Lean_Name_mkStr2(v___x_3571_, v___x_3921_);
v___x_3923_ = l_Lean_addMacroScope(v_quotContext_3915_, v___x_3922_, v_currMacroScope_3916_);
v___x_3924_ = l_Lean_Name_mkStr4(v___x_3572_, v___x_3573_, v___x_3571_, v___x_3921_);
v___x_3925_ = lean_box(0);
lean_inc(v___x_3924_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 1);
lean_ctor_set(v___x_3630_, 1, v___x_3925_);
lean_ctor_set(v___x_3630_, 0, v___x_3924_);
v___x_3927_ = v___x_3630_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v___x_3924_);
lean_ctor_set(v_reuseFailAlloc_3987_, 1, v___x_3925_);
v___x_3927_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
lean_object* v___x_3929_; 
if (v_isShared_3602_ == 0)
{
lean_ctor_set_tag(v___x_3601_, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3924_);
v___x_3929_ = v___x_3601_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v___x_3924_);
v___x_3929_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
lean_object* v___x_3931_; 
if (v_isShared_3626_ == 0)
{
lean_ctor_set_tag(v___x_3625_, 1);
lean_ctor_set(v___x_3625_, 1, v___x_3925_);
lean_ctor_set(v___x_3625_, 0, v___x_3929_);
v___x_3931_ = v___x_3625_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v___x_3929_);
lean_ctor_set(v_reuseFailAlloc_3985_, 1, v___x_3925_);
v___x_3931_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
lean_object* v___x_3933_; 
if (v_isShared_3617_ == 0)
{
lean_ctor_set_tag(v___x_3616_, 1);
lean_ctor_set(v___x_3616_, 1, v___x_3931_);
lean_ctor_set(v___x_3616_, 0, v___x_3927_);
v___x_3933_ = v___x_3616_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v___x_3927_);
lean_ctor_set(v_reuseFailAlloc_3984_, 1, v___x_3931_);
v___x_3933_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3939_; 
lean_inc_n(v___x_3918_, 2);
v___x_3934_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3918_);
lean_ctor_set(v___x_3934_, 1, v___x_3920_);
lean_ctor_set(v___x_3934_, 2, v___x_3923_);
lean_ctor_set(v___x_3934_, 3, v___x_3933_);
v___x_3935_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3936_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3937_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3612_ == 0)
{
lean_ctor_set_tag(v___x_3611_, 2);
lean_ctor_set(v___x_3611_, 1, v___x_3937_);
lean_ctor_set(v___x_3611_, 0, v___x_3918_);
v___x_3939_ = v___x_3611_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v___x_3918_);
lean_ctor_set(v_reuseFailAlloc_3983_, 1, v___x_3937_);
v___x_3939_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3946_; 
v___x_3940_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3941_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3916_);
lean_inc(v_quotContext_3915_);
v___x_3942_ = l_Lean_addMacroScope(v_quotContext_3915_, v___x_3941_, v_currMacroScope_3916_);
lean_inc_n(v___x_3918_, 2);
v___x_3943_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3918_);
lean_ctor_set(v___x_3943_, 1, v___x_3940_);
lean_ctor_set(v___x_3943_, 2, v___x_3942_);
lean_ctor_set(v___x_3943_, 3, v___x_3925_);
v___x_3944_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3608_ == 0)
{
lean_ctor_set_tag(v___x_3607_, 2);
lean_ctor_set(v___x_3607_, 1, v___x_3944_);
lean_ctor_set(v___x_3607_, 0, v___x_3918_);
v___x_3946_ = v___x_3607_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v___x_3918_);
lean_ctor_set(v_reuseFailAlloc_3982_, 1, v___x_3944_);
v___x_3946_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3947_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3948_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3918_, 17);
v___x_3949_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3918_);
lean_ctor_set(v___x_3949_, 1, v___x_3947_);
v___x_3950_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3951_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3952_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3916_, 3);
lean_inc_n(v_quotContext_3915_, 3);
v___x_3953_ = l_Lean_addMacroScope(v_quotContext_3915_, v___x_3952_, v_currMacroScope_3916_);
v___x_3954_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3918_);
lean_ctor_set(v___x_3954_, 1, v___x_3951_);
lean_ctor_set(v___x_3954_, 2, v___x_3953_);
lean_ctor_set(v___x_3954_, 3, v___x_3925_);
v___x_3955_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3956_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3957_ = l_Lean_addMacroScope(v_quotContext_3915_, v___x_3956_, v_currMacroScope_3916_);
v___x_3958_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3918_);
lean_ctor_set(v___x_3958_, 1, v___x_3955_);
lean_ctor_set(v___x_3958_, 2, v___x_3957_);
lean_ctor_set(v___x_3958_, 3, v___x_3925_);
lean_inc_ref(v___x_3958_);
v___x_3959_ = l_Lean_Syntax_node2(v___x_3918_, v___x_3935_, v___x_3954_, v___x_3958_);
v___x_3960_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3961_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3918_);
lean_ctor_set(v___x_3961_, 1, v___x_3935_);
lean_ctor_set(v___x_3961_, 2, v___x_3960_);
v___x_3962_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3963_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3918_);
lean_ctor_set(v___x_3963_, 1, v___x_3962_);
lean_inc_ref(v___x_3963_);
lean_inc_ref(v___x_3961_);
v___x_3964_ = l_Lean_Syntax_node4(v___x_3918_, v___x_3950_, v___x_3959_, v___x_3961_, v___x_3963_, v_snd_3623_);
lean_inc_ref(v___x_3949_);
v___x_3965_ = l_Lean_Syntax_node2(v___x_3918_, v___x_3948_, v___x_3949_, v___x_3964_);
v___x_3966_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3967_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3918_);
lean_ctor_set(v___x_3967_, 1, v___x_3966_);
lean_inc_ref(v___x_3967_);
lean_inc_ref(v___x_3946_);
lean_inc_ref(v___x_3939_);
v___x_3968_ = l_Lean_Syntax_node5(v___x_3918_, v___x_3936_, v___x_3939_, v___x_3943_, v___x_3946_, v___x_3965_, v___x_3967_);
v___x_3969_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3970_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3971_ = l_Lean_addMacroScope(v_quotContext_3915_, v___x_3970_, v_currMacroScope_3916_);
v___x_3972_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3918_);
lean_ctor_set(v___x_3972_, 1, v___x_3969_);
lean_ctor_set(v___x_3972_, 2, v___x_3971_);
lean_ctor_set(v___x_3972_, 3, v___x_3925_);
v___x_3973_ = l_String_toRawSubstring_x27(v___x_3574_);
v___x_3974_ = l_Lean_addMacroScope(v_quotContext_3915_, v___x_3562_, v_currMacroScope_3916_);
v___x_3975_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3975_, 0, v___x_3918_);
lean_ctor_set(v___x_3975_, 1, v___x_3973_);
lean_ctor_set(v___x_3975_, 2, v___x_3974_);
lean_ctor_set(v___x_3975_, 3, v___x_3925_);
v___x_3976_ = l_Lean_Syntax_node2(v___x_3918_, v___x_3935_, v___x_3975_, v___x_3958_);
v___x_3977_ = l_Lean_Syntax_node4(v___x_3918_, v___x_3950_, v___x_3976_, v___x_3961_, v___x_3963_, v_fst_3622_);
v___x_3978_ = l_Lean_Syntax_node2(v___x_3918_, v___x_3948_, v___x_3949_, v___x_3977_);
v___x_3979_ = l_Lean_Syntax_node5(v___x_3918_, v___x_3936_, v___x_3939_, v___x_3972_, v___x_3946_, v___x_3978_, v___x_3967_);
v___x_3980_ = l_Lean_Syntax_node2(v___x_3918_, v___x_3935_, v___x_3968_, v___x_3979_);
v___x_3981_ = l_Lean_Syntax_node2(v___x_3918_, v___x_3919_, v___x_3934_, v___x_3980_);
v_a_3585_ = v___x_3981_;
goto v___jp_3584_;
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
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_del_object(v___x_3616_);
lean_dec(v_snd_3614_);
lean_del_object(v___x_3611_);
lean_del_object(v___x_3607_);
lean_del_object(v___x_3601_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v___x_3574_);
lean_dec_ref(v___x_3573_);
lean_dec_ref(v___x_3572_);
lean_dec_ref(v___x_3571_);
lean_dec(v___x_3570_);
lean_dec(v___x_3562_);
v_a_3990_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3620_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3620_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
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
lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4077_; 
lean_dec(v_a_3592_);
lean_dec(v___x_3570_);
lean_dec(v___x_3568_);
lean_dec_ref(v___x_3563_);
v_isSharedCheck_4077_ = !lean_is_exclusive(v_val_3595_);
if (v_isSharedCheck_4077_ == 0)
{
lean_object* v_unused_4078_; lean_object* v_unused_4079_; 
v_unused_4078_ = lean_ctor_get(v_val_3595_, 1);
lean_dec(v_unused_4078_);
v_unused_4079_ = lean_ctor_get(v_val_3595_, 0);
lean_dec(v_unused_4079_);
v___x_4004_ = v_val_3595_;
v_isShared_4005_ = v_isSharedCheck_4077_;
goto v_resetjp_4003_;
}
else
{
lean_dec(v_val_3595_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4077_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v_toCold_4006_; lean_object* v_ref_4007_; lean_object* v_quotContext_4008_; lean_object* v_currMacroScope_4009_; uint8_t v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4020_; 
v_toCold_4006_ = lean_ctor_get(v___y_3581_, 0);
lean_inc_ref(v_toCold_4006_);
v_ref_4007_ = lean_ctor_get(v___y_3581_, 2);
lean_inc(v_ref_4007_);
lean_dec_ref(v___y_3581_);
v_quotContext_4008_ = lean_ctor_get(v_toCold_4006_, 8);
lean_inc_n(v_quotContext_4008_, 2);
v_currMacroScope_4009_ = lean_ctor_get(v_toCold_4006_, 9);
lean_inc_n(v_currMacroScope_4009_, 2);
lean_dec_ref(v_toCold_4006_);
v___x_4010_ = 0;
v___x_4011_ = l_Lean_SourceInfo_fromRef(v_ref_4007_, v___x_4010_);
lean_dec(v_ref_4007_);
v___x_4012_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_4013_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_4014_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3571_);
v___x_4015_ = l_Lean_Name_mkStr2(v___x_3571_, v___x_4014_);
v___x_4016_ = l_Lean_addMacroScope(v_quotContext_4008_, v___x_4015_, v_currMacroScope_4009_);
v___x_4017_ = l_Lean_Name_mkStr4(v___x_3572_, v___x_3573_, v___x_3571_, v___x_4014_);
v___x_4018_ = lean_box(0);
lean_inc(v___x_4017_);
if (v_isShared_4005_ == 0)
{
lean_ctor_set_tag(v___x_4004_, 1);
lean_ctor_set(v___x_4004_, 1, v___x_4018_);
lean_ctor_set(v___x_4004_, 0, v___x_4017_);
v___x_4020_ = v___x_4004_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4017_);
lean_ctor_set(v_reuseFailAlloc_4076_, 1, v___x_4018_);
v___x_4020_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
lean_object* v___x_4022_; 
if (v_isShared_3598_ == 0)
{
lean_ctor_set_tag(v___x_3597_, 0);
lean_ctor_set(v___x_3597_, 0, v___x_4017_);
v___x_4022_ = v___x_3597_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v___x_4017_);
v___x_4022_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4023_, 0, v___x_4022_);
lean_ctor_set(v___x_4023_, 1, v___x_4018_);
v___x_4024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4020_);
lean_ctor_set(v___x_4024_, 1, v___x_4023_);
lean_inc_n(v___x_4011_, 23);
v___x_4025_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4011_);
lean_ctor_set(v___x_4025_, 1, v___x_4013_);
lean_ctor_set(v___x_4025_, 2, v___x_4016_);
lean_ctor_set(v___x_4025_, 3, v___x_4024_);
v___x_4026_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_4027_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_4028_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
v___x_4029_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4011_);
lean_ctor_set(v___x_4029_, 1, v___x_4028_);
v___x_4030_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_4031_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc_n(v_currMacroScope_4009_, 4);
lean_inc_n(v_quotContext_4008_, 4);
v___x_4032_ = l_Lean_addMacroScope(v_quotContext_4008_, v___x_4031_, v_currMacroScope_4009_);
v___x_4033_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4011_);
lean_ctor_set(v___x_4033_, 1, v___x_4030_);
lean_ctor_set(v___x_4033_, 2, v___x_4032_);
lean_ctor_set(v___x_4033_, 3, v___x_4018_);
v___x_4034_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
v___x_4035_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4011_);
lean_ctor_set(v___x_4035_, 1, v___x_4034_);
v___x_4036_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_4037_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
v___x_4038_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4011_);
lean_ctor_set(v___x_4038_, 1, v___x_4036_);
v___x_4039_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_4040_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_4041_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_4042_ = l_Lean_addMacroScope(v_quotContext_4008_, v___x_4041_, v_currMacroScope_4009_);
v___x_4043_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4011_);
lean_ctor_set(v___x_4043_, 1, v___x_4040_);
lean_ctor_set(v___x_4043_, 2, v___x_4042_);
lean_ctor_set(v___x_4043_, 3, v___x_4018_);
v___x_4044_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4045_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4046_ = l_Lean_addMacroScope(v_quotContext_4008_, v___x_4045_, v_currMacroScope_4009_);
v___x_4047_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4011_);
lean_ctor_set(v___x_4047_, 1, v___x_4044_);
lean_ctor_set(v___x_4047_, 2, v___x_4046_);
lean_ctor_set(v___x_4047_, 3, v___x_4018_);
lean_inc_ref(v___x_4047_);
v___x_4048_ = l_Lean_Syntax_node2(v___x_4011_, v___x_4026_, v___x_4043_, v___x_4047_);
v___x_4049_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_4050_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4011_);
lean_ctor_set(v___x_4050_, 1, v___x_4026_);
lean_ctor_set(v___x_4050_, 2, v___x_4049_);
v___x_4051_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_4052_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4011_);
lean_ctor_set(v___x_4052_, 1, v___x_4051_);
v___x_4053_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_4054_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
v___x_4055_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4011_);
lean_ctor_set(v___x_4055_, 1, v___x_4054_);
v___x_4056_ = l_Lean_Syntax_node1(v___x_4011_, v___x_4053_, v___x_4055_);
lean_inc(v___x_4056_);
lean_inc_ref(v___x_4052_);
lean_inc_ref(v___x_4050_);
v___x_4057_ = l_Lean_Syntax_node4(v___x_4011_, v___x_4039_, v___x_4048_, v___x_4050_, v___x_4052_, v___x_4056_);
lean_inc_ref(v___x_4038_);
v___x_4058_ = l_Lean_Syntax_node2(v___x_4011_, v___x_4037_, v___x_4038_, v___x_4057_);
v___x_4059_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_4060_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4011_);
lean_ctor_set(v___x_4060_, 1, v___x_4059_);
lean_inc_ref(v___x_4060_);
lean_inc_ref(v___x_4035_);
lean_inc_ref(v___x_4029_);
v___x_4061_ = l_Lean_Syntax_node5(v___x_4011_, v___x_4027_, v___x_4029_, v___x_4033_, v___x_4035_, v___x_4058_, v___x_4060_);
v___x_4062_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_4063_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_4064_ = l_Lean_addMacroScope(v_quotContext_4008_, v___x_4063_, v_currMacroScope_4009_);
v___x_4065_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4011_);
lean_ctor_set(v___x_4065_, 1, v___x_4062_);
lean_ctor_set(v___x_4065_, 2, v___x_4064_);
lean_ctor_set(v___x_4065_, 3, v___x_4018_);
v___x_4066_ = l_String_toRawSubstring_x27(v___x_3574_);
v___x_4067_ = l_Lean_addMacroScope(v_quotContext_4008_, v___x_3562_, v_currMacroScope_4009_);
v___x_4068_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4011_);
lean_ctor_set(v___x_4068_, 1, v___x_4066_);
lean_ctor_set(v___x_4068_, 2, v___x_4067_);
lean_ctor_set(v___x_4068_, 3, v___x_4018_);
v___x_4069_ = l_Lean_Syntax_node2(v___x_4011_, v___x_4026_, v___x_4068_, v___x_4047_);
v___x_4070_ = l_Lean_Syntax_node4(v___x_4011_, v___x_4039_, v___x_4069_, v___x_4050_, v___x_4052_, v___x_4056_);
v___x_4071_ = l_Lean_Syntax_node2(v___x_4011_, v___x_4037_, v___x_4038_, v___x_4070_);
v___x_4072_ = l_Lean_Syntax_node5(v___x_4011_, v___x_4027_, v___x_4029_, v___x_4065_, v___x_4035_, v___x_4071_, v___x_4060_);
v___x_4073_ = l_Lean_Syntax_node2(v___x_4011_, v___x_4026_, v___x_4061_, v___x_4072_);
v___x_4074_ = l_Lean_Syntax_node2(v___x_4011_, v___x_4012_, v___x_4025_, v___x_4073_);
v_a_3585_ = v___x_4074_;
goto v___jp_3584_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3594_);
lean_dec_ref(v___x_3571_);
if (lean_obj_tag(v_a_3592_) == 1)
{
lean_object* v_val_4081_; lean_object* v_snd_4082_; lean_object* v_fst_4083_; lean_object* v_snd_4084_; lean_object* v___x_4085_; lean_object* v___f_4086_; lean_object* v___x_4087_; 
v_val_4081_ = lean_ctor_get(v_a_3592_, 0);
lean_inc(v_val_4081_);
lean_dec_ref_known(v_a_3592_, 1);
v_snd_4082_ = lean_ctor_get(v_val_4081_, 1);
lean_inc(v_snd_4082_);
v_fst_4083_ = lean_ctor_get(v_val_4081_, 0);
lean_inc(v_fst_4083_);
lean_dec(v_val_4081_);
v_snd_4084_ = lean_ctor_get(v_snd_4082_, 1);
lean_inc(v_snd_4084_);
lean_dec(v_snd_4082_);
v___x_4085_ = lean_box(v___x_3569_);
lean_inc(v___x_3562_);
v___f_4086_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed), 20, 10);
lean_closure_set(v___f_4086_, 0, v_fst_4083_);
lean_closure_set(v___f_4086_, 1, v_snd_4084_);
lean_closure_set(v___f_4086_, 2, v___x_3574_);
lean_closure_set(v___f_4086_, 3, v___x_3562_);
lean_closure_set(v___f_4086_, 4, v___x_3568_);
lean_closure_set(v___f_4086_, 5, v___x_3570_);
lean_closure_set(v___f_4086_, 6, v___x_3572_);
lean_closure_set(v___f_4086_, 7, v___x_3573_);
lean_closure_set(v___f_4086_, 8, v___x_4085_);
lean_closure_set(v___f_4086_, 9, v_arg_3567_);
v___x_4087_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3562_, v___x_3563_, v___f_4086_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
lean_dec_ref(v___y_3581_);
v___y_3589_ = v___x_4087_;
goto v___jp_3588_;
}
else
{
lean_object* v_toCold_4088_; lean_object* v_ref_4089_; lean_object* v_quotContext_4090_; lean_object* v_currMacroScope_4091_; uint8_t v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
lean_dec(v_a_3592_);
lean_dec(v___x_3570_);
lean_dec(v___x_3568_);
lean_dec_ref(v_arg_3567_);
lean_dec_ref(v___x_3563_);
v_toCold_4088_ = lean_ctor_get(v___y_3581_, 0);
lean_inc_ref(v_toCold_4088_);
v_ref_4089_ = lean_ctor_get(v___y_3581_, 2);
lean_inc(v_ref_4089_);
lean_dec_ref(v___y_3581_);
v_quotContext_4090_ = lean_ctor_get(v_toCold_4088_, 8);
lean_inc_n(v_quotContext_4090_, 2);
v_currMacroScope_4091_ = lean_ctor_get(v_toCold_4088_, 9);
lean_inc_n(v_currMacroScope_4091_, 2);
lean_dec_ref(v_toCold_4088_);
v___x_4092_ = 0;
v___x_4093_ = l_Lean_SourceInfo_fromRef(v_ref_4089_, v___x_4092_);
lean_dec(v_ref_4089_);
v___x_4094_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_4095_ = l_Lean_Name_mkStr3(v___x_3572_, v___x_3573_, v___x_4094_);
v___x_4096_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_4097_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_4093_, 13);
v___x_4098_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4093_);
lean_ctor_set(v___x_4098_, 1, v___x_4096_);
lean_ctor_set(v___x_4098_, 2, v___x_4097_);
v___x_4099_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_4100_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4093_);
lean_ctor_set(v___x_4100_, 1, v___x_4099_);
v___x_4101_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_4102_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_4103_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_4104_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4093_);
lean_ctor_set(v___x_4104_, 1, v___x_4103_);
v___x_4105_ = l_String_toRawSubstring_x27(v___x_3574_);
v___x_4106_ = l_Lean_addMacroScope(v_quotContext_4090_, v___x_3562_, v_currMacroScope_4091_);
v___x_4107_ = lean_box(0);
v___x_4108_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4093_);
lean_ctor_set(v___x_4108_, 1, v___x_4105_);
lean_ctor_set(v___x_4108_, 2, v___x_4106_);
lean_ctor_set(v___x_4108_, 3, v___x_4107_);
v___x_4109_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_4110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4093_);
lean_ctor_set(v___x_4110_, 1, v___x_4109_);
v___x_4111_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4112_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4113_ = l_Lean_addMacroScope(v_quotContext_4090_, v___x_4112_, v_currMacroScope_4091_);
v___x_4114_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4093_);
lean_ctor_set(v___x_4114_, 1, v___x_4111_);
lean_ctor_set(v___x_4114_, 2, v___x_4113_);
lean_ctor_set(v___x_4114_, 3, v___x_4107_);
v___x_4115_ = l_Lean_Syntax_node3(v___x_4093_, v___x_4101_, v___x_4108_, v___x_4110_, v___x_4114_);
v___x_4116_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_4117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4093_);
lean_ctor_set(v___x_4117_, 1, v___x_4116_);
v___x_4118_ = l_Lean_Syntax_node3(v___x_4093_, v___x_4102_, v___x_4104_, v___x_4115_, v___x_4117_);
v___x_4119_ = l_Lean_Syntax_node1(v___x_4093_, v___x_4101_, v___x_4118_);
v___x_4120_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_4121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4093_);
lean_ctor_set(v___x_4121_, 1, v___x_4120_);
v___x_4122_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_4123_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
v___x_4124_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4093_);
lean_ctor_set(v___x_4124_, 1, v___x_4123_);
v___x_4125_ = l_Lean_Syntax_node1(v___x_4093_, v___x_4122_, v___x_4124_);
v___x_4126_ = l_Lean_Syntax_node5(v___x_4093_, v___x_4095_, v___x_4098_, v___x_4100_, v___x_4119_, v___x_4121_, v___x_4125_);
v_a_3585_ = v___x_4126_;
goto v___jp_3584_;
}
}
}
else
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4134_; 
lean_dec(v_a_3592_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v___x_3574_);
lean_dec_ref(v___x_3573_);
lean_dec_ref(v___x_3572_);
lean_dec_ref(v___x_3571_);
lean_dec(v___x_3570_);
lean_dec(v___x_3568_);
lean_dec_ref(v_arg_3567_);
lean_dec_ref(v___x_3563_);
lean_dec(v___x_3562_);
v_a_4127_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4129_ = v___x_3593_;
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_3593_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4127_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_dec_ref(v___y_3581_);
lean_dec_ref(v___x_3574_);
lean_dec_ref(v___x_3573_);
lean_dec_ref(v___x_3572_);
lean_dec_ref(v___x_3571_);
lean_dec(v___x_3570_);
lean_dec(v___x_3568_);
lean_dec_ref(v_arg_3567_);
lean_dec(v_inv_3566_);
lean_dec_ref(v___x_3563_);
lean_dec(v___x_3562_);
v_a_4135_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_3591_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_3591_);
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
v___jp_3584_:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_a_3585_);
v___x_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
return v___x_3587_;
}
v___jp_3588_:
{
if (lean_obj_tag(v___y_3589_) == 0)
{
lean_object* v_a_3590_; 
v_a_3590_ = lean_ctor_get(v___y_3589_, 0);
lean_inc(v_a_3590_);
lean_dec_ref_known(v___y_3589_, 1);
v_a_3585_ = v_a_3590_;
goto v___jp_3584_;
}
else
{
return v___y_3589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed(lean_object** _args){
lean_object* v___x_4143_ = _args[0];
lean_object* v___x_4144_ = _args[1];
lean_object* v___f_4145_ = _args[2];
lean_object* v_a_4146_ = _args[3];
lean_object* v_inv_4147_ = _args[4];
lean_object* v_arg_4148_ = _args[5];
lean_object* v___x_4149_ = _args[6];
lean_object* v___x_4150_ = _args[7];
lean_object* v___x_4151_ = _args[8];
lean_object* v___x_4152_ = _args[9];
lean_object* v___x_4153_ = _args[10];
lean_object* v___x_4154_ = _args[11];
lean_object* v___x_4155_ = _args[12];
lean_object* v___y_4156_ = _args[13];
lean_object* v___y_4157_ = _args[14];
lean_object* v___y_4158_ = _args[15];
lean_object* v___y_4159_ = _args[16];
lean_object* v___y_4160_ = _args[17];
lean_object* v___y_4161_ = _args[18];
lean_object* v___y_4162_ = _args[19];
lean_object* v___y_4163_ = _args[20];
lean_object* v___y_4164_ = _args[21];
_start:
{
uint8_t v___x_79132__boxed_4165_; lean_object* v_res_4166_; 
v___x_79132__boxed_4165_ = lean_unbox(v___x_4150_);
v_res_4166_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(v___x_4143_, v___x_4144_, v___f_4145_, v_a_4146_, v_inv_4147_, v_arg_4148_, v___x_4149_, v___x_79132__boxed_4165_, v___x_4151_, v___x_4152_, v___x_4153_, v___x_4154_, v___x_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
lean_dec(v___y_4163_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
lean_dec(v___y_4159_);
lean_dec_ref(v___y_4158_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec_ref(v_a_4146_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(lean_object* v_msgData_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v___x_4173_; lean_object* v_env_4174_; uint8_t v___x_4175_; lean_object* v_env_4176_; lean_object* v___x_4177_; lean_object* v_toCold_4178_; lean_object* v_mctx_4179_; lean_object* v_lctx_4180_; lean_object* v_options_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; 
v___x_4173_ = lean_st_ref_get(v___y_4171_);
v_env_4174_ = lean_ctor_get(v___x_4173_, 0);
lean_inc_ref(v_env_4174_);
lean_dec(v___x_4173_);
v___x_4175_ = 0;
v_env_4176_ = l_Lean_Environment_setRecordingDeps(v_env_4174_, v___x_4175_);
v___x_4177_ = lean_st_ref_get(v___y_4169_);
v_toCold_4178_ = lean_ctor_get(v___y_4170_, 0);
v_mctx_4179_ = lean_ctor_get(v___x_4177_, 0);
lean_inc_ref(v_mctx_4179_);
lean_dec(v___x_4177_);
v_lctx_4180_ = lean_ctor_get(v___y_4168_, 2);
v_options_4181_ = lean_ctor_get(v_toCold_4178_, 2);
lean_inc_ref(v_options_4181_);
lean_inc_ref(v_lctx_4180_);
v___x_4182_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4182_, 0, v_env_4176_);
lean_ctor_set(v___x_4182_, 1, v_mctx_4179_);
lean_ctor_set(v___x_4182_, 2, v_lctx_4180_);
lean_ctor_set(v___x_4182_, 3, v_options_4181_);
v___x_4183_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4182_);
lean_ctor_set(v___x_4183_, 1, v_msgData_4167_);
v___x_4184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4183_);
return v___x_4184_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1___boxed(lean_object* v_msgData_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msgData_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(lean_object* v_msg_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_){
_start:
{
lean_object* v_ref_4198_; lean_object* v___x_4199_; lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4208_; 
v_ref_4198_ = lean_ctor_get(v___y_4195_, 2);
v___x_4199_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msg_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4202_ = v___x_4199_;
v_isShared_4203_ = v_isSharedCheck_4208_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4199_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4208_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4204_; lean_object* v___x_4206_; 
lean_inc(v_ref_4198_);
v___x_4204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4204_, 0, v_ref_4198_);
lean_ctor_set(v___x_4204_, 1, v_a_4200_);
if (v_isShared_4203_ == 0)
{
lean_ctor_set_tag(v___x_4202_, 1);
lean_ctor_set(v___x_4202_, 0, v___x_4204_);
v___x_4206_ = v___x_4202_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v___x_4204_);
v___x_4206_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
return v___x_4206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg___boxed(lean_object* v_msg_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(lean_object* v_as_4222_, size_t v_i_4223_, size_t v_stop_4224_, lean_object* v_b_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v_a_4236_; lean_object* v_a_4241_; uint8_t v___x_4243_; 
v___x_4243_ = lean_usize_dec_eq(v_i_4223_, v_stop_4224_);
if (v___x_4243_ == 0)
{
lean_object* v___x_4244_; lean_object* v___x_4245_; 
v___x_4244_ = lean_array_uget_borrowed(v_as_4222_, v_i_4223_);
v___x_4245_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_4227_, v___y_4229_, v___y_4231_, v___y_4233_);
if (lean_obj_tag(v___x_4245_) == 0)
{
lean_object* v_a_4246_; lean_object* v___y_4248_; uint8_t v___y_4249_; lean_object* v___y_4264_; lean_object* v_a_4265_; lean_object* v_ref_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v_a_4246_ = lean_ctor_get(v___x_4245_, 0);
lean_inc(v_a_4246_);
lean_dec_ref_known(v___x_4245_, 1);
v_ref_4268_ = lean_ctor_get(v___y_4232_, 2);
v___x_4269_ = l_Lean_SourceInfo_fromRef(v_ref_4268_, v___x_4243_);
v___x_4270_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__0));
v___x_4271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__1));
lean_inc(v___x_4269_);
v___x_4272_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4269_);
lean_ctor_set(v___x_4272_, 1, v___x_4270_);
v___x_4273_ = l_Lean_Syntax_node1(v___x_4269_, v___x_4271_, v___x_4272_);
lean_inc(v___x_4244_);
v___x_4274_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v___x_4244_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_object* v_a_4275_; lean_object* v___x_4276_; 
v_a_4275_ = lean_ctor_get(v___x_4274_, 0);
lean_inc(v_a_4275_);
lean_dec_ref_known(v___x_4274_, 1);
v___x_4276_ = l_Lean_Elab_Tactic_evalTacticAt(v___x_4273_, v_a_4275_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
if (lean_obj_tag(v___x_4276_) == 0)
{
lean_object* v_a_4277_; lean_object* v___x_4278_; 
lean_dec(v_a_4246_);
v_a_4277_ = lean_ctor_get(v___x_4276_, 0);
lean_inc(v_a_4277_);
lean_dec_ref_known(v___x_4276_, 1);
v___x_4278_ = lean_array_mk(v_a_4277_);
v_a_4241_ = v___x_4278_;
goto v___jp_4240_;
}
else
{
lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4286_; 
v_a_4279_ = lean_ctor_get(v___x_4276_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4281_ = v___x_4276_;
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_a_4279_);
lean_dec(v___x_4276_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4284_; 
lean_inc(v_a_4279_);
if (v_isShared_4282_ == 0)
{
v___x_4284_ = v___x_4281_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_a_4279_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
v___y_4264_ = v___x_4284_;
v_a_4265_ = v_a_4279_;
goto v___jp_4263_;
}
}
}
}
else
{
lean_object* v_a_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4294_; 
lean_dec(v___x_4273_);
v_a_4287_ = lean_ctor_get(v___x_4274_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4289_ = v___x_4274_;
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_a_4287_);
lean_dec(v___x_4274_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4292_; 
lean_inc(v_a_4287_);
if (v_isShared_4290_ == 0)
{
v___x_4292_ = v___x_4289_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_a_4287_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
v___y_4264_ = v___x_4292_;
v_a_4265_ = v_a_4287_;
goto v___jp_4263_;
}
}
}
v___jp_4247_:
{
if (v___y_4249_ == 0)
{
lean_object* v___x_4250_; 
lean_dec_ref(v___y_4248_);
v___x_4250_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_4246_, v___y_4249_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
if (lean_obj_tag(v___x_4250_) == 0)
{
lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
lean_dec_ref_known(v___x_4250_, 1);
v___x_4251_ = lean_unsigned_to_nat(1u);
v___x_4252_ = lean_mk_empty_array_with_capacity(v___x_4251_);
lean_inc(v___x_4244_);
v___x_4253_ = lean_array_push(v___x_4252_, v___x_4244_);
v_a_4241_ = v___x_4253_;
goto v___jp_4240_;
}
else
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4261_; 
lean_dec_ref(v_b_4225_);
v_a_4254_ = lean_ctor_get(v___x_4250_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4250_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4256_ = v___x_4250_;
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4250_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4259_; 
if (v_isShared_4257_ == 0)
{
v___x_4259_ = v___x_4256_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_a_4254_);
v___x_4259_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
return v___x_4259_;
}
}
}
}
else
{
lean_dec(v_a_4246_);
lean_dec_ref(v_b_4225_);
if (lean_obj_tag(v___y_4248_) == 0)
{
lean_object* v_a_4262_; 
v_a_4262_ = lean_ctor_get(v___y_4248_, 0);
lean_inc(v_a_4262_);
lean_dec_ref_known(v___y_4248_, 1);
v_a_4236_ = v_a_4262_;
goto v___jp_4235_;
}
else
{
return v___y_4248_;
}
}
}
v___jp_4263_:
{
uint8_t v___x_4266_; 
v___x_4266_ = l_Lean_Exception_isInterrupt(v_a_4265_);
if (v___x_4266_ == 0)
{
uint8_t v___x_4267_; 
v___x_4267_ = l_Lean_Exception_isRuntime(v_a_4265_);
v___y_4248_ = v___y_4264_;
v___y_4249_ = v___x_4267_;
goto v___jp_4247_;
}
else
{
lean_dec_ref(v_a_4265_);
v___y_4248_ = v___y_4264_;
v___y_4249_ = v___x_4266_;
goto v___jp_4247_;
}
}
}
else
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4302_; 
lean_dec_ref(v_b_4225_);
v_a_4295_ = lean_ctor_get(v___x_4245_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v___x_4245_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4297_ = v___x_4245_;
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4245_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4300_; 
if (v_isShared_4298_ == 0)
{
v___x_4300_ = v___x_4297_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_a_4295_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
return v___x_4300_;
}
}
}
}
else
{
lean_object* v___x_4303_; 
v___x_4303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4303_, 0, v_b_4225_);
return v___x_4303_;
}
v___jp_4235_:
{
size_t v___x_4237_; size_t v___x_4238_; 
v___x_4237_ = ((size_t)1ULL);
v___x_4238_ = lean_usize_add(v_i_4223_, v___x_4237_);
v_i_4223_ = v___x_4238_;
v_b_4225_ = v_a_4236_;
goto _start;
}
v___jp_4240_:
{
lean_object* v___x_4242_; 
v___x_4242_ = l_Array_append___redArg(v_b_4225_, v_a_4241_);
lean_dec_ref(v_a_4241_);
v_a_4236_ = v___x_4242_;
goto v___jp_4235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___boxed(lean_object* v_as_4304_, lean_object* v_i_4305_, lean_object* v_stop_4306_, lean_object* v_b_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
size_t v_i_boxed_4317_; size_t v_stop_boxed_4318_; lean_object* v_res_4319_; 
v_i_boxed_4317_ = lean_unbox_usize(v_i_4305_);
lean_dec(v_i_4305_);
v_stop_boxed_4318_ = lean_unbox_usize(v_stop_4306_);
lean_dec(v_stop_4306_);
v_res_4319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_as_4304_, v_i_boxed_4317_, v_stop_boxed_4318_, v_b_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
lean_dec_ref(v___y_4312_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec_ref(v_as_4304_);
return v_res_4319_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1(void){
_start:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; 
v___x_4321_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__0));
v___x_4322_ = l_Lean_stringToMessageData(v___x_4321_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant(lean_object* v_vcs_4338_, lean_object* v_inv_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_){
_start:
{
lean_object* v___x_4349_; 
lean_inc(v_inv_4339_);
v___x_4349_ = l_Lean_MVarId_getType(v_inv_4339_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v_a_4350_; lean_object* v___x_4351_; lean_object* v_a_4352_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___x_4366_; uint8_t v___x_4367_; 
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_a_4350_);
lean_dec_ref_known(v___x_4349_, 1);
v___x_4351_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_a_4350_, v_a_4345_);
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
lean_inc_n(v_a_4352_, 2);
lean_dec_ref(v___x_4351_);
v___x_4366_ = l_Lean_Expr_cleanupAnnotations(v_a_4352_);
v___x_4367_ = l_Lean_Expr_isApp(v___x_4366_);
if (v___x_4367_ == 0)
{
lean_dec_ref(v___x_4366_);
lean_dec(v_inv_4339_);
v___y_4354_ = v_a_4340_;
v___y_4355_ = v_a_4341_;
v___y_4356_ = v_a_4342_;
v___y_4357_ = v_a_4343_;
v___y_4358_ = v_a_4344_;
v___y_4359_ = v_a_4345_;
v___y_4360_ = v_a_4346_;
v___y_4361_ = v_a_4347_;
goto v___jp_4353_;
}
else
{
lean_object* v___x_4368_; uint8_t v___x_4369_; 
v___x_4368_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4366_);
v___x_4369_ = l_Lean_Expr_isApp(v___x_4368_);
if (v___x_4369_ == 0)
{
lean_dec_ref(v___x_4368_);
lean_dec(v_inv_4339_);
v___y_4354_ = v_a_4340_;
v___y_4355_ = v_a_4341_;
v___y_4356_ = v_a_4342_;
v___y_4357_ = v_a_4343_;
v___y_4358_ = v_a_4344_;
v___y_4359_ = v_a_4345_;
v___y_4360_ = v_a_4346_;
v___y_4361_ = v_a_4347_;
goto v___jp_4353_;
}
else
{
lean_object* v_arg_4370_; lean_object* v___x_4371_; uint8_t v___x_4372_; 
v_arg_4370_ = lean_ctor_get(v___x_4368_, 1);
lean_inc_ref(v_arg_4370_);
v___x_4371_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4368_);
v___x_4372_ = l_Lean_Expr_isApp(v___x_4371_);
if (v___x_4372_ == 0)
{
lean_dec_ref(v___x_4371_);
lean_dec_ref(v_arg_4370_);
lean_dec(v_inv_4339_);
v___y_4354_ = v_a_4340_;
v___y_4355_ = v_a_4341_;
v___y_4356_ = v_a_4342_;
v___y_4357_ = v_a_4343_;
v___y_4358_ = v_a_4344_;
v___y_4359_ = v_a_4345_;
v___y_4360_ = v_a_4346_;
v___y_4361_ = v_a_4347_;
goto v___jp_4353_;
}
else
{
lean_object* v_arg_4373_; lean_object* v___x_4374_; uint8_t v___x_4375_; 
v_arg_4373_ = lean_ctor_get(v___x_4371_, 1);
lean_inc_ref(v_arg_4373_);
v___x_4374_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4371_);
v___x_4375_ = l_Lean_Expr_isApp(v___x_4374_);
if (v___x_4375_ == 0)
{
lean_dec_ref(v___x_4374_);
lean_dec_ref(v_arg_4373_);
lean_dec_ref(v_arg_4370_);
lean_dec(v_inv_4339_);
v___y_4354_ = v_a_4340_;
v___y_4355_ = v_a_4341_;
v___y_4356_ = v_a_4342_;
v___y_4357_ = v_a_4343_;
v___y_4358_ = v_a_4344_;
v___y_4359_ = v_a_4345_;
v___y_4360_ = v_a_4346_;
v___y_4361_ = v_a_4347_;
goto v___jp_4353_;
}
else
{
lean_object* v_arg_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; uint8_t v___x_4382_; 
v_arg_4376_ = lean_ctor_get(v___x_4374_, 1);
lean_inc_ref(v_arg_4376_);
v___x_4377_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4374_);
v___x_4378_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1));
v___x_4379_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3));
v___x_4380_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__2));
v___x_4381_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__3));
v___x_4382_ = l_Lean_Expr_isConstOf(v___x_4377_, v___x_4381_);
if (v___x_4382_ == 0)
{
lean_dec_ref(v___x_4377_);
lean_dec_ref(v_arg_4376_);
lean_dec_ref(v_arg_4373_);
lean_dec_ref(v_arg_4370_);
lean_dec(v_inv_4339_);
v___y_4354_ = v_a_4340_;
v___y_4355_ = v_a_4341_;
v___y_4356_ = v_a_4342_;
v___y_4357_ = v_a_4343_;
v___y_4358_ = v_a_4344_;
v___y_4359_ = v_a_4345_;
v___y_4360_ = v_a_4346_;
v___y_4361_ = v_a_4347_;
goto v___jp_4353_;
}
else
{
lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v_a_4389_; lean_object* v___x_4400_; lean_object* v___x_4401_; uint8_t v___x_4402_; 
lean_dec(v_a_4352_);
v___x_4383_ = lean_unsigned_to_nat(1u);
v___x_4384_ = l_Lean_Expr_constLevels_x21(v___x_4377_);
lean_dec_ref(v___x_4377_);
v___x_4385_ = lean_unsigned_to_nat(0u);
v___x_4386_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__4));
lean_inc(v___x_4384_);
v___x_4387_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v___x_4384_, v___x_4384_, v___x_4383_, v___x_4386_);
lean_dec(v___x_4384_);
v___x_4400_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__8));
v___x_4401_ = lean_array_get_size(v_vcs_4338_);
v___x_4402_ = lean_nat_dec_lt(v___x_4385_, v___x_4401_);
if (v___x_4402_ == 0)
{
v_a_4389_ = v___x_4400_;
goto v___jp_4388_;
}
else
{
size_t v___x_4403_; size_t v___x_4404_; lean_object* v___x_4405_; 
v___x_4403_ = ((size_t)0ULL);
v___x_4404_ = lean_usize_of_nat(v___x_4401_);
v___x_4405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_vcs_4338_, v___x_4403_, v___x_4404_, v___x_4400_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4406_);
lean_dec_ref_known(v___x_4405_, 1);
v_a_4389_ = v_a_4406_;
goto v___jp_4388_;
}
else
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4414_; 
lean_dec(v___x_4387_);
lean_dec_ref(v_arg_4376_);
lean_dec_ref(v_arg_4373_);
lean_dec_ref(v_arg_4370_);
lean_dec(v_inv_4339_);
v_a_4407_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4409_ = v___x_4405_;
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4405_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___x_4412_; 
if (v_isShared_4410_ == 0)
{
v___x_4412_ = v___x_4409_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_a_4407_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
}
v___jp_4388_:
{
lean_object* v___x_4390_; lean_object* v___f_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___f_4398_; lean_object* v___x_4399_; 
v___x_4390_ = lean_box(v___x_4382_);
lean_inc_ref(v_arg_4370_);
lean_inc_n(v_inv_4339_, 2);
lean_inc_ref(v_a_4389_);
v___f_4391_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed), 15, 5);
lean_closure_set(v___f_4391_, 0, v_a_4389_);
lean_closure_set(v___f_4391_, 1, v_inv_4339_);
lean_closure_set(v___f_4391_, 2, v___x_4390_);
lean_closure_set(v___f_4391_, 3, v___x_4383_);
lean_closure_set(v___f_4391_, 4, v_arg_4370_);
v___x_4392_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__5));
v___x_4393_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__6));
v___x_4394_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__7));
v___x_4395_ = l_Lean_mkConst(v___x_4394_, v___x_4387_);
v___x_4396_ = l_Lean_mkAppB(v___x_4395_, v_arg_4376_, v_arg_4373_);
v___x_4397_ = lean_box(v___x_4382_);
v___f_4398_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed), 22, 13);
lean_closure_set(v___f_4398_, 0, v___x_4393_);
lean_closure_set(v___f_4398_, 1, v___x_4396_);
lean_closure_set(v___f_4398_, 2, v___f_4391_);
lean_closure_set(v___f_4398_, 3, v_a_4389_);
lean_closure_set(v___f_4398_, 4, v_inv_4339_);
lean_closure_set(v___f_4398_, 5, v_arg_4370_);
lean_closure_set(v___f_4398_, 6, v___x_4383_);
lean_closure_set(v___f_4398_, 7, v___x_4397_);
lean_closure_set(v___f_4398_, 8, v___x_4385_);
lean_closure_set(v___f_4398_, 9, v___x_4380_);
lean_closure_set(v___f_4398_, 10, v___x_4378_);
lean_closure_set(v___f_4398_, 11, v___x_4379_);
lean_closure_set(v___f_4398_, 12, v___x_4392_);
v___x_4399_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_inv_4339_, v___f_4398_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
return v___x_4399_;
}
}
}
}
}
}
v___jp_4353_:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4362_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1, &l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1);
v___x_4363_ = l_Lean_MessageData_ofExpr(v_a_4352_);
v___x_4364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4362_);
lean_ctor_set(v___x_4364_, 1, v___x_4363_);
v___x_4365_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v___x_4364_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
return v___x_4365_;
}
}
else
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
lean_dec(v_inv_4339_);
v_a_4415_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4417_ = v___x_4349_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4349_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___boxed(lean_object* v_vcs_4423_, lean_object* v_inv_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_){
_start:
{
lean_object* v_res_4434_; 
v_res_4434_ = l_Lean_Elab_Tactic_Do_suggestInvariant(v_vcs_4423_, v_inv_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_);
lean_dec(v_a_4432_);
lean_dec_ref(v_a_4431_);
lean_dec(v_a_4430_);
lean_dec_ref(v_a_4429_);
lean_dec(v_a_4428_);
lean_dec_ref(v_a_4427_);
lean_dec(v_a_4426_);
lean_dec_ref(v_a_4425_);
lean_dec_ref(v_vcs_4423_);
return v_res_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(lean_object* v_00_u03b1_4435_, lean_object* v_msg_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v___x_4446_; 
v___x_4446_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4436_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
return v___x_4446_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___boxed(lean_object* v_00_u03b1_4447_, lean_object* v_msg_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_){
_start:
{
lean_object* v_res_4458_; 
v_res_4458_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(v_00_u03b1_4447_, v_msg_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(lean_object* v_00_u03b1_4459_, lean_object* v_name_4460_, uint8_t v_bi_4461_, lean_object* v_type_4462_, lean_object* v_k_4463_, uint8_t v_kind_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_){
_start:
{
lean_object* v___x_4474_; 
v___x_4474_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_4460_, v_bi_4461_, v_type_4462_, v_k_4463_, v_kind_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_);
return v___x_4474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4475_, lean_object* v_name_4476_, lean_object* v_bi_4477_, lean_object* v_type_4478_, lean_object* v_k_4479_, lean_object* v_kind_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_){
_start:
{
uint8_t v_bi_boxed_4490_; uint8_t v_kind_boxed_4491_; lean_object* v_res_4492_; 
v_bi_boxed_4490_ = lean_unbox(v_bi_4477_);
v_kind_boxed_4491_ = lean_unbox(v_kind_4480_);
v_res_4492_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(v_00_u03b1_4475_, v_name_4476_, v_bi_boxed_4490_, v_type_4478_, v_k_4479_, v_kind_boxed_4491_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(lean_object* v_00_u03b1_4493_, lean_object* v_name_4494_, lean_object* v_type_4495_, lean_object* v_k_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_){
_start:
{
lean_object* v___x_4506_; 
v___x_4506_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_4494_, v_type_4495_, v_k_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
return v___x_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___boxed(lean_object* v_00_u03b1_4507_, lean_object* v_name_4508_, lean_object* v_type_4509_, lean_object* v_k_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(v_00_u03b1_4507_, v_name_4508_, v_type_4509_, v_k_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec(v___y_4514_);
lean_dec_ref(v___y_4513_);
lean_dec(v___y_4512_);
lean_dec_ref(v___y_4511_);
return v_res_4520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(lean_object* v_as_4521_, size_t v_sz_4522_, size_t v_i_4523_, lean_object* v_b_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
lean_object* v___x_4534_; 
v___x_4534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_4521_, v_sz_4522_, v_i_4523_, v_b_4524_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_);
return v___x_4534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___boxed(lean_object* v_as_4535_, lean_object* v_sz_4536_, lean_object* v_i_4537_, lean_object* v_b_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_){
_start:
{
size_t v_sz_boxed_4548_; size_t v_i_boxed_4549_; lean_object* v_res_4550_; 
v_sz_boxed_4548_ = lean_unbox_usize(v_sz_4536_);
lean_dec(v_sz_4536_);
v_i_boxed_4549_ = lean_unbox_usize(v_i_4537_);
lean_dec(v_i_4537_);
v_res_4550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(v_as_4535_, v_sz_boxed_4548_, v_i_boxed_4549_, v_b_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
lean_dec_ref(v_as_4535_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(lean_object* v_as_4551_, size_t v_sz_4552_, size_t v_i_4553_, lean_object* v_b_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_){
_start:
{
lean_object* v___x_4564_; 
v___x_4564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_4551_, v_sz_4552_, v_i_4553_, v_b_4554_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
return v___x_4564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___boxed(lean_object* v_as_4565_, lean_object* v_sz_4566_, lean_object* v_i_4567_, lean_object* v_b_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
size_t v_sz_boxed_4578_; size_t v_i_boxed_4579_; lean_object* v_res_4580_; 
v_sz_boxed_4578_ = lean_unbox_usize(v_sz_4566_);
lean_dec(v_sz_4566_);
v_i_boxed_4579_ = lean_unbox_usize(v_i_4567_);
lean_dec(v_i_4567_);
v_res_4580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(v_as_4565_, v_sz_boxed_4578_, v_i_boxed_4579_, v_b_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_);
lean_dec(v___y_4576_);
lean_dec_ref(v___y_4575_);
lean_dec(v___y_4574_);
lean_dec_ref(v___y_4573_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec_ref(v_as_4565_);
return v_res_4580_;
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
