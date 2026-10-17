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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_lastDecl(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
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
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_collectForwardDeps(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
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
lean_inc(v___x_291_);
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
lean_object* v_arg_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v_arg_295_ = lean_ctor_get(v___x_292_, 1);
lean_inc_ref(v_arg_295_);
v___x_296_ = l_Lean_Expr_appFnCleanup___redArg(v___x_292_);
v___x_297_ = l_Lean_Expr_isApp(v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; 
lean_dec_ref(v___x_296_);
lean_dec_ref(v_arg_295_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_298_ = lean_box(2);
return v___x_298_;
}
else
{
lean_object* v_arg_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v_arg_299_ = lean_ctor_get(v___x_296_, 1);
lean_inc_ref(v_arg_299_);
v___x_300_ = l_Lean_Expr_appFnCleanup___redArg(v___x_296_);
v___x_301_ = l_Lean_Expr_isApp(v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; 
lean_dec_ref(v___x_300_);
lean_dec_ref(v_arg_299_);
lean_dec_ref(v_arg_295_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_302_ = lean_box(2);
return v___x_302_;
}
else
{
lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_303_ = l_Lean_Expr_appFnCleanup___redArg(v___x_300_);
v___x_304_ = l_Lean_Expr_isApp(v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
lean_dec_ref(v___x_303_);
lean_dec_ref(v_arg_299_);
lean_dec_ref(v_arg_295_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_305_ = lean_box(2);
return v___x_305_;
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_306_ = l_Lean_Expr_appFnCleanup___redArg(v___x_303_);
v___x_307_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_308_ = l_Lean_Expr_isConstOf(v___x_306_, v___x_307_);
lean_dec_ref(v___x_306_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
lean_dec_ref(v_arg_299_);
lean_dec_ref(v_arg_295_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_309_ = lean_box(2);
return v___x_309_;
}
else
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = l_Lean_Expr_cleanupAnnotations(v_arg_299_);
v___x_311_ = l_Lean_Expr_isApp(v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; 
lean_dec_ref(v___x_310_);
lean_dec_ref(v_arg_295_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_312_ = lean_box(2);
return v___x_312_;
}
else
{
lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_313_ = l_Lean_Expr_appFnCleanup___redArg(v___x_310_);
v___x_314_ = l_Lean_Expr_isApp(v___x_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; 
lean_dec_ref(v___x_313_);
lean_dec_ref(v_arg_295_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_315_ = lean_box(2);
return v___x_315_;
}
else
{
lean_object* v_arg_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v_arg_316_ = lean_ctor_get(v___x_313_, 1);
lean_inc_ref(v_arg_316_);
v___x_317_ = l_Lean_Expr_appFnCleanup___redArg(v___x_313_);
v___x_318_ = l_Lean_Expr_isApp(v___x_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; 
lean_dec_ref(v___x_317_);
lean_dec_ref(v_arg_316_);
lean_dec_ref(v_arg_295_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_319_ = lean_box(2);
return v___x_319_;
}
else
{
lean_object* v_arg_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v_arg_320_ = lean_ctor_get(v___x_317_, 1);
lean_inc_ref(v_arg_320_);
v___x_321_ = l_Lean_Expr_appFnCleanup___redArg(v___x_317_);
v___x_322_ = l_Lean_Expr_isApp(v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; 
lean_dec_ref(v___x_321_);
lean_dec_ref(v_arg_320_);
lean_dec_ref(v_arg_316_);
lean_dec_ref(v_arg_295_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_323_ = lean_box(2);
return v___x_323_;
}
else
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = l_Lean_Expr_appFnCleanup___redArg(v___x_321_);
v___x_325_ = l_Lean_Expr_isApp(v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
lean_dec_ref(v___x_324_);
lean_dec_ref(v_arg_320_);
lean_dec_ref(v_arg_316_);
lean_dec_ref(v_arg_295_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_326_ = lean_box(2);
return v___x_326_;
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_327_ = l_Lean_Expr_appFnCleanup___redArg(v___x_324_);
v___x_328_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__4));
v___x_329_ = l_Lean_Expr_isConstOf(v___x_327_, v___x_328_);
lean_dec_ref(v___x_327_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
lean_dec_ref(v_arg_320_);
lean_dec_ref(v_arg_316_);
lean_dec_ref(v_arg_295_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_330_ = lean_box(2);
return v___x_330_;
}
else
{
lean_object* v_snd_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_347_; 
v_snd_331_ = lean_ctor_get(v_snd_281_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v_snd_281_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; 
v_unused_348_ = lean_ctor_get(v_snd_281_, 0);
lean_dec(v_unused_348_);
v___x_333_ = v_snd_281_;
v_isShared_334_ = v_isSharedCheck_347_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_snd_331_);
lean_dec(v_snd_281_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_347_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_335_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5));
lean_inc_ref(v_arg_295_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v___x_335_);
lean_ctor_set(v___x_333_, 0, v_arg_295_);
v___x_337_ = v___x_333_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_arg_295_);
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
lean_ctor_set(v___x_344_, 0, v_snd_331_);
lean_ctor_set(v___x_344_, 1, v_arg_320_);
lean_ctor_set(v___x_344_, 2, v_arg_316_);
lean_ctor_set(v___x_344_, 3, v___x_342_);
lean_ctor_set(v___x_344_, 4, v_arg_295_);
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
lean_object* v_arg_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v_arg_589_ = lean_ctor_get(v___x_587_, 1);
lean_inc_ref(v_arg_589_);
v___x_590_ = l_Lean_Expr_appFnCleanup___redArg(v___x_587_);
v___x_591_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1));
v___x_592_ = l_Lean_Expr_isConstOf(v___x_590_, v___x_591_);
lean_dec_ref(v___x_590_);
if (v___x_592_ == 0)
{
lean_dec_ref(v_arg_589_);
lean_dec(v___x_585_);
lean_dec(v_inv_566_);
goto v___jp_576_;
}
else
{
lean_object* v___x_593_; lean_object* v_00_u03c3_594_; lean_object* v___x_595_; size_t v_sz_596_; size_t v___x_597_; lean_object* v___x_598_; 
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
lean_ctor_set(v___x_605_, 0, v_arg_589_);
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_arg_589_);
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
lean_dec_ref(v_arg_589_);
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
lean_dec_ref(v_arg_589_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(lean_object* v_dontRevert_638_, lean_object* v_as_639_, size_t v_i_640_, size_t v_stop_641_, lean_object* v_b_642_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2___boxed(lean_object* v_dontRevert_653_, lean_object* v_as_654_, lean_object* v_i_655_, lean_object* v_stop_656_, lean_object* v_b_657_){
_start:
{
size_t v_i_boxed_658_; size_t v_stop_boxed_659_; lean_object* v_res_660_; 
v_i_boxed_658_ = lean_unbox_usize(v_i_655_);
lean_dec(v_i_655_);
v_stop_boxed_659_ = lean_unbox_usize(v_stop_656_);
lean_dec(v_stop_656_);
v_res_660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_653_, v_as_654_, v_i_boxed_658_, v_stop_boxed_659_, v_b_657_);
lean_dec_ref(v_as_654_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(size_t v_sz_661_, size_t v_i_662_, lean_object* v_bs_663_){
_start:
{
uint8_t v___x_664_; 
v___x_664_ = lean_usize_dec_lt(v_i_662_, v_sz_661_);
if (v___x_664_ == 0)
{
return v_bs_663_;
}
else
{
lean_object* v_v_665_; lean_object* v___x_666_; lean_object* v_bs_x27_667_; lean_object* v___x_668_; size_t v___x_669_; size_t v___x_670_; lean_object* v___x_671_; 
v_v_665_ = lean_array_uget(v_bs_663_, v_i_662_);
v___x_666_ = lean_unsigned_to_nat(0u);
v_bs_x27_667_ = lean_array_uset(v_bs_663_, v_i_662_, v___x_666_);
v___x_668_ = l_Lean_mkFVar(v_v_665_);
v___x_669_ = ((size_t)1ULL);
v___x_670_ = lean_usize_add(v_i_662_, v___x_669_);
v___x_671_ = lean_array_uset(v_bs_x27_667_, v_i_662_, v___x_668_);
v_i_662_ = v___x_670_;
v_bs_663_ = v___x_671_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1___boxed(lean_object* v_sz_673_, lean_object* v_i_674_, lean_object* v_bs_675_){
_start:
{
size_t v_sz_boxed_676_; size_t v_i_boxed_677_; lean_object* v_res_678_; 
v_sz_boxed_676_ = lean_unbox_usize(v_sz_673_);
lean_dec(v_sz_673_);
v_i_boxed_677_ = lean_unbox_usize(v_i_674_);
lean_dec(v_i_674_);
v_res_678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_boxed_676_, v_i_boxed_677_, v_bs_675_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(size_t v_sz_679_, size_t v_i_680_, lean_object* v_bs_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
uint8_t v___x_687_; 
v___x_687_ = lean_usize_dec_lt(v_i_680_, v_sz_679_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; 
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v_bs_681_);
return v___x_688_;
}
else
{
lean_object* v_v_689_; lean_object* v___x_690_; lean_object* v_bs_x27_691_; lean_object* v___x_692_; 
v_v_689_ = lean_array_uget(v_bs_681_, v_i_680_);
v___x_690_ = lean_unsigned_to_nat(0u);
v_bs_x27_691_ = lean_array_uset(v_bs_681_, v_i_680_, v___x_690_);
lean_inc(v___y_685_);
lean_inc_ref(v___y_684_);
lean_inc(v___y_683_);
lean_inc_ref(v___y_682_);
v___x_692_ = lean_infer_type(v_v_689_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; size_t v___x_694_; size_t v___x_695_; lean_object* v___x_696_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
v___x_694_ = ((size_t)1ULL);
v___x_695_ = lean_usize_add(v_i_680_, v___x_694_);
v___x_696_ = lean_array_uset(v_bs_x27_691_, v_i_680_, v_a_693_);
v_i_680_ = v___x_695_;
v_bs_681_ = v___x_696_;
goto _start;
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec_ref(v_bs_x27_691_);
v_a_698_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_692_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_692_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0___boxed(lean_object* v_sz_706_, lean_object* v_i_707_, lean_object* v_bs_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
size_t v_sz_boxed_714_; size_t v_i_boxed_715_; lean_object* v_res_716_; 
v_sz_boxed_714_ = lean_unbox_usize(v_sz_706_);
lean_dec(v_sz_706_);
v_i_boxed_715_ = lean_unbox_usize(v_i_707_);
lean_dec(v_i_707_);
v_res_716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(v_sz_boxed_714_, v_i_boxed_715_, v_bs_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(lean_object* v_dontRevert_717_, lean_object* v_as_718_, size_t v_i_719_, size_t v_stop_720_, lean_object* v_b_721_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5___boxed(lean_object* v_dontRevert_733_, lean_object* v_as_734_, lean_object* v_i_735_, lean_object* v_stop_736_, lean_object* v_b_737_){
_start:
{
size_t v_i_boxed_738_; size_t v_stop_boxed_739_; lean_object* v_res_740_; 
v_i_boxed_738_ = lean_unbox_usize(v_i_735_);
lean_dec(v_i_735_);
v_stop_boxed_739_ = lean_unbox_usize(v_stop_736_);
lean_dec(v_stop_736_);
v_res_740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_733_, v_as_734_, v_i_boxed_738_, v_stop_boxed_739_, v_b_737_);
lean_dec_ref(v_as_734_);
return v_res_740_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(lean_object* v_a_741_, lean_object* v_x_742_){
_start:
{
if (lean_obj_tag(v_x_742_) == 0)
{
uint8_t v___x_743_; 
v___x_743_ = 0;
return v___x_743_;
}
else
{
lean_object* v_key_744_; lean_object* v_tail_745_; uint8_t v___x_746_; 
v_key_744_ = lean_ctor_get(v_x_742_, 0);
v_tail_745_ = lean_ctor_get(v_x_742_, 2);
v___x_746_ = lean_expr_eqv(v_key_744_, v_a_741_);
if (v___x_746_ == 0)
{
v_x_742_ = v_tail_745_;
goto _start;
}
else
{
return v___x_746_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_a_748_, lean_object* v_x_749_){
_start:
{
uint8_t v_res_750_; lean_object* v_r_751_; 
v_res_750_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_748_, v_x_749_);
lean_dec(v_x_749_);
lean_dec_ref(v_a_748_);
v_r_751_ = lean_box(v_res_750_);
return v_r_751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(lean_object* v_x_752_, lean_object* v_x_753_){
_start:
{
if (lean_obj_tag(v_x_753_) == 0)
{
return v_x_752_;
}
else
{
lean_object* v_key_754_; lean_object* v_value_755_; lean_object* v_tail_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_779_; 
v_key_754_ = lean_ctor_get(v_x_753_, 0);
v_value_755_ = lean_ctor_get(v_x_753_, 1);
v_tail_756_ = lean_ctor_get(v_x_753_, 2);
v_isSharedCheck_779_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_779_ == 0)
{
v___x_758_ = v_x_753_;
v_isShared_759_ = v_isSharedCheck_779_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_tail_756_);
lean_inc(v_value_755_);
lean_inc(v_key_754_);
lean_dec(v_x_753_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_779_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; uint64_t v___x_761_; uint64_t v___x_762_; uint64_t v___x_763_; uint64_t v_fold_764_; uint64_t v___x_765_; uint64_t v___x_766_; uint64_t v___x_767_; size_t v___x_768_; size_t v___x_769_; size_t v___x_770_; size_t v___x_771_; size_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_760_ = lean_array_get_size(v_x_752_);
v___x_761_ = l_Lean_Expr_hash(v_key_754_);
v___x_762_ = 32ULL;
v___x_763_ = lean_uint64_shift_right(v___x_761_, v___x_762_);
v_fold_764_ = lean_uint64_xor(v___x_761_, v___x_763_);
v___x_765_ = 16ULL;
v___x_766_ = lean_uint64_shift_right(v_fold_764_, v___x_765_);
v___x_767_ = lean_uint64_xor(v_fold_764_, v___x_766_);
v___x_768_ = lean_uint64_to_usize(v___x_767_);
v___x_769_ = lean_usize_of_nat(v___x_760_);
v___x_770_ = ((size_t)1ULL);
v___x_771_ = lean_usize_sub(v___x_769_, v___x_770_);
v___x_772_ = lean_usize_land(v___x_768_, v___x_771_);
v___x_773_ = lean_array_uget_borrowed(v_x_752_, v___x_772_);
lean_inc(v___x_773_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 2, v___x_773_);
v___x_775_ = v___x_758_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_key_754_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_value_755_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v___x_773_);
v___x_775_ = v_reuseFailAlloc_778_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_776_; 
v___x_776_ = lean_array_uset(v_x_752_, v___x_772_, v___x_775_);
v_x_752_ = v___x_776_;
v_x_753_ = v_tail_756_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(lean_object* v_i_780_, lean_object* v_source_781_, lean_object* v_target_782_){
_start:
{
lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_783_ = lean_array_get_size(v_source_781_);
v___x_784_ = lean_nat_dec_lt(v_i_780_, v___x_783_);
if (v___x_784_ == 0)
{
lean_dec_ref(v_source_781_);
lean_dec(v_i_780_);
return v_target_782_;
}
else
{
lean_object* v_es_785_; lean_object* v___x_786_; lean_object* v_source_787_; lean_object* v_target_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v_es_785_ = lean_array_fget(v_source_781_, v_i_780_);
v___x_786_ = lean_box(0);
v_source_787_ = lean_array_fset(v_source_781_, v_i_780_, v___x_786_);
v_target_788_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(v_target_782_, v_es_785_);
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_add(v_i_780_, v___x_789_);
lean_dec(v_i_780_);
v_i_780_ = v___x_790_;
v_source_781_ = v_source_787_;
v_target_782_ = v_target_788_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(lean_object* v_data_792_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v_nbuckets_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_793_ = lean_array_get_size(v_data_792_);
v___x_794_ = lean_unsigned_to_nat(2u);
v_nbuckets_795_ = lean_nat_mul(v___x_793_, v___x_794_);
v___x_796_ = lean_unsigned_to_nat(0u);
v___x_797_ = lean_box(0);
v___x_798_ = lean_mk_array(v_nbuckets_795_, v___x_797_);
v___x_799_ = lean_array_propagate_mark(v_data_792_, v___x_798_);
v___x_800_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(v___x_796_, v_data_792_, v___x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(lean_object* v_m_801_, lean_object* v_a_802_, lean_object* v_b_803_){
_start:
{
lean_object* v_size_804_; lean_object* v_buckets_805_; lean_object* v___x_806_; uint64_t v___x_807_; uint64_t v___x_808_; uint64_t v___x_809_; uint64_t v_fold_810_; uint64_t v___x_811_; uint64_t v___x_812_; uint64_t v___x_813_; size_t v___x_814_; size_t v___x_815_; size_t v___x_816_; size_t v___x_817_; size_t v___x_818_; lean_object* v_bkt_819_; uint8_t v___x_820_; 
v_size_804_ = lean_ctor_get(v_m_801_, 0);
v_buckets_805_ = lean_ctor_get(v_m_801_, 1);
v___x_806_ = lean_array_get_size(v_buckets_805_);
v___x_807_ = l_Lean_Expr_hash(v_a_802_);
v___x_808_ = 32ULL;
v___x_809_ = lean_uint64_shift_right(v___x_807_, v___x_808_);
v_fold_810_ = lean_uint64_xor(v___x_807_, v___x_809_);
v___x_811_ = 16ULL;
v___x_812_ = lean_uint64_shift_right(v_fold_810_, v___x_811_);
v___x_813_ = lean_uint64_xor(v_fold_810_, v___x_812_);
v___x_814_ = lean_uint64_to_usize(v___x_813_);
v___x_815_ = lean_usize_of_nat(v___x_806_);
v___x_816_ = ((size_t)1ULL);
v___x_817_ = lean_usize_sub(v___x_815_, v___x_816_);
v___x_818_ = lean_usize_land(v___x_814_, v___x_817_);
v_bkt_819_ = lean_array_uget_borrowed(v_buckets_805_, v___x_818_);
v___x_820_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_802_, v_bkt_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_841_; 
lean_inc_ref(v_buckets_805_);
lean_inc(v_size_804_);
v_isSharedCheck_841_ = !lean_is_exclusive(v_m_801_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; lean_object* v_unused_843_; 
v_unused_842_ = lean_ctor_get(v_m_801_, 1);
lean_dec(v_unused_842_);
v_unused_843_ = lean_ctor_get(v_m_801_, 0);
lean_dec(v_unused_843_);
v___x_822_ = v_m_801_;
v_isShared_823_ = v_isSharedCheck_841_;
goto v_resetjp_821_;
}
else
{
lean_dec(v_m_801_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_841_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v_size_x27_825_; lean_object* v___x_826_; lean_object* v_buckets_x27_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_824_ = lean_unsigned_to_nat(1u);
v_size_x27_825_ = lean_nat_add(v_size_804_, v___x_824_);
lean_dec(v_size_804_);
lean_inc(v_bkt_819_);
v___x_826_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_826_, 0, v_a_802_);
lean_ctor_set(v___x_826_, 1, v_b_803_);
lean_ctor_set(v___x_826_, 2, v_bkt_819_);
v_buckets_x27_827_ = lean_array_uset(v_buckets_805_, v___x_818_, v___x_826_);
v___x_828_ = lean_unsigned_to_nat(4u);
v___x_829_ = lean_nat_mul(v_size_x27_825_, v___x_828_);
v___x_830_ = lean_unsigned_to_nat(3u);
v___x_831_ = lean_nat_div(v___x_829_, v___x_830_);
lean_dec(v___x_829_);
v___x_832_ = lean_array_get_size(v_buckets_x27_827_);
v___x_833_ = lean_nat_dec_le(v___x_831_, v___x_832_);
lean_dec(v___x_831_);
if (v___x_833_ == 0)
{
lean_object* v_val_834_; lean_object* v___x_836_; 
v_val_834_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(v_buckets_x27_827_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v_val_834_);
lean_ctor_set(v___x_822_, 0, v_size_x27_825_);
v___x_836_ = v___x_822_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_size_x27_825_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_val_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
else
{
lean_object* v___x_839_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v_buckets_x27_827_);
lean_ctor_set(v___x_822_, 0, v_size_x27_825_);
v___x_839_ = v___x_822_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_size_x27_825_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_buckets_x27_827_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
else
{
lean_dec(v_b_803_);
lean_dec_ref(v_a_802_);
return v_m_801_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(lean_object* v_as_844_, size_t v_sz_845_, size_t v_i_846_, lean_object* v_b_847_){
_start:
{
uint8_t v___x_848_; 
v___x_848_ = lean_usize_dec_lt(v_i_846_, v_sz_845_);
if (v___x_848_ == 0)
{
return v_b_847_;
}
else
{
lean_object* v_a_849_; lean_object* v___x_850_; lean_object* v_r_851_; size_t v___x_852_; size_t v___x_853_; 
v_a_849_ = lean_array_uget_borrowed(v_as_844_, v_i_846_);
v___x_850_ = lean_box(0);
lean_inc(v_a_849_);
v_r_851_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v_b_847_, v_a_849_, v___x_850_);
v___x_852_ = ((size_t)1ULL);
v___x_853_ = lean_usize_add(v_i_846_, v___x_852_);
v_i_846_ = v___x_853_;
v_b_847_ = v_r_851_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4___boxed(lean_object* v_as_855_, lean_object* v_sz_856_, lean_object* v_i_857_, lean_object* v_b_858_){
_start:
{
size_t v_sz_boxed_859_; size_t v_i_boxed_860_; lean_object* v_res_861_; 
v_sz_boxed_859_ = lean_unbox_usize(v_sz_856_);
lean_dec(v_sz_856_);
v_i_boxed_860_ = lean_unbox_usize(v_i_857_);
lean_dec(v_i_857_);
v_res_861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(v_as_855_, v_sz_boxed_859_, v_i_boxed_860_, v_b_858_);
lean_dec_ref(v_as_855_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(lean_object* v_m_862_, lean_object* v_l_863_){
_start:
{
size_t v_sz_864_; size_t v___x_865_; lean_object* v___x_866_; 
v_sz_864_ = lean_array_size(v_l_863_);
v___x_865_ = ((size_t)0ULL);
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(v_l_863_, v_sz_864_, v___x_865_, v_m_862_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3___boxed(lean_object* v_m_867_, lean_object* v_l_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(v_m_867_, v_l_868_);
lean_dec_ref(v_l_868_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(lean_object* v_as_870_, size_t v_i_871_, size_t v_stop_872_, lean_object* v_b_873_){
_start:
{
uint8_t v___x_874_; 
v___x_874_ = lean_usize_dec_eq(v_i_871_, v_stop_872_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; size_t v___x_877_; size_t v___x_878_; 
v___x_875_ = lean_array_uget_borrowed(v_as_870_, v_i_871_);
lean_inc(v___x_875_);
v___x_876_ = l_Lean_collectFVars(v_b_873_, v___x_875_);
v___x_877_ = ((size_t)1ULL);
v___x_878_ = lean_usize_add(v_i_871_, v___x_877_);
v_i_871_ = v___x_878_;
v_b_873_ = v___x_876_;
goto _start;
}
else
{
return v_b_873_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4___boxed(lean_object* v_as_880_, lean_object* v_i_881_, lean_object* v_stop_882_, lean_object* v_b_883_){
_start:
{
size_t v_i_boxed_884_; size_t v_stop_boxed_885_; lean_object* v_res_886_; 
v_i_boxed_884_ = lean_unbox_usize(v_i_881_);
lean_dec(v_i_881_);
v_stop_boxed_885_ = lean_unbox_usize(v_stop_882_);
lean_dec(v_stop_882_);
v_res_886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_as_880_, v_i_boxed_884_, v_stop_boxed_885_, v_b_883_);
lean_dec_ref(v_as_880_);
return v_res_886_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = lean_box(0);
v___x_890_ = lean_unsigned_to_nat(16u);
v___x_891_ = lean_mk_array(v___x_890_, v___x_889_);
return v___x_891_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1);
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v___x_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(lean_object* v_dontRevert_895_, lean_object* v_a_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v___x_902_; size_t v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___x_914_; lean_object* v___x_915_; size_t v___y_917_; lean_object* v___y_918_; lean_object* v_fvarIds_919_; uint8_t v___x_924_; uint8_t v___x_925_; lean_object* v___x_926_; 
v___x_902_ = lean_unsigned_to_nat(0u);
v___x_914_ = lean_box(1);
v___x_915_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_924_ = 0;
v___x_925_ = 1;
lean_inc_ref(v_a_896_);
v___x_926_ = l_Lean_Meta_collectForwardDeps(v_a_896_, v___x_924_, v___x_925_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_964_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_964_ == 0)
{
v___x_929_ = v___x_926_;
v_isShared_930_ = v_isSharedCheck_964_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_926_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_964_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___y_932_; lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_959_ = lean_array_get_size(v_a_927_);
v___x_960_ = lean_nat_dec_lt(v___x_902_, v___x_959_);
if (v___x_960_ == 0)
{
lean_dec(v_a_927_);
v___y_932_ = v___x_915_;
goto v___jp_931_;
}
else
{
size_t v___x_961_; size_t v___x_962_; lean_object* v___x_963_; 
v___x_961_ = ((size_t)0ULL);
v___x_962_ = lean_usize_of_nat(v___x_959_);
lean_inc_ref(v_dontRevert_895_);
v___x_963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_895_, v_a_927_, v___x_961_, v___x_962_, v___x_915_);
lean_dec(v_a_927_);
v___y_932_ = v___x_963_;
goto v___jp_931_;
}
v___jp_931_:
{
lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_933_ = lean_array_get_size(v___y_932_);
v___x_934_ = lean_array_get_size(v_a_896_);
lean_dec_ref(v_a_896_);
v___x_935_ = lean_nat_dec_eq(v___x_933_, v___x_934_);
if (v___x_935_ == 0)
{
size_t v_sz_936_; size_t v___x_937_; lean_object* v___x_938_; 
lean_del_object(v___x_929_);
v_sz_936_ = lean_array_size(v___y_932_);
v___x_937_ = ((size_t)0ULL);
lean_inc_ref(v___y_932_);
v___x_938_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(v_sz_936_, v___x_937_, v___y_932_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_939_);
lean_dec_ref_known(v___x_938_, 1);
v___x_940_ = lean_array_get_size(v_a_939_);
v___x_941_ = lean_nat_dec_lt(v___x_902_, v___x_940_);
if (v___x_941_ == 0)
{
lean_dec(v_a_939_);
v___y_917_ = v___x_937_;
v___y_918_ = v___y_932_;
v_fvarIds_919_ = v___x_915_;
goto v___jp_916_;
}
else
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; size_t v___x_945_; lean_object* v___x_946_; lean_object* v_fvarIds_947_; 
v___x_942_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2);
v___x_943_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(v___x_942_, v___y_932_);
v___x_944_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v___x_914_);
lean_ctor_set(v___x_944_, 2, v___x_915_);
v___x_945_ = lean_usize_of_nat(v___x_940_);
v___x_946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_a_939_, v___x_937_, v___x_945_, v___x_944_);
lean_dec(v_a_939_);
v_fvarIds_947_ = lean_ctor_get(v___x_946_, 2);
lean_inc_ref(v_fvarIds_947_);
lean_dec_ref(v___x_946_);
v___y_917_ = v___x_937_;
v___y_918_ = v___y_932_;
v_fvarIds_919_ = v_fvarIds_947_;
goto v___jp_916_;
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref(v___y_932_);
lean_dec_ref(v_dontRevert_895_);
v_a_948_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_938_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_938_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
else
{
lean_object* v___x_957_; 
lean_dec_ref(v_dontRevert_895_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___y_932_);
v___x_957_ = v___x_929_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___y_932_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_896_);
lean_dec_ref(v_dontRevert_895_);
return v___x_926_;
}
v___jp_903_:
{
size_t v_sz_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v_sz_907_ = lean_array_size(v___y_906_);
lean_inc_ref(v___y_906_);
v___x_908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_907_, v___y_904_, v___y_906_);
v___x_909_ = l_Array_append___redArg(v___y_905_, v___x_908_);
lean_dec_ref(v___x_908_);
v___x_910_ = lean_array_get_size(v___y_906_);
lean_dec_ref(v___y_906_);
v___x_911_ = lean_nat_dec_eq(v___x_910_, v___x_902_);
if (v___x_911_ == 0)
{
v_a_896_ = v___x_909_;
goto _start;
}
else
{
lean_object* v___x_913_; 
lean_dec_ref(v_dontRevert_895_);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_909_);
return v___x_913_;
}
}
v___jp_916_:
{
lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_920_ = lean_array_get_size(v_fvarIds_919_);
v___x_921_ = lean_nat_dec_lt(v___x_902_, v___x_920_);
if (v___x_921_ == 0)
{
lean_dec_ref(v_fvarIds_919_);
v___y_904_ = v___y_917_;
v___y_905_ = v___y_918_;
v___y_906_ = v___x_915_;
goto v___jp_903_;
}
else
{
size_t v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_usize_of_nat(v___x_920_);
lean_inc_ref(v_dontRevert_895_);
v___x_923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_895_, v_fvarIds_919_, v___y_917_, v___x_922_, v___x_915_);
lean_dec_ref(v_fvarIds_919_);
v___y_904_ = v___y_917_;
v___y_905_ = v___y_918_;
v___y_906_ = v___x_923_;
goto v___jp_903_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___boxed(lean_object* v_dontRevert_965_, lean_object* v_a_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_965_, v_a_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_972_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_973_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_974_ = lean_box(1);
v___x_975_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2);
v___x_976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set(v___x_976_, 1, v___x_974_);
lean_ctor_set(v___x_976_, 2, v___x_973_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(lean_object* v_e_977_, lean_object* v_dontRevert_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v___y_985_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v_fvarIds_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_990_ = lean_unsigned_to_nat(0u);
v___x_991_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_992_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0);
v___x_993_ = l_Lean_collectFVars(v___x_992_, v_e_977_);
v_fvarIds_994_ = lean_ctor_get(v___x_993_, 2);
lean_inc_ref(v_fvarIds_994_);
lean_dec_ref(v___x_993_);
v___x_995_ = lean_array_get_size(v_fvarIds_994_);
v___x_996_ = lean_nat_dec_lt(v___x_990_, v___x_995_);
if (v___x_996_ == 0)
{
lean_dec_ref(v_fvarIds_994_);
v___y_985_ = v___x_991_;
goto v___jp_984_;
}
else
{
size_t v___x_997_; size_t v___x_998_; lean_object* v___x_999_; 
v___x_997_ = ((size_t)0ULL);
v___x_998_ = lean_usize_of_nat(v___x_995_);
lean_inc_ref(v_dontRevert_978_);
v___x_999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_978_, v_fvarIds_994_, v___x_997_, v___x_998_, v___x_991_);
lean_dec_ref(v_fvarIds_994_);
v___y_985_ = v___x_999_;
goto v___jp_984_;
}
v___jp_984_:
{
size_t v_sz_986_; size_t v___x_987_; lean_object* v_xs_988_; lean_object* v___x_989_; 
v_sz_986_ = lean_array_size(v___y_985_);
v___x_987_ = ((size_t)0ULL);
v_xs_988_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_986_, v___x_987_, v___y_985_);
v___x_989_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_978_, v_xs_988_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
return v___x_989_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___boxed(lean_object* v_e_1000_, lean_object* v_dontRevert_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1000_, v_dontRevert_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(lean_object* v_dontRevert_1008_, lean_object* v_inst_1009_, lean_object* v_a_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_1008_, v_a_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___boxed(lean_object* v_dontRevert_1017_, lean_object* v_inst_1018_, lean_object* v_a_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(v_dontRevert_1017_, v_inst_1018_, v_a_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3(lean_object* v_00_u03b2_1026_, lean_object* v_m_1027_, lean_object* v_a_1028_, lean_object* v_b_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v_m_1027_, v_a_1028_, v_b_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_1031_, lean_object* v_a_1032_, lean_object* v_x_1033_){
_start:
{
uint8_t v___x_1034_; 
v___x_1034_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_1032_, v_x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1035_, lean_object* v_a_1036_, lean_object* v_x_1037_){
_start:
{
uint8_t v_res_1038_; lean_object* v_r_1039_; 
v_res_1038_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(v_00_u03b2_1035_, v_a_1036_, v_x_1037_);
lean_dec(v_x_1037_);
lean_dec_ref(v_a_1036_);
v_r_1039_ = lean_box(v_res_1038_);
return v_r_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5(lean_object* v_00_u03b2_1040_, lean_object* v_data_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(v_data_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_1043_, lean_object* v_i_1044_, lean_object* v_source_1045_, lean_object* v_target_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(v_i_1044_, v_source_1045_, v_target_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11(lean_object* v_00_u03b2_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(v_x_1049_, v_x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(lean_object* v_a_1058_, lean_object* v___x_1059_, lean_object* v___x_1060_, lean_object* v_i_1061_, lean_object* v_a_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_zero_1068_; uint8_t v_isZero_1069_; 
v_zero_1068_ = lean_unsigned_to_nat(0u);
v_isZero_1069_ = lean_nat_dec_eq(v_i_1061_, v_zero_1068_);
if (v_isZero_1069_ == 1)
{
lean_object* v___x_1070_; 
lean_dec(v_i_1061_);
lean_dec(v___x_1060_);
lean_dec_ref(v___x_1059_);
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v_a_1062_);
return v___x_1070_;
}
else
{
lean_object* v_one_1071_; lean_object* v_n_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_one_1071_ = lean_unsigned_to_nat(1u);
v_n_1072_ = lean_nat_sub(v_i_1061_, v_one_1071_);
lean_dec(v_i_1061_);
v___x_1073_ = lean_array_fget_borrowed(v_a_1058_, v_n_1072_);
lean_inc_ref(v___x_1059_);
v___x_1074_ = l_Lean_LocalContext_getFVar_x21(v___x_1059_, v___x_1073_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_userName_1075_; lean_object* v_type_1076_; uint8_t v_bi_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v_userName_1075_ = lean_ctor_get(v___x_1074_, 2);
lean_inc(v_userName_1075_);
v_type_1076_ = lean_ctor_get(v___x_1074_, 3);
lean_inc_ref(v_type_1076_);
v_bi_1077_ = lean_ctor_get_uint8(v___x_1074_, sizeof(void*)*4);
lean_dec_ref_known(v___x_1074_, 4);
v___x_1078_ = l_Lean_Expr_headBeta(v_type_1076_);
v___x_1079_ = lean_expr_abstract_range(v___x_1078_, v_n_1072_, v_a_1058_);
lean_dec_ref(v___x_1078_);
lean_inc_ref(v___x_1079_);
v___x_1080_ = l_Lean_Meta_getLevel(v___x_1079_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v___x_1080_, 1);
v___x_1082_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_1083_ = lean_box(0);
lean_inc_n(v___x_1060_, 2);
v___x_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1060_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1085_, 0, v_a_1081_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = l_Lean_mkConst(v___x_1082_, v___x_1085_);
v___x_1087_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v___x_1060_);
lean_inc_ref(v___x_1079_);
v___x_1088_ = l_Lean_mkLambda(v_userName_1075_, v_bi_1077_, v___x_1079_, v_a_1062_);
v___x_1089_ = l_Lean_mkApp3(v___x_1086_, v___x_1079_, v___x_1087_, v___x_1088_);
v_i_1061_ = v_n_1072_;
v_a_1062_ = v___x_1089_;
goto _start;
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec_ref(v___x_1079_);
lean_dec(v_userName_1075_);
lean_dec(v_n_1072_);
lean_dec_ref(v_a_1062_);
lean_dec(v___x_1060_);
lean_dec_ref(v___x_1059_);
v_a_1091_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1080_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1080_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
else
{
uint8_t v_nondep_1099_; 
v_nondep_1099_ = lean_ctor_get_uint8(v___x_1074_, sizeof(void*)*5);
if (v_nondep_1099_ == 0)
{
lean_object* v_userName_1100_; lean_object* v_type_1101_; lean_object* v_value_1102_; uint8_t v___x_1103_; 
v_userName_1100_ = lean_ctor_get(v___x_1074_, 2);
lean_inc(v_userName_1100_);
v_type_1101_ = lean_ctor_get(v___x_1074_, 3);
lean_inc_ref(v_type_1101_);
v_value_1102_ = lean_ctor_get(v___x_1074_, 4);
lean_inc_ref(v_value_1102_);
lean_dec_ref_known(v___x_1074_, 5);
v___x_1103_ = lean_expr_has_loose_bvar(v_a_1062_, v_zero_1068_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; 
lean_dec_ref(v_value_1102_);
lean_dec_ref(v_type_1101_);
lean_dec(v_userName_1100_);
v___x_1104_ = lean_expr_lower_loose_bvars(v_a_1062_, v_one_1071_, v_one_1071_);
lean_dec_ref(v_a_1062_);
v_i_1061_ = v_n_1072_;
v_a_1062_ = v___x_1104_;
goto _start;
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1106_ = l_Lean_Expr_headBeta(v_type_1101_);
v___x_1107_ = lean_expr_abstract_range(v___x_1106_, v_n_1072_, v_a_1058_);
lean_dec_ref(v___x_1106_);
v___x_1108_ = lean_expr_abstract_range(v_value_1102_, v_n_1072_, v_a_1058_);
lean_dec_ref(v_value_1102_);
v___x_1109_ = l_Lean_Expr_letE___override(v_userName_1100_, v___x_1107_, v___x_1108_, v_a_1062_, v_nondep_1099_);
v_i_1061_ = v_n_1072_;
v_a_1062_ = v___x_1109_;
goto _start;
}
}
else
{
lean_object* v_userName_1111_; lean_object* v_type_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v_userName_1111_ = lean_ctor_get(v___x_1074_, 2);
lean_inc(v_userName_1111_);
v_type_1112_ = lean_ctor_get(v___x_1074_, 3);
lean_inc_ref(v_type_1112_);
lean_dec_ref_known(v___x_1074_, 5);
v___x_1113_ = l_Lean_Expr_headBeta(v_type_1112_);
v___x_1114_ = lean_expr_abstract_range(v___x_1113_, v_n_1072_, v_a_1058_);
lean_dec_ref(v___x_1113_);
lean_inc_ref(v___x_1114_);
v___x_1115_ = l_Lean_Meta_getLevel(v___x_1114_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 1);
v___x_1117_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_1118_ = lean_box(0);
lean_inc_n(v___x_1060_, 2);
v___x_1119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1060_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1120_, 0, v_a_1116_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = l_Lean_mkConst(v___x_1117_, v___x_1120_);
v___x_1122_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v___x_1060_);
v___x_1123_ = 0;
lean_inc_ref(v___x_1114_);
v___x_1124_ = l_Lean_mkLambda(v_userName_1111_, v___x_1123_, v___x_1114_, v_a_1062_);
v___x_1125_ = l_Lean_mkApp3(v___x_1121_, v___x_1114_, v___x_1122_, v___x_1124_);
v_i_1061_ = v_n_1072_;
v_a_1062_ = v___x_1125_;
goto _start;
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec_ref(v___x_1114_);
lean_dec(v_userName_1111_);
lean_dec(v_n_1072_);
lean_dec_ref(v_a_1062_);
lean_dec(v___x_1060_);
lean_dec_ref(v___x_1059_);
v_a_1127_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1115_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1115_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___boxed(lean_object* v_a_1135_, lean_object* v___x_1136_, lean_object* v___x_1137_, lean_object* v_i_1138_, lean_object* v_a_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1135_, v___x_1136_, v___x_1137_, v_i_1138_, v_a_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec_ref(v_a_1135_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(lean_object* v_e_1150_, lean_object* v_dontRevert_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_box(0);
lean_inc_ref(v_e_1150_);
v___x_1158_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1150_, v_dontRevert_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v_lctx_1160_; lean_object* v___x_1161_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
v_lctx_1160_ = lean_ctor_get(v_a_1152_, 2);
lean_inc(v_a_1155_);
lean_inc_ref(v_a_1154_);
lean_inc(v_a_1153_);
lean_inc_ref(v_a_1152_);
lean_inc_ref(v_e_1150_);
v___x_1161_ = lean_infer_type(v_e_1150_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1183_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1164_ = v___x_1161_;
v_isShared_1165_ = v_isSharedCheck_1183_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1161_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1183_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = l_Lean_Expr_cleanupAnnotations(v_a_1162_);
v___x_1167_ = l_Lean_Expr_isApp(v___x_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1169_; 
lean_dec_ref(v___x_1166_);
lean_dec(v_a_1159_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v_e_1150_);
v___x_1169_ = v___x_1164_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_e_1150_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1171_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1166_);
v___x_1172_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___closed__0));
v___x_1173_ = l_Lean_Expr_isConstOf(v___x_1171_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1175_; 
lean_dec_ref(v___x_1171_);
lean_dec(v_a_1159_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v_e_1150_);
v___x_1175_ = v___x_1164_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_e_1150_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_del_object(v___x_1164_);
v___x_1177_ = l_Lean_Expr_constLevels_x21(v___x_1171_);
lean_dec_ref(v___x_1171_);
v___x_1178_ = lean_unsigned_to_nat(0u);
v___x_1179_ = l_List_get_x21Internal___redArg(v___x_1157_, v___x_1177_, v___x_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_array_get_size(v_a_1159_);
v___x_1181_ = lean_expr_abstract(v_e_1150_, v_a_1159_);
lean_dec_ref(v_e_1150_);
lean_inc_ref(v_lctx_1160_);
v___x_1182_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1159_, v_lctx_1160_, v___x_1179_, v___x_1180_, v___x_1181_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
lean_dec(v_a_1159_);
return v___x_1182_;
}
}
}
}
else
{
lean_dec(v_a_1159_);
lean_dec_ref(v_e_1150_);
return v___x_1161_;
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec_ref(v_e_1150_);
v_a_1184_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1158_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1158_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed(lean_object* v_e_1192_, lean_object* v_dontRevert_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(v_e_1192_, v_dontRevert_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(lean_object* v_a_1200_, lean_object* v___x_1201_, lean_object* v___x_1202_, lean_object* v_n_1203_, lean_object* v_i_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1200_, v___x_1201_, v___x_1202_, v_i_1204_, v_a_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___boxed(lean_object* v_a_1213_, lean_object* v___x_1214_, lean_object* v___x_1215_, lean_object* v_n_1216_, lean_object* v_i_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(v_a_1213_, v___x_1214_, v___x_1215_, v_n_1216_, v_i_1217_, v_a_1218_, v_a_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v_n_1216_);
lean_dec_ref(v_a_1213_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(lean_object* v_lvl_1232_, lean_object* v_lhs_1233_, lean_object* v_rhs_1234_){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1235_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
v___x_1236_ = lean_box(0);
lean_inc(v_lvl_1232_);
v___x_1237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_lvl_1232_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = l_Lean_mkConst(v___x_1235_, v___x_1237_);
v___x_1239_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_lvl_1232_);
v___x_1240_ = l_Lean_mkApp3(v___x_1238_, v___x_1239_, v_lhs_1233_, v_rhs_1234_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(lean_object* v_lvl_1247_, lean_object* v_lhs_1248_, lean_object* v_rhs_1249_){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1250_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
v___x_1251_ = lean_box(0);
lean_inc(v_lvl_1247_);
v___x_1252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1252_, 0, v_lvl_1247_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = l_Lean_mkConst(v___x_1250_, v___x_1252_);
v___x_1254_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_lvl_1247_);
v___x_1255_ = l_Lean_mkApp3(v___x_1253_, v___x_1254_, v_lhs_1248_, v_rhs_1249_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(lean_object* v_p_1256_){
_start:
{
lean_object* v_lvl_1257_; lean_object* v_cursorPred_1258_; lean_object* v_letMutsPred_1259_; lean_object* v___x_1260_; 
v_lvl_1257_ = lean_ctor_get(v_p_1256_, 0);
lean_inc(v_lvl_1257_);
v_cursorPred_1258_ = lean_ctor_get(v_p_1256_, 1);
lean_inc_ref(v_cursorPred_1258_);
v_letMutsPred_1259_ = lean_ctor_get(v_p_1256_, 2);
lean_inc_ref(v_letMutsPred_1259_);
lean_dec_ref(v_p_1256_);
v___x_1260_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v_lvl_1257_, v_cursorPred_1258_, v_letMutsPred_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___impl(lean_object* v_x_1261_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_obj_tag_nat(v_x_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___impl___boxed(lean_object* v_x_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___impl(v_x_1263_);
lean_dec(v_x_1263_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(lean_object* v_t_1265_, lean_object* v_k_1266_){
_start:
{
if (lean_obj_tag(v_t_1265_) == 3)
{
lean_object* v_e_1267_; lean_object* v___x_1268_; 
v_e_1267_ = lean_ctor_get(v_t_1265_, 0);
lean_inc_ref(v_e_1267_);
lean_dec_ref_known(v_t_1265_, 1);
v___x_1268_ = lean_apply_1(v_k_1266_, v_e_1267_);
return v___x_1268_;
}
else
{
lean_dec(v_t_1265_);
return v_k_1266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(lean_object* v_motive_1269_, lean_object* v_ctorIdx_1270_, lean_object* v_t_1271_, lean_object* v_h_1272_, lean_object* v_k_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1271_, v_k_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___boxed(lean_object* v_motive_1275_, lean_object* v_ctorIdx_1276_, lean_object* v_t_1277_, lean_object* v_h_1278_, lean_object* v_k_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(v_motive_1275_, v_ctorIdx_1276_, v_t_1277_, v_h_1278_, v_k_1279_);
lean_dec(v_ctorIdx_1276_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim___redArg(lean_object* v_t_1281_, lean_object* v_punit_1282_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1281_, v_punit_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim(lean_object* v_motive_1284_, lean_object* v_t_1285_, lean_object* v_h_1286_, lean_object* v_punit_1287_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1285_, v_punit_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim___redArg(lean_object* v_t_1289_, lean_object* v_false_1290_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1289_, v_false_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim(lean_object* v_motive_1292_, lean_object* v_t_1293_, lean_object* v_h_1294_, lean_object* v_false_1295_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1293_, v_false_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim___redArg(lean_object* v_t_1297_, lean_object* v_true_1298_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1297_, v_true_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim(lean_object* v_motive_1300_, lean_object* v_t_1301_, lean_object* v_h_1302_, lean_object* v_true_1303_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1301_, v_true_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim___redArg(lean_object* v_t_1305_, lean_object* v_other_1306_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1305_, v_other_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim(lean_object* v_motive_1308_, lean_object* v_t_1309_, lean_object* v_h_1310_, lean_object* v_other_1311_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1309_, v_other_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(lean_object* v_a_1313_){
_start:
{
lean_object* v_snd_1315_; lean_object* v_fst_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1355_; 
v_snd_1315_ = lean_ctor_get(v_a_1313_, 1);
v_fst_1316_ = lean_ctor_get(v_a_1313_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_a_1313_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1318_ = v_a_1313_;
v_isShared_1319_ = v_isSharedCheck_1355_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_snd_1315_);
lean_inc(v_fst_1316_);
lean_dec(v_a_1313_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1355_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v_fst_1320_; lean_object* v_snd_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1354_; 
v_fst_1320_ = lean_ctor_get(v_snd_1315_, 0);
v_snd_1321_ = lean_ctor_get(v_snd_1315_, 1);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_snd_1315_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1323_ = v_snd_1315_;
v_isShared_1324_ = v_isSharedCheck_1354_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_snd_1321_);
lean_inc(v_fst_1320_);
lean_dec(v_snd_1315_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1354_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1325_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_1326_ = lean_unsigned_to_nat(4u);
v___x_1327_ = l_Lean_Expr_isAppOfArity(v_fst_1320_, v___x_1325_, v___x_1326_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1329_; 
if (v_isShared_1324_ == 0)
{
v___x_1329_ = v___x_1323_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_fst_1320_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_snd_1321_);
v___x_1329_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1331_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 1, v___x_1329_);
v___x_1331_ = v___x_1318_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_fst_1316_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
return v___x_1332_;
}
}
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1335_ = lean_unsigned_to_nat(3u);
v___x_1336_ = lean_unsigned_to_nat(2u);
v___x_1337_ = l_Lean_Expr_getAppNumArgs(v_fst_1320_);
v___x_1338_ = lean_nat_sub(v___x_1337_, v___x_1336_);
v___x_1339_ = lean_unsigned_to_nat(1u);
v___x_1340_ = lean_nat_sub(v___x_1338_, v___x_1339_);
lean_dec(v___x_1338_);
v___x_1341_ = l_Lean_Expr_getRevArg_x21(v_fst_1320_, v___x_1340_);
v___x_1342_ = lean_array_push(v_snd_1321_, v___x_1341_);
v___x_1343_ = lean_nat_add(v_fst_1316_, v___x_1339_);
lean_dec(v_fst_1316_);
v___x_1344_ = lean_nat_sub(v___x_1337_, v___x_1335_);
lean_dec(v___x_1337_);
v___x_1345_ = lean_nat_sub(v___x_1344_, v___x_1339_);
lean_dec(v___x_1344_);
v___x_1346_ = l_Lean_Expr_getRevArg_x21(v_fst_1320_, v___x_1345_);
lean_dec(v_fst_1320_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 1, v___x_1342_);
lean_ctor_set(v___x_1323_, 0, v___x_1346_);
v___x_1348_ = v___x_1323_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v___x_1342_);
v___x_1348_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1350_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 1, v___x_1348_);
lean_ctor_set(v___x_1318_, 0, v___x_1343_);
v___x_1350_ = v___x_1318_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
v_a_1313_ = v___x_1350_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg___boxed(lean_object* v_a_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_a_1356_);
return v_res_1358_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(lean_object* v_letMutsTuple_1359_, lean_object* v___x_1360_, uint8_t v___x_1361_, lean_object* v_fvarId_1362_){
_start:
{
lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1363_ = l_Lean_Expr_fvarId_x21(v_letMutsTuple_1359_);
v___x_1364_ = l_Lean_instBEqFVarId_beq(v_fvarId_1362_, v___x_1363_);
lean_dec(v___x_1363_);
if (v___x_1364_ == 0)
{
uint8_t v___x_1365_; 
v___x_1365_ = l_Lean_LocalContext_contains(v___x_1360_, v_fvarId_1362_);
return v___x_1365_;
}
else
{
return v___x_1361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1___boxed(lean_object* v_letMutsTuple_1366_, lean_object* v___x_1367_, lean_object* v___x_1368_, lean_object* v_fvarId_1369_){
_start:
{
uint8_t v___x_10026__boxed_1370_; uint8_t v_res_1371_; lean_object* v_r_1372_; 
v___x_10026__boxed_1370_ = lean_unbox(v___x_1368_);
v_res_1371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(v_letMutsTuple_1366_, v___x_1367_, v___x_10026__boxed_1370_, v_fvarId_1369_);
lean_dec(v_fvarId_1369_);
lean_dec_ref(v___x_1367_);
lean_dec_ref(v_letMutsTuple_1366_);
v_r_1372_ = lean_box(v_res_1371_);
return v_r_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(lean_object* v_fst_1373_, lean_object* v_p_1374_){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_inc(v_fst_1373_);
v___x_1375_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_1373_);
v___x_1376_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_1373_, v___x_1375_, v_p_1374_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(lean_object* v_inv_1406_, lean_object* v___x_1407_, lean_object* v_xs_1408_, lean_object* v_letMuts_1409_, lean_object* v_as_1410_, size_t v_sz_1411_, size_t v_i_1412_, lean_object* v_b_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_a_1420_; uint8_t v___x_1424_; 
v___x_1424_ = lean_usize_dec_lt(v_i_1412_, v_sz_1411_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; 
lean_dec_ref(v_letMuts_1409_);
lean_dec_ref(v_xs_1408_);
lean_dec_ref(v___x_1407_);
lean_dec(v_inv_1406_);
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v_b_1413_);
return v___x_1425_;
}
else
{
lean_object* v_snd_1426_; lean_object* v_fst_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1740_; 
v_snd_1426_ = lean_ctor_get(v_b_1413_, 1);
v_fst_1427_ = lean_ctor_get(v_b_1413_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_b_1413_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1429_ = v_b_1413_;
v_isShared_1430_ = v_isSharedCheck_1740_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_snd_1426_);
lean_inc(v_fst_1427_);
lean_dec(v_b_1413_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1740_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v_fst_1431_; lean_object* v_snd_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1739_; 
v_fst_1431_ = lean_ctor_get(v_snd_1426_, 0);
v_snd_1432_ = lean_ctor_get(v_snd_1426_, 1);
v_isSharedCheck_1739_ = !lean_is_exclusive(v_snd_1426_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1434_ = v_snd_1426_;
v_isShared_1435_ = v_isSharedCheck_1739_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_snd_1432_);
lean_inc(v_fst_1431_);
lean_dec(v_snd_1426_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1739_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v_a_1448_; lean_object* v___x_1449_; 
v___x_1445_ = lean_unsigned_to_nat(0u);
v___x_1446_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5));
v___x_1447_ = lean_box(0);
v_a_1448_ = lean_array_uget_borrowed(v_as_1410_, v_i_1412_);
lean_inc(v_a_1448_);
v___x_1449_ = l_Lean_MVarId_getType(v_a_1448_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1451_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1450_);
lean_dec_ref_known(v___x_1449_, 1);
v___x_1451_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_1450_, v___y_1415_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1453_; lean_object* v_prefixPoint_x3f_1455_; lean_object* v_suffixPoint_x3f_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___x_1451_, 1);
v___x_1453_ = l_Lean_Expr_consumeMData(v_a_1452_);
lean_dec(v_a_1452_);
lean_inc_ref(v___x_1453_);
v___x_1564_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed), 6, 1);
lean_closure_set(v___x_1564_, 0, v___x_1453_);
lean_inc(v_a_1448_);
v___x_1565_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_a_1448_, v___x_1564_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
if (lean_obj_tag(v_a_1566_) == 1)
{
lean_object* v_val_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1714_; 
v_val_1567_ = lean_ctor_get(v_a_1566_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_a_1566_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1569_ = v_a_1566_;
v_isShared_1570_ = v_isSharedCheck_1714_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_val_1567_);
lean_dec(v_a_1566_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1714_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v_snd_1571_; lean_object* v_fst_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1713_; 
v_snd_1571_ = lean_ctor_get(v_val_1567_, 1);
v_fst_1572_ = lean_ctor_get(v_val_1567_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_val_1567_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1574_ = v_val_1567_;
v_isShared_1575_ = v_isSharedCheck_1713_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_snd_1571_);
lean_inc(v_fst_1572_);
lean_dec(v_val_1567_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1713_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v_fst_1576_; lean_object* v_snd_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1712_; 
v_fst_1576_ = lean_ctor_get(v_snd_1571_, 0);
v_snd_1577_ = lean_ctor_get(v_snd_1571_, 1);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_snd_1571_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1579_ = v_snd_1571_;
v_isShared_1580_ = v_isSharedCheck_1712_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_snd_1577_);
lean_inc(v_fst_1576_);
lean_dec(v_snd_1571_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1712_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v_prefixPoint_x3f_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___x_1661_; 
lean_inc(v_inv_1406_);
v___x_1661_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_snd_1577_, v_inv_1406_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_invariantUse_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1711_; 
v_invariantUse_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1711_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_invariantUse_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1711_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v_conditionIdx_1666_; lean_object* v_cursorPrefix_1667_; lean_object* v_letMutsTuple_1668_; uint8_t v___x_1669_; 
v_conditionIdx_1666_ = lean_ctor_get(v_invariantUse_1662_, 0);
lean_inc(v_conditionIdx_1666_);
v_cursorPrefix_1667_ = lean_ctor_get(v_invariantUse_1662_, 1);
lean_inc_ref(v_cursorPrefix_1667_);
v_letMutsTuple_1668_ = lean_ctor_get(v_invariantUse_1662_, 4);
lean_inc_ref(v_letMutsTuple_1668_);
lean_dec_ref(v_invariantUse_1662_);
v___x_1669_ = lean_nat_dec_eq(v_conditionIdx_1666_, v___x_1445_);
lean_dec(v_conditionIdx_1666_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_dec_ref(v_letMutsTuple_1668_);
lean_dec_ref(v_cursorPrefix_1667_);
lean_del_object(v___x_1664_);
lean_del_object(v___x_1579_);
lean_dec(v_snd_1577_);
lean_dec(v_fst_1576_);
lean_del_object(v___x_1574_);
lean_dec(v_fst_1572_);
lean_del_object(v___x_1569_);
lean_dec_ref(v___x_1453_);
lean_del_object(v___x_1434_);
lean_del_object(v___x_1429_);
v___x_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1670_, 0, v_fst_1431_);
lean_ctor_set(v___x_1670_, 1, v_snd_1432_);
v___x_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1671_, 0, v_fst_1427_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v_a_1420_ = v___x_1671_;
goto v___jp_1419_;
}
else
{
lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1672_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2));
v___x_1673_ = l_Lean_Expr_isAppOf(v_cursorPrefix_1667_, v___x_1672_);
if (v___x_1673_ == 0)
{
lean_dec_ref(v_letMutsTuple_1668_);
lean_dec_ref(v_cursorPrefix_1667_);
lean_del_object(v___x_1664_);
v_prefixPoint_x3f_1582_ = v_fst_1427_;
v___y_1583_ = v___y_1414_;
v___y_1584_ = v___y_1415_;
v___y_1585_ = v___y_1416_;
v___y_1586_ = v___y_1417_;
goto v___jp_1581_;
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_dec(v_fst_1427_);
v___x_1674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__12));
lean_inc_ref(v_xs_1408_);
v___x_1675_ = l_Lean_Meta_mkProjection(v_xs_1408_, v___x_1674_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1677_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref_known(v___x_1675_, 1);
v___x_1677_ = l_Lean_Meta_mkEq(v_a_1676_, v_cursorPrefix_1667_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1679_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_a_1678_);
lean_dec_ref_known(v___x_1677_, 1);
lean_inc_ref(v_letMuts_1409_);
v___x_1679_ = l_Lean_Meta_mkEq(v_letMuts_1409_, v_letMutsTuple_1668_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1685_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1679_, 1);
lean_inc_n(v_fst_1572_, 3);
v___x_1681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(v_fst_1572_, v_a_1680_);
v___x_1682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(v_fst_1572_, v_a_1678_);
v___x_1683_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1683_, 0, v_fst_1572_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
lean_ctor_set(v___x_1683_, 2, v___x_1681_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set_tag(v___x_1664_, 1);
lean_ctor_set(v___x_1664_, 0, v___x_1683_);
v___x_1685_ = v___x_1664_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
v_prefixPoint_x3f_1582_ = v___x_1685_;
v___y_1583_ = v___y_1414_;
v___y_1584_ = v___y_1415_;
v___y_1585_ = v___y_1416_;
v___y_1586_ = v___y_1417_;
goto v___jp_1581_;
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec(v_a_1678_);
lean_del_object(v___x_1664_);
lean_del_object(v___x_1579_);
lean_dec(v_snd_1577_);
lean_dec(v_fst_1576_);
lean_del_object(v___x_1574_);
lean_dec(v_fst_1572_);
lean_del_object(v___x_1569_);
lean_dec_ref(v___x_1453_);
lean_del_object(v___x_1434_);
lean_dec(v_snd_1432_);
lean_dec(v_fst_1431_);
lean_del_object(v___x_1429_);
lean_dec_ref(v_letMuts_1409_);
lean_dec_ref(v_xs_1408_);
lean_dec_ref(v___x_1407_);
lean_dec(v_inv_1406_);
v_a_1687_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1679_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1679_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_dec_ref(v_letMutsTuple_1668_);
lean_del_object(v___x_1664_);
lean_del_object(v___x_1579_);
lean_dec(v_snd_1577_);
lean_dec(v_fst_1576_);
lean_del_object(v___x_1574_);
lean_dec(v_fst_1572_);
lean_del_object(v___x_1569_);
lean_dec_ref(v___x_1453_);
lean_del_object(v___x_1434_);
lean_dec(v_snd_1432_);
lean_dec(v_fst_1431_);
lean_del_object(v___x_1429_);
lean_dec_ref(v_letMuts_1409_);
lean_dec_ref(v_xs_1408_);
lean_dec_ref(v___x_1407_);
lean_dec(v_inv_1406_);
v_a_1695_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1677_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1677_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec_ref(v_letMutsTuple_1668_);
lean_dec_ref(v_cursorPrefix_1667_);
lean_del_object(v___x_1664_);
lean_del_object(v___x_1579_);
lean_dec(v_snd_1577_);
lean_dec(v_fst_1576_);
lean_del_object(v___x_1574_);
lean_dec(v_fst_1572_);
lean_del_object(v___x_1569_);
lean_dec_ref(v___x_1453_);
lean_del_object(v___x_1434_);
lean_dec(v_snd_1432_);
lean_dec(v_fst_1431_);
lean_del_object(v___x_1429_);
lean_dec_ref(v_letMuts_1409_);
lean_dec_ref(v_xs_1408_);
lean_dec_ref(v___x_1407_);
lean_dec(v_inv_1406_);
v_a_1703_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1675_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1675_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_1661_);
v_prefixPoint_x3f_1582_ = v_fst_1427_;
v___y_1583_ = v___y_1414_;
v___y_1584_ = v___y_1415_;
v___y_1585_ = v___y_1416_;
v___y_1586_ = v___y_1417_;
goto v___jp_1581_;
}
v___jp_1581_:
{
lean_object* v___x_1587_; 
lean_inc(v_inv_1406_);
v___x_1587_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_fst_1576_, v_inv_1406_);
lean_dec(v_fst_1576_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_invariantUse_1588_; lean_object* v_conditionIdx_1589_; lean_object* v_cursorSuffix_1590_; lean_object* v_letMutsTuple_1591_; uint8_t v___x_1592_; 
v_invariantUse_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc_ref(v_invariantUse_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v_conditionIdx_1589_ = lean_ctor_get(v_invariantUse_1588_, 0);
lean_inc(v_conditionIdx_1589_);
v_cursorSuffix_1590_ = lean_ctor_get(v_invariantUse_1588_, 2);
lean_inc_ref(v_cursorSuffix_1590_);
v_letMutsTuple_1591_ = lean_ctor_get(v_invariantUse_1588_, 4);
lean_inc_ref(v_letMutsTuple_1591_);
lean_dec_ref(v_invariantUse_1588_);
v___x_1592_ = lean_nat_dec_eq(v_conditionIdx_1589_, v___x_1445_);
lean_dec(v_conditionIdx_1589_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1594_; 
lean_dec_ref(v_letMutsTuple_1591_);
lean_dec_ref(v_cursorSuffix_1590_);
lean_dec(v_snd_1577_);
lean_dec(v_fst_1572_);
lean_del_object(v___x_1569_);
lean_dec_ref(v___x_1453_);
lean_del_object(v___x_1434_);
lean_del_object(v___x_1429_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 1, v_snd_1432_);
lean_ctor_set(v___x_1579_, 0, v_fst_1431_);
v___x_1594_ = v___x_1579_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_fst_1431_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_snd_1432_);
v___x_1594_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1596_; 
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 1, v___x_1594_);
lean_ctor_set(v___x_1574_, 0, v_prefixPoint_x3f_1582_);
v___x_1596_ = v___x_1574_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_prefixPoint_x3f_1582_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
v_a_1420_ = v___x_1596_;
goto v___jp_1419_;
}
}
}
else
{
lean_object* v___x_1599_; uint8_t v___x_1600_; 
lean_del_object(v___x_1579_);
lean_del_object(v___x_1574_);
v___x_1599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2));
v___x_1600_ = l_Lean_Expr_isAppOf(v_cursorSuffix_1590_, v___x_1599_);
if (v___x_1600_ == 0)
{
lean_dec_ref(v_letMutsTuple_1591_);
lean_dec_ref(v_cursorSuffix_1590_);
lean_dec(v_snd_1577_);
lean_dec(v_fst_1572_);
lean_del_object(v___x_1569_);
v_prefixPoint_x3f_1455_ = v_prefixPoint_x3f_1582_;
v_suffixPoint_x3f_1456_ = v_fst_1431_;
v___y_1457_ = v___y_1583_;
v___y_1458_ = v___y_1584_;
v___y_1459_ = v___y_1585_;
v___y_1460_ = v___y_1586_;
goto v___jp_1454_;
}
else
{
uint8_t v___x_1601_; 
v___x_1601_ = l_Lean_Expr_isFVar(v_letMutsTuple_1591_);
if (v___x_1601_ == 0)
{
lean_dec_ref(v_letMutsTuple_1591_);
lean_dec_ref(v_cursorSuffix_1590_);
lean_dec(v_snd_1577_);
lean_dec(v_fst_1572_);
lean_del_object(v___x_1569_);
v_prefixPoint_x3f_1455_ = v_prefixPoint_x3f_1582_;
v_suffixPoint_x3f_1456_ = v_fst_1431_;
v___y_1457_ = v___y_1583_;
v___y_1458_ = v___y_1584_;
v___y_1459_ = v___y_1585_;
v___y_1460_ = v___y_1586_;
goto v___jp_1454_;
}
else
{
lean_object* v___x_1602_; lean_object* v___f_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1602_ = lean_box(v___x_1592_);
lean_inc_ref(v___x_1407_);
lean_inc_ref(v_letMutsTuple_1591_);
v___f_1603_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1603_, 0, v_letMutsTuple_1591_);
lean_closure_set(v___f_1603_, 1, v___x_1407_);
lean_closure_set(v___f_1603_, 2, v___x_1602_);
v___x_1604_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__10));
lean_inc_ref(v_xs_1408_);
v___x_1605_ = l_Lean_Meta_mkProjection(v_xs_1408_, v___x_1604_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v___x_1607_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref_known(v___x_1605_, 1);
v___x_1607_ = l_Lean_Meta_mkEq(v_a_1606_, v_cursorSuffix_1590_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v___x_1607_, 1);
v___x_1609_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed), 7, 2);
lean_closure_set(v___x_1609_, 0, v_snd_1577_);
lean_closure_set(v___x_1609_, 1, v___f_1603_);
lean_inc(v_a_1448_);
v___x_1610_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_a_1448_, v___x_1609_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1612_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1610_, 1);
v___x_1612_ = l_Lean_Expr_replaceFVar(v_a_1611_, v_letMutsTuple_1591_, v_letMuts_1409_);
lean_dec(v_a_1611_);
if (lean_obj_tag(v_fst_1431_) == 1)
{
lean_object* v_val_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1631_; 
lean_dec(v_a_1608_);
lean_del_object(v___x_1569_);
v_val_1613_ = lean_ctor_get(v_fst_1431_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_fst_1431_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1615_ = v_fst_1431_;
v_isShared_1616_ = v_isSharedCheck_1631_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_val_1613_);
lean_dec(v_fst_1431_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1631_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v_lvl_1617_; lean_object* v_cursorPred_1618_; lean_object* v_letMutsPred_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1630_; 
v_lvl_1617_ = lean_ctor_get(v_val_1613_, 0);
v_cursorPred_1618_ = lean_ctor_get(v_val_1613_, 1);
v_letMutsPred_1619_ = lean_ctor_get(v_val_1613_, 2);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_val_1613_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1621_ = v_val_1613_;
v_isShared_1622_ = v_isSharedCheck_1630_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_letMutsPred_1619_);
lean_inc(v_cursorPred_1618_);
lean_inc(v_lvl_1617_);
lean_dec(v_val_1613_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1630_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1625_; 
v___x_1623_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v_fst_1572_, v_letMutsPred_1619_, v___x_1612_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 2, v___x_1623_);
v___x_1625_ = v___x_1621_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_lvl_1617_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_cursorPred_1618_);
lean_ctor_set(v_reuseFailAlloc_1629_, 2, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1627_; 
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 0, v___x_1625_);
v___x_1627_ = v___x_1615_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
v_prefixPoint_x3f_1455_ = v_prefixPoint_x3f_1582_;
v_suffixPoint_x3f_1456_ = v___x_1627_;
v___y_1457_ = v___y_1583_;
v___y_1458_ = v___y_1584_;
v___y_1459_ = v___y_1585_;
v___y_1460_ = v___y_1586_;
goto v___jp_1454_;
}
}
}
}
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; 
lean_dec(v_fst_1431_);
lean_inc(v_fst_1572_);
v___x_1632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(v_fst_1572_, v_a_1608_);
v___x_1633_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1633_, 0, v_fst_1572_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
lean_ctor_set(v___x_1633_, 2, v___x_1612_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v___x_1633_);
v___x_1635_ = v___x_1569_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
v_prefixPoint_x3f_1455_ = v_prefixPoint_x3f_1582_;
v_suffixPoint_x3f_1456_ = v___x_1635_;
v___y_1457_ = v___y_1583_;
v___y_1458_ = v___y_1584_;
v___y_1459_ = v___y_1585_;
v___y_1460_ = v___y_1586_;
goto v___jp_1454_;
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec(v_a_1608_);
lean_dec_ref(v_letMutsTuple_1591_);
lean_dec(v_prefixPoint_x3f_1582_);
lean_dec(v_fst_1572_);
lean_del_object(v___x_1569_);
lean_dec_ref(v___x_1453_);
lean_del_object(v___x_1434_);
lean_dec(v_snd_1432_);
lean_dec(v_fst_1431_);
lean_del_object(v___x_1429_);
lean_dec_ref(v_letMuts_1409_);
lean_dec_ref(v_xs_1408_);
lean_dec_ref(v___x_1407_);
lean_dec(v_inv_1406_);
v_a_1637_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1610_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1610_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_dec_ref(v___f_1603_);
lean_dec_ref(v_letMutsTuple_1591_);
lean_dec(v_prefixPoint_x3f_1582_);
lean_dec(v_snd_1577_);
lean_dec(v_fst_1572_);
lean_del_object(v___x_1569_);
lean_dec_ref(v___x_1453_);
lean_del_object(v___x_1434_);
lean_dec(v_snd_1432_);
lean_dec(v_fst_1431_);
lean_del_object(v___x_1429_);
lean_dec_ref(v_letMuts_1409_);
lean_dec_ref(v_xs_1408_);
lean_dec_ref(v___x_1407_);
lean_dec(v_inv_1406_);
v_a_1645_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1607_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1607_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec_ref(v___f_1603_);
lean_dec_ref(v_letMutsTuple_1591_);
lean_dec_ref(v_cursorSuffix_1590_);
lean_dec(v_prefixPoint_x3f_1582_);
lean_dec(v_snd_1577_);
lean_dec(v_fst_1572_);
lean_del_object(v___x_1569_);
lean_dec_ref(v___x_1453_);
lean_del_object(v___x_1434_);
lean_dec(v_snd_1432_);
lean_dec(v_fst_1431_);
lean_del_object(v___x_1429_);
lean_dec_ref(v_letMuts_1409_);
lean_dec_ref(v_xs_1408_);
lean_dec_ref(v___x_1407_);
lean_dec(v_inv_1406_);
v_a_1653_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1605_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1605_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_1587_);
lean_del_object(v___x_1579_);
lean_dec(v_snd_1577_);
lean_del_object(v___x_1574_);
lean_dec(v_fst_1572_);
lean_del_object(v___x_1569_);
v_prefixPoint_x3f_1455_ = v_prefixPoint_x3f_1582_;
v_suffixPoint_x3f_1456_ = v_fst_1431_;
v___y_1457_ = v___y_1583_;
v___y_1458_ = v___y_1584_;
v___y_1459_ = v___y_1585_;
v___y_1460_ = v___y_1586_;
goto v___jp_1454_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1566_);
v_prefixPoint_x3f_1455_ = v_fst_1427_;
v_suffixPoint_x3f_1456_ = v_fst_1431_;
v___y_1457_ = v___y_1414_;
v___y_1458_ = v___y_1415_;
v___y_1459_ = v___y_1416_;
v___y_1460_ = v___y_1417_;
goto v___jp_1454_;
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec_ref(v___x_1453_);
lean_del_object(v___x_1434_);
lean_dec(v_snd_1432_);
lean_dec(v_fst_1431_);
lean_del_object(v___x_1429_);
lean_dec(v_fst_1427_);
lean_dec_ref(v_letMuts_1409_);
lean_dec_ref(v_xs_1408_);
lean_dec_ref(v___x_1407_);
lean_dec(v_inv_1406_);
v_a_1715_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1565_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1565_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
v___jp_1454_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1461_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__1));
v___x_1462_ = lean_unsigned_to_nat(3u);
v___x_1463_ = l_Lean_Expr_isAppOfArity(v___x_1453_, v___x_1461_, v___x_1462_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_dec_ref(v___x_1453_);
lean_del_object(v___x_1434_);
lean_del_object(v___x_1429_);
v___x_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1464_, 0, v_suffixPoint_x3f_1456_);
lean_ctor_set(v___x_1464_, 1, v_snd_1432_);
v___x_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1465_, 0, v_prefixPoint_x3f_1455_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v_a_1420_ = v___x_1465_;
goto v___jp_1419_;
}
else
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1466_ = l_Lean_Expr_appFn_x21(v___x_1453_);
v___x_1467_ = l_Lean_Expr_appArg_x21(v___x_1466_);
lean_dec_ref(v___x_1466_);
v___x_1468_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__1));
v___x_1469_ = l_Lean_Expr_isAppOfArity(v___x_1467_, v___x_1468_, v___x_1462_);
if (v___x_1469_ == 0)
{
lean_dec_ref(v___x_1467_);
lean_dec_ref(v___x_1453_);
v___y_1437_ = v_prefixPoint_x3f_1455_;
v___y_1438_ = v_suffixPoint_x3f_1456_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
v___x_1470_ = lean_unsigned_to_nat(2u);
v___x_1471_ = l_Lean_Expr_getAppNumArgs(v___x_1467_);
v___x_1472_ = lean_nat_sub(v___x_1471_, v___x_1470_);
lean_dec(v___x_1471_);
v___x_1473_ = lean_unsigned_to_nat(1u);
v___x_1474_ = lean_nat_sub(v___x_1472_, v___x_1473_);
lean_dec(v___x_1472_);
v___x_1475_ = l_Lean_Expr_getRevArg_x21(v___x_1467_, v___x_1474_);
lean_dec_ref(v___x_1467_);
lean_inc(v_inv_1406_);
v___x_1476_ = l_Lean_mkMVar(v_inv_1406_);
v___x_1477_ = lean_expr_eqv(v___x_1475_, v___x_1476_);
lean_dec_ref(v___x_1476_);
lean_dec_ref(v___x_1475_);
if (v___x_1477_ == 0)
{
lean_dec_ref(v___x_1453_);
v___y_1437_ = v_prefixPoint_x3f_1455_;
v___y_1438_ = v_suffixPoint_x3f_1456_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_del_object(v___x_1434_);
lean_del_object(v___x_1429_);
v___x_1478_ = l_Lean_Expr_appArg_x21(v___x_1453_);
lean_dec_ref(v___x_1453_);
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
lean_ctor_set(v___x_1479_, 1, v___x_1446_);
v___x_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1445_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
v___x_1481_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v___x_1480_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v_snd_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1554_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref_known(v___x_1481_, 1);
v_snd_1483_ = lean_ctor_get(v_a_1482_, 1);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_a_1482_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; 
v_unused_1555_ = lean_ctor_get(v_a_1482_, 0);
lean_dec(v_unused_1555_);
v___x_1485_ = v_a_1482_;
v_isShared_1486_ = v_isSharedCheck_1554_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_snd_1483_);
lean_dec(v_a_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1554_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v_fst_1487_; lean_object* v_snd_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1553_; 
v_fst_1487_ = lean_ctor_get(v_snd_1483_, 0);
v_snd_1488_ = lean_ctor_get(v_snd_1483_, 1);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_snd_1483_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1490_ = v_snd_1483_;
v_isShared_1491_ = v_isSharedCheck_1553_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_snd_1488_);
lean_inc(v_fst_1487_);
lean_dec(v_snd_1483_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1553_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v_points_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v_points_1492_ = lean_ctor_get(v_snd_1432_, 0);
v___x_1493_ = lean_array_get_size(v_points_1492_);
v___x_1494_ = lean_array_get_size(v_snd_1488_);
v___x_1495_ = lean_nat_dec_lt(v___x_1493_, v___x_1494_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1497_; 
lean_dec(v_snd_1488_);
lean_dec(v_fst_1487_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v_snd_1432_);
lean_ctor_set(v___x_1490_, 0, v_suffixPoint_x3f_1456_);
v___x_1497_ = v___x_1490_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_suffixPoint_x3f_1456_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_snd_1432_);
v___x_1497_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1499_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 1, v___x_1497_);
lean_ctor_set(v___x_1485_, 0, v_prefixPoint_x3f_1455_);
v___x_1499_ = v___x_1485_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_prefixPoint_x3f_1455_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
v_a_1420_ = v___x_1499_;
goto v___jp_1419_;
}
}
}
else
{
lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1550_; 
v_isSharedCheck_1550_ = !lean_is_exclusive(v_snd_1432_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; lean_object* v_unused_1552_; 
v_unused_1551_ = lean_ctor_get(v_snd_1432_, 1);
lean_dec(v_unused_1551_);
v_unused_1552_ = lean_ctor_get(v_snd_1432_, 0);
lean_dec(v_unused_1552_);
v___x_1503_ = v_snd_1432_;
v_isShared_1504_ = v_isSharedCheck_1550_;
goto v_resetjp_1502_;
}
else
{
lean_dec(v_snd_1432_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1550_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1505_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4));
v___x_1506_ = l_Lean_Expr_isConstOf(v_fst_1487_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; uint8_t v___x_1508_; 
v___x_1507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6));
v___x_1508_ = l_Lean_Expr_isAppOfArity(v_fst_1487_, v___x_1507_, v___x_1473_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; uint8_t v___x_1510_; 
v___x_1509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8));
v___x_1510_ = l_Lean_Expr_isAppOfArity(v_fst_1487_, v___x_1509_, v___x_1473_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1511_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1511_, 0, v_fst_1487_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 1, v___x_1511_);
lean_ctor_set(v___x_1503_, 0, v_snd_1488_);
v___x_1513_ = v___x_1503_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_snd_1488_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1515_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v___x_1513_);
lean_ctor_set(v___x_1490_, 0, v_suffixPoint_x3f_1456_);
v___x_1515_ = v___x_1490_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_suffixPoint_x3f_1456_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1517_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 1, v___x_1515_);
lean_ctor_set(v___x_1485_, 0, v_prefixPoint_x3f_1455_);
v___x_1517_ = v___x_1485_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_prefixPoint_x3f_1455_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
v_a_1420_ = v___x_1517_;
goto v___jp_1419_;
}
}
}
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1523_; 
lean_dec(v_fst_1487_);
v___x_1521_ = lean_box(2);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 1, v___x_1521_);
lean_ctor_set(v___x_1503_, 0, v_snd_1488_);
v___x_1523_ = v___x_1503_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_snd_1488_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1525_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v___x_1523_);
lean_ctor_set(v___x_1490_, 0, v_suffixPoint_x3f_1456_);
v___x_1525_ = v___x_1490_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_suffixPoint_x3f_1456_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1527_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 1, v___x_1525_);
lean_ctor_set(v___x_1485_, 0, v_prefixPoint_x3f_1455_);
v___x_1527_ = v___x_1485_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_prefixPoint_x3f_1455_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
v_a_1420_ = v___x_1527_;
goto v___jp_1419_;
}
}
}
}
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1533_; 
lean_dec(v_fst_1487_);
v___x_1531_ = lean_box(1);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 1, v___x_1531_);
lean_ctor_set(v___x_1503_, 0, v_snd_1488_);
v___x_1533_ = v___x_1503_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_snd_1488_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1535_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v___x_1533_);
lean_ctor_set(v___x_1490_, 0, v_suffixPoint_x3f_1456_);
v___x_1535_ = v___x_1490_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_suffixPoint_x3f_1456_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1537_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 1, v___x_1535_);
lean_ctor_set(v___x_1485_, 0, v_prefixPoint_x3f_1455_);
v___x_1537_ = v___x_1485_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_prefixPoint_x3f_1455_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
v_a_1420_ = v___x_1537_;
goto v___jp_1419_;
}
}
}
}
}
else
{
lean_object* v___x_1542_; 
lean_dec(v_fst_1487_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 1, v___x_1447_);
lean_ctor_set(v___x_1503_, 0, v_snd_1488_);
v___x_1542_ = v___x_1503_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_snd_1488_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v___x_1447_);
v___x_1542_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1544_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v___x_1542_);
lean_ctor_set(v___x_1490_, 0, v_suffixPoint_x3f_1456_);
v___x_1544_ = v___x_1490_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_suffixPoint_x3f_1456_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1546_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 1, v___x_1544_);
lean_ctor_set(v___x_1485_, 0, v_prefixPoint_x3f_1455_);
v___x_1546_ = v___x_1485_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_prefixPoint_x3f_1455_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
v_a_1420_ = v___x_1546_;
goto v___jp_1419_;
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
lean_dec(v_suffixPoint_x3f_1456_);
lean_dec(v_prefixPoint_x3f_1455_);
lean_dec(v_snd_1432_);
lean_dec_ref(v_letMuts_1409_);
lean_dec_ref(v_xs_1408_);
lean_dec_ref(v___x_1407_);
lean_dec(v_inv_1406_);
v_a_1556_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1481_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1481_);
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
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_del_object(v___x_1434_);
lean_dec(v_snd_1432_);
lean_dec(v_fst_1431_);
lean_del_object(v___x_1429_);
lean_dec(v_fst_1427_);
lean_dec_ref(v_letMuts_1409_);
lean_dec_ref(v_xs_1408_);
lean_dec_ref(v___x_1407_);
lean_dec(v_inv_1406_);
v_a_1723_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1451_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1451_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_del_object(v___x_1434_);
lean_dec(v_snd_1432_);
lean_dec(v_fst_1431_);
lean_del_object(v___x_1429_);
lean_dec(v_fst_1427_);
lean_dec_ref(v_letMuts_1409_);
lean_dec_ref(v_xs_1408_);
lean_dec_ref(v___x_1407_);
lean_dec(v_inv_1406_);
v_a_1731_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1449_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1449_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
v___jp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___y_1438_);
v___x_1440_ = v___x_1434_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___y_1438_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_snd_1432_);
v___x_1440_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1442_; 
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 1, v___x_1440_);
lean_ctor_set(v___x_1429_, 0, v___y_1437_);
v___x_1442_ = v___x_1429_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___y_1437_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
v_a_1420_ = v___x_1442_;
goto v___jp_1419_;
}
}
}
}
}
}
v___jp_1419_:
{
size_t v___x_1421_; size_t v___x_1422_; 
v___x_1421_ = ((size_t)1ULL);
v___x_1422_ = lean_usize_add(v_i_1412_, v___x_1421_);
v_i_1412_ = v___x_1422_;
v_b_1413_ = v_a_1420_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___boxed(lean_object* v_inv_1741_, lean_object* v___x_1742_, lean_object* v_xs_1743_, lean_object* v_letMuts_1744_, lean_object* v_as_1745_, lean_object* v_sz_1746_, lean_object* v_i_1747_, lean_object* v_b_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
size_t v_sz_boxed_1754_; size_t v_i_boxed_1755_; lean_object* v_res_1756_; 
v_sz_boxed_1754_ = lean_unbox_usize(v_sz_1746_);
lean_dec(v_sz_1746_);
v_i_boxed_1755_ = lean_unbox_usize(v_i_1747_);
lean_dec(v_i_1747_);
v_res_1756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1741_, v___x_1742_, v_xs_1743_, v_letMuts_1744_, v_as_1745_, v_sz_boxed_1754_, v_i_boxed_1755_, v_b_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec_ref(v_as_1745_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(lean_object* v_vcs_1766_, lean_object* v_inv_1767_, lean_object* v_xs_1768_, lean_object* v_letMuts_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v_lctx_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; size_t v_sz_1778_; size_t v___x_1779_; lean_object* v___x_1780_; 
v_lctx_1775_ = lean_ctor_get(v_a_1770_, 2);
v___x_1776_ = lean_box(0);
v___x_1777_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__2));
v_sz_1778_ = lean_array_size(v_vcs_1766_);
v___x_1779_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1775_);
v___x_1780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1767_, v_lctx_1775_, v_xs_1768_, v_letMuts_1769_, v_vcs_1766_, v_sz_1778_, v___x_1779_, v___x_1777_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1824_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1783_ = v___x_1780_;
v_isShared_1784_ = v_isSharedCheck_1824_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1780_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1824_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v_snd_1789_; lean_object* v_fst_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1823_; 
v_snd_1789_ = lean_ctor_get(v_a_1781_, 1);
v_fst_1790_ = lean_ctor_get(v_a_1781_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_a_1781_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1792_ = v_a_1781_;
v_isShared_1793_ = v_isSharedCheck_1823_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_snd_1789_);
lean_inc(v_fst_1790_);
lean_dec(v_a_1781_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1823_;
goto v_resetjp_1791_;
}
v___jp_1785_:
{
lean_object* v___x_1787_; 
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v___x_1776_);
v___x_1787_ = v___x_1783_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1776_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
v_resetjp_1791_:
{
if (lean_obj_tag(v_fst_1790_) == 0)
{
lean_del_object(v___x_1792_);
lean_dec(v_snd_1789_);
goto v___jp_1785_;
}
else
{
lean_object* v_fst_1794_; 
v_fst_1794_ = lean_ctor_get(v_snd_1789_, 0);
lean_inc(v_fst_1794_);
if (lean_obj_tag(v_fst_1794_) == 0)
{
lean_dec_ref_known(v_fst_1790_, 1);
lean_del_object(v___x_1792_);
lean_dec(v_snd_1789_);
goto v___jp_1785_;
}
else
{
lean_object* v_snd_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1821_; 
lean_del_object(v___x_1783_);
v_snd_1795_ = lean_ctor_get(v_snd_1789_, 1);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_snd_1789_);
if (v_isSharedCheck_1821_ == 0)
{
lean_object* v_unused_1822_; 
v_unused_1822_ = lean_ctor_get(v_snd_1789_, 0);
lean_dec(v_unused_1822_);
v___x_1797_ = v_snd_1789_;
v_isShared_1798_ = v_isSharedCheck_1821_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_snd_1795_);
lean_dec(v_snd_1789_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1821_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v_val_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1820_; 
v_val_1799_ = lean_ctor_get(v_fst_1790_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_fst_1790_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1801_ = v_fst_1790_;
v_isShared_1802_ = v_isSharedCheck_1820_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_val_1799_);
lean_dec(v_fst_1790_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1820_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v_val_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1819_; 
v_val_1803_ = lean_ctor_get(v_fst_1794_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_fst_1794_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1805_ = v_fst_1794_;
v_isShared_1806_ = v_isSharedCheck_1819_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_val_1803_);
lean_dec(v_fst_1794_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1819_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v_val_1803_);
v___x_1808_ = v___x_1797_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_val_1803_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_snd_1795_);
v___x_1808_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1810_; 
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 1, v___x_1808_);
lean_ctor_set(v___x_1792_, 0, v_val_1799_);
v___x_1810_ = v___x_1792_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_val_1799_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1812_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1810_);
v___x_1812_ = v___x_1805_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1814_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set_tag(v___x_1801_, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1812_);
v___x_1814_ = v___x_1801_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
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
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
v_a_1825_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1780_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1780_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___boxed(lean_object* v_vcs_1833_, lean_object* v_inv_1834_, lean_object* v_xs_1835_, lean_object* v_letMuts_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_vcs_1833_, v_inv_1834_, v_xs_1835_, v_letMuts_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec_ref(v_vcs_1833_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(lean_object* v_inst_1843_, lean_object* v_a_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_a_1844_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___boxed(lean_object* v_inst_1851_, lean_object* v_a_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(v_inst_1851_, v_a_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(lean_object* v_m_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_MVarId_getDecl(v_m_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v_userName_1867_; lean_object* v_lctx_1868_; lean_object* v_type_1869_; lean_object* v_localInstances_1870_; uint8_t v_kind_1871_; lean_object* v_numScopeArgs_1872_; lean_object* v___x_1873_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v___x_1865_, 1);
v_userName_1867_ = lean_ctor_get(v_a_1866_, 0);
lean_inc(v_userName_1867_);
v_lctx_1868_ = lean_ctor_get(v_a_1866_, 1);
lean_inc_ref(v_lctx_1868_);
v_type_1869_ = lean_ctor_get(v_a_1866_, 2);
lean_inc_ref(v_type_1869_);
v_localInstances_1870_ = lean_ctor_get(v_a_1866_, 4);
lean_inc_ref(v_localInstances_1870_);
v_kind_1871_ = lean_ctor_get_uint8(v_a_1866_, sizeof(void*)*7);
v_numScopeArgs_1872_ = lean_ctor_get(v_a_1866_, 5);
lean_inc(v_numScopeArgs_1872_);
lean_dec(v_a_1866_);
v___x_1873_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_1868_, v_localInstances_1870_, v_type_1869_, v_kind_1871_, v_userName_1867_, v_numScopeArgs_1872_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1882_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = l_Lean_Expr_mvarId_x21(v_a_1874_);
lean_dec(v_a_1874_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1878_);
v___x_1880_ = v___x_1876_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
v_a_1883_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1873_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1873_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
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
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
v_a_1891_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1865_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1865_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar___boxed(lean_object* v_m_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v_m_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__1(lean_object* v_msg_1906_){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = l_String_instInhabitedSlice;
v___x_1908_ = lean_panic_fn_borrowed(v___x_1907_, v_msg_1906_);
return v___x_1908_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(lean_object* v_s_1909_, lean_object* v_a_1910_, uint8_t v_b_1911_){
_start:
{
lean_object* v_str_1912_; lean_object* v_startInclusive_1913_; lean_object* v_endExclusive_1914_; lean_object* v___x_1915_; uint8_t v_decide_1916_; 
v_str_1912_ = lean_ctor_get(v_s_1909_, 0);
v_startInclusive_1913_ = lean_ctor_get(v_s_1909_, 1);
v_endExclusive_1914_ = lean_ctor_get(v_s_1909_, 2);
v___x_1915_ = lean_nat_sub(v_endExclusive_1914_, v_startInclusive_1913_);
v_decide_1916_ = lean_nat_dec_eq(v_a_1910_, v___x_1915_);
lean_dec(v___x_1915_);
if (v_decide_1916_ == 0)
{
uint32_t v___x_1917_; lean_object* v___x_1918_; uint32_t v___x_1919_; uint8_t v___x_1920_; 
v___x_1917_ = 64;
v___x_1918_ = lean_nat_add(v_startInclusive_1913_, v_a_1910_);
lean_dec(v_a_1910_);
v___x_1919_ = lean_string_utf8_get_fast(v_str_1912_, v___x_1918_);
v___x_1920_ = lean_uint32_dec_eq(v___x_1919_, v___x_1917_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = lean_string_utf8_next_fast(v_str_1912_, v___x_1918_);
lean_dec(v___x_1918_);
v___x_1922_ = lean_nat_sub(v___x_1921_, v_startInclusive_1913_);
v_a_1910_ = v___x_1922_;
v_b_1911_ = v___x_1920_;
goto _start;
}
else
{
lean_dec(v___x_1918_);
return v___x_1920_;
}
}
else
{
lean_dec(v_a_1910_);
return v_b_1911_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg___boxed(lean_object* v_s_1924_, lean_object* v_a_1925_, lean_object* v_b_1926_){
_start:
{
uint8_t v_b_boxed_1927_; uint8_t v_res_1928_; lean_object* v_r_1929_; 
v_b_boxed_1927_ = lean_unbox(v_b_1926_);
v_res_1928_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_1924_, v_a_1925_, v_b_boxed_1927_);
lean_dec_ref(v_s_1924_);
v_r_1929_ = lean_box(v_res_1928_);
return v_r_1929_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(lean_object* v_s_1930_){
_start:
{
lean_object* v_searcher_1931_; uint8_t v___x_1932_; uint8_t v___x_1933_; 
v_searcher_1931_ = lean_unsigned_to_nat(0u);
v___x_1932_ = 0;
v___x_1933_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_1930_, v_searcher_1931_, v___x_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2___boxed(lean_object* v_s_1934_){
_start:
{
uint8_t v_res_1935_; lean_object* v_r_1936_; 
v_res_1935_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v_s_1934_);
lean_dec_ref(v_s_1934_);
v_r_1936_ = lean_box(v_res_1935_);
return v_r_1936_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3(void){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1940_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__2));
v___x_1941_ = lean_unsigned_to_nat(14u);
v___x_1942_ = lean_unsigned_to_nat(22u);
v___x_1943_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__1));
v___x_1944_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__0));
v___x_1945_ = l_mkPanicMessageWithDecl(v___x_1944_, v___x_1943_, v___x_1942_, v___x_1941_, v___x_1940_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(lean_object* v_x_1946_){
_start:
{
switch(lean_obj_tag(v_x_1946_))
{
case 1:
{
lean_object* v_info_1947_; lean_object* v_kind_1948_; lean_object* v_args_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1959_; 
v_info_1947_ = lean_ctor_get(v_x_1946_, 0);
v_kind_1948_ = lean_ctor_get(v_x_1946_, 1);
v_args_1949_ = lean_ctor_get(v_x_1946_, 2);
v_isSharedCheck_1959_ = !lean_is_exclusive(v_x_1946_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1951_ = v_x_1946_;
v_isShared_1952_ = v_isSharedCheck_1959_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_args_1949_);
lean_inc(v_kind_1948_);
lean_inc(v_info_1947_);
lean_dec(v_x_1946_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1959_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
size_t v_sz_1953_; size_t v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
v_sz_1953_ = lean_array_size(v_args_1949_);
v___x_1954_ = ((size_t)0ULL);
v___x_1955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(v_sz_1953_, v___x_1954_, v_args_1949_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 2, v___x_1955_);
v___x_1957_ = v___x_1951_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_info_1947_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_kind_1948_);
lean_ctor_set(v_reuseFailAlloc_1958_, 2, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
case 3:
{
lean_object* v_info_1960_; lean_object* v_rawVal_1961_; lean_object* v_val_1962_; lean_object* v_preresolved_1963_; uint8_t v___y_1965_; lean_object* v_str_1982_; lean_object* v_startPos_1983_; lean_object* v_stopPos_1984_; uint8_t v___x_1985_; 
v_info_1960_ = lean_ctor_get(v_x_1946_, 0);
v_rawVal_1961_ = lean_ctor_get(v_x_1946_, 1);
v_val_1962_ = lean_ctor_get(v_x_1946_, 2);
v_preresolved_1963_ = lean_ctor_get(v_x_1946_, 3);
v_str_1982_ = lean_ctor_get(v_rawVal_1961_, 0);
v_startPos_1983_ = lean_ctor_get(v_rawVal_1961_, 1);
v_stopPos_1984_ = lean_ctor_get(v_rawVal_1961_, 2);
v___x_1985_ = lean_string_is_valid_pos(v_str_1982_, v_startPos_1983_);
if (v___x_1985_ == 0)
{
goto v___jp_1978_;
}
else
{
uint8_t v___x_1986_; 
v___x_1986_ = lean_string_is_valid_pos(v_str_1982_, v_stopPos_1984_);
if (v___x_1986_ == 0)
{
goto v___jp_1978_;
}
else
{
uint8_t v___x_1987_; 
v___x_1987_ = lean_nat_dec_le(v_startPos_1983_, v_stopPos_1984_);
if (v___x_1987_ == 0)
{
goto v___jp_1978_;
}
else
{
lean_object* v___x_1988_; uint8_t v___x_1989_; 
lean_inc(v_stopPos_1984_);
lean_inc(v_startPos_1983_);
lean_inc_ref(v_str_1982_);
v___x_1988_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1988_, 0, v_str_1982_);
lean_ctor_set(v___x_1988_, 1, v_startPos_1983_);
lean_ctor_set(v___x_1988_, 2, v_stopPos_1984_);
v___x_1989_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v___x_1988_);
lean_dec_ref_known(v___x_1988_, 3);
v___y_1965_ = v___x_1989_;
goto v___jp_1964_;
}
}
}
v___jp_1964_:
{
if (v___y_1965_ == 0)
{
lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1973_; 
lean_inc(v_preresolved_1963_);
lean_inc(v_val_1962_);
lean_inc_ref(v_rawVal_1961_);
lean_inc(v_info_1960_);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_x_1946_);
if (v_isSharedCheck_1973_ == 0)
{
lean_object* v_unused_1974_; lean_object* v_unused_1975_; lean_object* v_unused_1976_; lean_object* v_unused_1977_; 
v_unused_1974_ = lean_ctor_get(v_x_1946_, 3);
lean_dec(v_unused_1974_);
v_unused_1975_ = lean_ctor_get(v_x_1946_, 2);
lean_dec(v_unused_1975_);
v_unused_1976_ = lean_ctor_get(v_x_1946_, 1);
lean_dec(v_unused_1976_);
v_unused_1977_ = lean_ctor_get(v_x_1946_, 0);
lean_dec(v_unused_1977_);
v___x_1967_ = v_x_1946_;
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
else
{
lean_dec(v_x_1946_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1969_ = l_Lean_Name_eraseMacroScopes(v_val_1962_);
lean_dec(v_val_1962_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 2, v___x_1969_);
v___x_1971_ = v___x_1967_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_info_1960_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_rawVal_1961_);
lean_ctor_set(v_reuseFailAlloc_1972_, 2, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1972_, 3, v_preresolved_1963_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
else
{
return v_x_1946_;
}
}
v___jp_1978_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; 
v___x_1979_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3);
v___x_1980_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__1(v___x_1979_);
v___x_1981_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v___x_1980_);
lean_dec_ref(v___x_1980_);
v___y_1965_ = v___x_1981_;
goto v___jp_1964_;
}
}
default: 
{
return v_x_1946_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(size_t v_sz_1990_, size_t v_i_1991_, lean_object* v_bs_1992_){
_start:
{
uint8_t v___x_1993_; 
v___x_1993_ = lean_usize_dec_lt(v_i_1991_, v_sz_1990_);
if (v___x_1993_ == 0)
{
return v_bs_1992_;
}
else
{
lean_object* v_v_1994_; lean_object* v___x_1995_; lean_object* v_bs_x27_1996_; lean_object* v___x_1997_; size_t v___x_1998_; size_t v___x_1999_; lean_object* v___x_2000_; 
v_v_1994_ = lean_array_uget(v_bs_1992_, v_i_1991_);
v___x_1995_ = lean_unsigned_to_nat(0u);
v_bs_x27_1996_ = lean_array_uset(v_bs_1992_, v_i_1991_, v___x_1995_);
v___x_1997_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_v_1994_);
v___x_1998_ = ((size_t)1ULL);
v___x_1999_ = lean_usize_add(v_i_1991_, v___x_1998_);
v___x_2000_ = lean_array_uset(v_bs_x27_1996_, v_i_1991_, v___x_1997_);
v_i_1991_ = v___x_1999_;
v_bs_1992_ = v___x_2000_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0___boxed(lean_object* v_sz_2002_, lean_object* v_i_2003_, lean_object* v_bs_2004_){
_start:
{
size_t v_sz_boxed_2005_; size_t v_i_boxed_2006_; lean_object* v_res_2007_; 
v_sz_boxed_2005_ = lean_unbox_usize(v_sz_2002_);
lean_dec(v_sz_2002_);
v_i_boxed_2006_ = lean_unbox_usize(v_i_2003_);
lean_dec(v_i_2003_);
v_res_2007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(v_sz_boxed_2005_, v_i_boxed_2006_, v_bs_2004_);
return v_res_2007_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2(lean_object* v_s_2008_, lean_object* v_inst_2009_, lean_object* v_R_2010_, lean_object* v_a_2011_, uint8_t v_b_2012_, lean_object* v_c_2013_){
_start:
{
uint8_t v___x_2014_; 
v___x_2014_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_2008_, v_a_2011_, v_b_2012_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___boxed(lean_object* v_s_2015_, lean_object* v_inst_2016_, lean_object* v_R_2017_, lean_object* v_a_2018_, lean_object* v_b_2019_, lean_object* v_c_2020_){
_start:
{
uint8_t v_b_boxed_2021_; uint8_t v_res_2022_; lean_object* v_r_2023_; 
v_b_boxed_2021_ = lean_unbox(v_b_2019_);
v_res_2022_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2(v_s_2015_, v_inst_2016_, v_R_2017_, v_a_2018_, v_b_boxed_2021_, v_c_2020_);
lean_dec_ref(v_s_2015_);
v_r_2023_ = lean_box(v_res_2022_);
return v_r_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter___redArg(lean_object* v_x_2024_, lean_object* v_h__1_2025_, lean_object* v_h__2_2026_, lean_object* v_h__3_2027_, lean_object* v_h__4_2028_){
_start:
{
switch(lean_obj_tag(v_x_2024_))
{
case 0:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
lean_dec(v_h__3_2027_);
lean_dec(v_h__2_2026_);
lean_dec(v_h__1_2025_);
v___x_2029_ = lean_box(0);
v___x_2030_ = lean_apply_1(v_h__4_2028_, v___x_2029_);
return v___x_2030_;
}
case 1:
{
lean_object* v_info_2031_; lean_object* v_kind_2032_; lean_object* v_args_2033_; lean_object* v___x_2034_; 
lean_dec(v_h__4_2028_);
lean_dec(v_h__3_2027_);
lean_dec(v_h__1_2025_);
v_info_2031_ = lean_ctor_get(v_x_2024_, 0);
lean_inc(v_info_2031_);
v_kind_2032_ = lean_ctor_get(v_x_2024_, 1);
lean_inc(v_kind_2032_);
v_args_2033_ = lean_ctor_get(v_x_2024_, 2);
lean_inc_ref(v_args_2033_);
lean_dec_ref_known(v_x_2024_, 3);
v___x_2034_ = lean_apply_3(v_h__2_2026_, v_info_2031_, v_kind_2032_, v_args_2033_);
return v___x_2034_;
}
case 2:
{
lean_object* v_info_2035_; lean_object* v_val_2036_; lean_object* v___x_2037_; 
lean_dec(v_h__4_2028_);
lean_dec(v_h__2_2026_);
lean_dec(v_h__1_2025_);
v_info_2035_ = lean_ctor_get(v_x_2024_, 0);
lean_inc(v_info_2035_);
v_val_2036_ = lean_ctor_get(v_x_2024_, 1);
lean_inc_ref(v_val_2036_);
lean_dec_ref_known(v_x_2024_, 2);
v___x_2037_ = lean_apply_2(v_h__3_2027_, v_info_2035_, v_val_2036_);
return v___x_2037_;
}
default: 
{
lean_object* v_info_2038_; lean_object* v_rawVal_2039_; lean_object* v_val_2040_; lean_object* v_preresolved_2041_; lean_object* v___x_2042_; 
lean_dec(v_h__4_2028_);
lean_dec(v_h__3_2027_);
lean_dec(v_h__2_2026_);
v_info_2038_ = lean_ctor_get(v_x_2024_, 0);
lean_inc(v_info_2038_);
v_rawVal_2039_ = lean_ctor_get(v_x_2024_, 1);
lean_inc_ref(v_rawVal_2039_);
v_val_2040_ = lean_ctor_get(v_x_2024_, 2);
lean_inc(v_val_2040_);
v_preresolved_2041_ = lean_ctor_get(v_x_2024_, 3);
lean_inc(v_preresolved_2041_);
lean_dec_ref_known(v_x_2024_, 4);
v___x_2042_ = lean_apply_4(v_h__1_2025_, v_info_2038_, v_rawVal_2039_, v_val_2040_, v_preresolved_2041_);
return v___x_2042_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter(lean_object* v_motive_2043_, lean_object* v_x_2044_, lean_object* v_h__1_2045_, lean_object* v_h__2_2046_, lean_object* v_h__3_2047_, lean_object* v_h__4_2048_){
_start:
{
switch(lean_obj_tag(v_x_2044_))
{
case 0:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
lean_dec(v_h__3_2047_);
lean_dec(v_h__2_2046_);
lean_dec(v_h__1_2045_);
v___x_2049_ = lean_box(0);
v___x_2050_ = lean_apply_1(v_h__4_2048_, v___x_2049_);
return v___x_2050_;
}
case 1:
{
lean_object* v_info_2051_; lean_object* v_kind_2052_; lean_object* v_args_2053_; lean_object* v___x_2054_; 
lean_dec(v_h__4_2048_);
lean_dec(v_h__3_2047_);
lean_dec(v_h__1_2045_);
v_info_2051_ = lean_ctor_get(v_x_2044_, 0);
lean_inc(v_info_2051_);
v_kind_2052_ = lean_ctor_get(v_x_2044_, 1);
lean_inc(v_kind_2052_);
v_args_2053_ = lean_ctor_get(v_x_2044_, 2);
lean_inc_ref(v_args_2053_);
lean_dec_ref_known(v_x_2044_, 3);
v___x_2054_ = lean_apply_3(v_h__2_2046_, v_info_2051_, v_kind_2052_, v_args_2053_);
return v___x_2054_;
}
case 2:
{
lean_object* v_info_2055_; lean_object* v_val_2056_; lean_object* v___x_2057_; 
lean_dec(v_h__4_2048_);
lean_dec(v_h__2_2046_);
lean_dec(v_h__1_2045_);
v_info_2055_ = lean_ctor_get(v_x_2044_, 0);
lean_inc(v_info_2055_);
v_val_2056_ = lean_ctor_get(v_x_2044_, 1);
lean_inc_ref(v_val_2056_);
lean_dec_ref_known(v_x_2044_, 2);
v___x_2057_ = lean_apply_2(v_h__3_2047_, v_info_2055_, v_val_2056_);
return v___x_2057_;
}
default: 
{
lean_object* v_info_2058_; lean_object* v_rawVal_2059_; lean_object* v_val_2060_; lean_object* v_preresolved_2061_; lean_object* v___x_2062_; 
lean_dec(v_h__4_2048_);
lean_dec(v_h__3_2047_);
lean_dec(v_h__2_2046_);
v_info_2058_ = lean_ctor_get(v_x_2044_, 0);
lean_inc(v_info_2058_);
v_rawVal_2059_ = lean_ctor_get(v_x_2044_, 1);
lean_inc_ref(v_rawVal_2059_);
v_val_2060_ = lean_ctor_get(v_x_2044_, 2);
lean_inc(v_val_2060_);
v_preresolved_2061_ = lean_ctor_get(v_x_2044_, 3);
lean_inc(v_preresolved_2061_);
lean_dec_ref_known(v_x_2044_, 4);
v___x_2062_ = lean_apply_4(v_h__1_2045_, v_info_2058_, v_rawVal_2059_, v_val_2060_, v_preresolved_2061_);
return v___x_2062_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_2063_, lean_object* v_h__1_2064_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = lean_apply_2(v_h__1_2064_, v_x_2063_, lean_box(0));
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_2066_, lean_object* v_P_2067_, lean_object* v_motive_2068_, lean_object* v_x_2069_, lean_object* v_h__1_2070_){
_start:
{
lean_object* v___x_2071_; 
v___x_2071_ = lean_apply_2(v_h__1_2070_, v_x_2069_, lean_box(0));
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___redArg(lean_object* v_syn_2072_){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_syn_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(lean_object* v_name_2074_, lean_object* v_syn_2075_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_syn_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___boxed(lean_object* v_name_2077_, lean_object* v_syn_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(v_name_2077_, v_syn_2078_);
lean_dec(v_name_2077_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(lean_object* v_e_2086_){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; 
v___x_2113_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__1));
v___x_2114_ = lean_unsigned_to_nat(2u);
v___x_2115_ = l_Lean_Expr_isAppOfArity(v_e_2086_, v___x_2113_, v___x_2114_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2116_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
v___x_2117_ = lean_unsigned_to_nat(3u);
v___x_2118_ = l_Lean_Expr_isAppOfArity(v_e_2086_, v___x_2116_, v___x_2117_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2119_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
v___x_2120_ = l_Lean_Expr_isAppOfArity(v_e_2086_, v___x_2119_, v___x_2117_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2121_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_2122_ = l_Lean_Expr_isAppOfArity(v_e_2086_, v___x_2121_, v___x_2117_);
if (v___x_2122_ == 0)
{
goto v___jp_2087_;
}
else
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_Expr_appArg_x21(v_e_2086_);
if (lean_obj_tag(v___x_2123_) == 6)
{
lean_object* v_binderName_2124_; lean_object* v_binderType_2125_; lean_object* v_body_2126_; uint8_t v_binderInfo_2127_; lean_object* v___x_2128_; 
lean_dec_ref(v_e_2086_);
v_binderName_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_binderName_2124_);
v_binderType_2125_ = lean_ctor_get(v___x_2123_, 1);
lean_inc_ref(v_binderType_2125_);
v_body_2126_ = lean_ctor_get(v___x_2123_, 2);
lean_inc_ref(v_body_2126_);
v_binderInfo_2127_ = lean_ctor_get_uint8(v___x_2123_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_2123_, 3);
v___x_2128_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_2126_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_dec_ref(v_binderType_2125_);
lean_dec(v_binderName_2124_);
return v___x_2128_;
}
else
{
lean_object* v_val_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2146_; 
v_val_2129_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2131_ = v___x_2128_;
v_isShared_2132_ = v_isSharedCheck_2146_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_val_2129_);
lean_dec(v___x_2128_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2146_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v_fst_2133_; lean_object* v_snd_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2145_; 
v_fst_2133_ = lean_ctor_get(v_val_2129_, 0);
v_snd_2134_ = lean_ctor_get(v_val_2129_, 1);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_val_2129_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2136_ = v_val_2129_;
v_isShared_2137_ = v_isSharedCheck_2145_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_snd_2134_);
lean_inc(v_fst_2133_);
lean_dec(v_val_2129_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2145_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2138_ = l_Lean_mkForall(v_binderName_2124_, v_binderInfo_2127_, v_binderType_2125_, v_snd_2134_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 1, v___x_2138_);
v___x_2140_ = v___x_2136_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_fst_2133_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2142_; 
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v___x_2140_);
v___x_2142_ = v___x_2131_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2123_);
goto v___jp_2087_;
}
}
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2147_ = l_Lean_Expr_appFn_x21(v_e_2086_);
v___x_2148_ = l_Lean_Expr_appArg_x21(v___x_2147_);
lean_dec_ref(v___x_2147_);
v___x_2149_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2148_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_dec_ref(v_e_2086_);
return v___x_2149_;
}
else
{
lean_object* v_val_2150_; lean_object* v_snd_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v_val_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_val_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v_snd_2151_ = lean_ctor_get(v_val_2150_, 1);
lean_inc(v_snd_2151_);
lean_dec(v_val_2150_);
v___x_2152_ = l_Lean_Expr_appArg_x21(v_e_2086_);
lean_dec_ref(v_e_2086_);
v___x_2153_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2152_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_dec(v_snd_2151_);
return v___x_2153_;
}
else
{
lean_object* v_val_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2171_; 
v_val_2154_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2156_ = v___x_2153_;
v_isShared_2157_ = v_isSharedCheck_2171_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_val_2154_);
lean_dec(v___x_2153_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2171_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v_fst_2158_; lean_object* v_snd_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2170_; 
v_fst_2158_ = lean_ctor_get(v_val_2154_, 0);
v_snd_2159_ = lean_ctor_get(v_val_2154_, 1);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_val_2154_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2161_ = v_val_2154_;
v_isShared_2162_ = v_isSharedCheck_2170_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_snd_2159_);
lean_inc(v_fst_2158_);
lean_dec(v_val_2154_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2170_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2163_; lean_object* v___x_2165_; 
v___x_2163_ = l_Lean_mkOr(v_snd_2151_, v_snd_2159_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 1, v___x_2163_);
v___x_2165_ = v___x_2161_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_fst_2158_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
lean_object* v___x_2167_; 
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2165_);
v___x_2167_ = v___x_2156_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
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
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = l_Lean_Expr_appFn_x21(v_e_2086_);
v___x_2173_ = l_Lean_Expr_appArg_x21(v___x_2172_);
lean_dec_ref(v___x_2172_);
v___x_2174_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2173_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_dec_ref(v_e_2086_);
return v___x_2174_;
}
else
{
lean_object* v_val_2175_; lean_object* v_snd_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v_val_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_val_2175_);
lean_dec_ref_known(v___x_2174_, 1);
v_snd_2176_ = lean_ctor_get(v_val_2175_, 1);
lean_inc(v_snd_2176_);
lean_dec(v_val_2175_);
v___x_2177_ = l_Lean_Expr_appArg_x21(v_e_2086_);
lean_dec_ref(v_e_2086_);
v___x_2178_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2177_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_dec(v_snd_2176_);
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
v___x_2188_ = l_Lean_mkAnd(v_snd_2176_, v_snd_2184_);
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
}
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2197_ = lean_box(0);
v___x_2198_ = l_Lean_Expr_getAppFn(v_e_2086_);
v___x_2199_ = l_Lean_Expr_constLevels_x21(v___x_2198_);
lean_dec_ref(v___x_2198_);
v___x_2200_ = lean_unsigned_to_nat(0u);
v___x_2201_ = l_List_get_x21Internal___redArg(v___x_2197_, v___x_2199_, v___x_2200_);
lean_dec(v___x_2199_);
v___x_2202_ = lean_unsigned_to_nat(1u);
v___x_2203_ = l_Lean_Expr_getAppNumArgs(v_e_2086_);
v___x_2204_ = lean_nat_sub(v___x_2203_, v___x_2202_);
lean_dec(v___x_2203_);
v___x_2205_ = lean_nat_sub(v___x_2204_, v___x_2202_);
lean_dec(v___x_2204_);
v___x_2206_ = l_Lean_Expr_getRevArg_x21(v_e_2086_, v___x_2205_);
lean_dec_ref(v_e_2086_);
v___x_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2201_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
v___x_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
return v___x_2208_;
}
v___jp_2087_:
{
if (lean_obj_tag(v_e_2086_) == 8)
{
lean_object* v_declName_2088_; lean_object* v_type_2089_; lean_object* v_value_2090_; lean_object* v_body_2091_; uint8_t v_nondep_2092_; lean_object* v___x_2093_; 
v_declName_2088_ = lean_ctor_get(v_e_2086_, 0);
lean_inc(v_declName_2088_);
v_type_2089_ = lean_ctor_get(v_e_2086_, 1);
lean_inc_ref(v_type_2089_);
v_value_2090_ = lean_ctor_get(v_e_2086_, 2);
lean_inc_ref(v_value_2090_);
v_body_2091_ = lean_ctor_get(v_e_2086_, 3);
lean_inc_ref(v_body_2091_);
v_nondep_2092_ = lean_ctor_get_uint8(v_e_2086_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2086_, 4);
v___x_2093_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_2091_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_dec_ref(v_value_2090_);
lean_dec_ref(v_type_2089_);
lean_dec(v_declName_2088_);
return v___x_2093_;
}
else
{
lean_object* v_val_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2111_; 
v_val_2094_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2096_ = v___x_2093_;
v_isShared_2097_ = v_isSharedCheck_2111_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_val_2094_);
lean_dec(v___x_2093_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2111_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v_fst_2098_; lean_object* v_snd_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2110_; 
v_fst_2098_ = lean_ctor_get(v_val_2094_, 0);
v_snd_2099_ = lean_ctor_get(v_val_2094_, 1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_val_2094_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2101_ = v_val_2094_;
v_isShared_2102_ = v_isSharedCheck_2110_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_snd_2099_);
lean_inc(v_fst_2098_);
lean_dec(v_val_2094_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2110_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; lean_object* v___x_2105_; 
v___x_2103_ = l_Lean_Expr_letE___override(v_declName_2088_, v_type_2089_, v_value_2090_, v_snd_2099_, v_nondep_2092_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 1, v___x_2103_);
v___x_2105_ = v___x_2101_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_fst_2098_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
lean_object* v___x_2107_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v___x_2105_);
v___x_2107_ = v___x_2096_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
}
else
{
lean_object* v___x_2112_; 
lean_dec_ref(v_e_2086_);
v___x_2112_ = lean_box(0);
return v___x_2112_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(lean_object* v_e_2209_){
_start:
{
lean_object* v___x_2210_; 
lean_inc_ref(v_e_2209_);
v___x_2210_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_e_2209_);
if (lean_obj_tag(v___x_2210_) == 0)
{
return v_e_2209_;
}
else
{
lean_object* v_val_2211_; lean_object* v_fst_2212_; lean_object* v_snd_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
lean_dec_ref(v_e_2209_);
v_val_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_val_2211_);
lean_dec_ref_known(v___x_2210_, 1);
v_fst_2212_ = lean_ctor_get(v_val_2211_, 0);
lean_inc_n(v_fst_2212_, 2);
v_snd_2213_ = lean_ctor_get(v_val_2211_, 1);
lean_inc(v_snd_2213_);
lean_dec(v_val_2211_);
v___x_2214_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_2212_);
v___x_2215_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_2212_, v___x_2214_, v_snd_2213_);
return v___x_2215_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6(void){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Array_mkArray0___redArg();
return v___x_2226_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__23));
v___x_2265_ = l_String_toRawSubstring_x27(v___x_2264_);
return v___x_2265_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__28));
v___x_2277_ = l_String_toRawSubstring_x27(v___x_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(lean_object* v_handlers_2287_, lean_object* v_default_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v___x_2294_; lean_object* v_handlers_2295_; 
v___x_2294_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v_handlers_2295_ = l_Lean_Syntax_SepArray_ofElems(v___x_2294_, v_handlers_2287_);
switch(lean_obj_tag(v_default_2288_))
{
case 0:
{
lean_object* v_ref_2296_; uint8_t v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v_ref_2296_ = lean_ctor_get(v_a_2291_, 2);
v___x_2297_ = 0;
v___x_2298_ = l_Lean_SourceInfo_fromRef(v_ref_2296_, v___x_2297_);
v___x_2299_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__2));
v___x_2300_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__3));
lean_inc_n(v___x_2298_, 3);
v___x_2301_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2298_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2303_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2304_ = l_Array_append___redArg(v___x_2303_, v_handlers_2295_);
lean_dec_ref(v_handlers_2295_);
v___x_2305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2298_);
lean_ctor_set(v___x_2305_, 1, v___x_2302_);
lean_ctor_set(v___x_2305_, 2, v___x_2304_);
v___x_2306_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2298_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = l_Lean_Syntax_node3(v___x_2298_, v___x_2299_, v___x_2301_, v___x_2305_, v___x_2307_);
v___x_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
return v___x_2309_;
}
case 1:
{
lean_object* v_toCold_2310_; lean_object* v_ref_2311_; lean_object* v_quotContext_2312_; lean_object* v_currMacroScope_2313_; uint8_t v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v_toCold_2310_ = lean_ctor_get(v_a_2291_, 0);
v_ref_2311_ = lean_ctor_get(v_a_2291_, 2);
v_quotContext_2312_ = lean_ctor_get(v_toCold_2310_, 8);
v_currMacroScope_2313_ = lean_ctor_get(v_toCold_2310_, 9);
v___x_2314_ = 0;
v___x_2315_ = l_Lean_SourceInfo_fromRef(v_ref_2311_, v___x_2314_);
v___x_2316_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2317_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2315_, 12);
v___x_2318_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2315_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v___x_2319_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2320_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2321_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2322_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2323_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2324_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2315_);
lean_ctor_set(v___x_2324_, 1, v___x_2322_);
v___x_2325_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2326_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2315_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
v___x_2328_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2329_ = l_Array_append___redArg(v___x_2328_, v_handlers_2295_);
lean_dec_ref(v_handlers_2295_);
v___x_2330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2315_);
lean_ctor_set(v___x_2330_, 1, v___x_2294_);
v___x_2331_ = lean_array_push(v___x_2329_, v___x_2330_);
v___x_2332_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24);
v___x_2333_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25));
lean_inc(v_currMacroScope_2313_);
lean_inc(v_quotContext_2312_);
v___x_2334_ = l_Lean_addMacroScope(v_quotContext_2312_, v___x_2333_, v_currMacroScope_2313_);
v___x_2335_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__27));
v___x_2336_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2315_);
lean_ctor_set(v___x_2336_, 1, v___x_2332_);
lean_ctor_set(v___x_2336_, 2, v___x_2334_);
lean_ctor_set(v___x_2336_, 3, v___x_2335_);
v___x_2337_ = lean_array_push(v___x_2331_, v___x_2336_);
v___x_2338_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2315_);
lean_ctor_set(v___x_2338_, 1, v___x_2321_);
lean_ctor_set(v___x_2338_, 2, v___x_2337_);
v___x_2339_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2340_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2315_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
v___x_2341_ = l_Lean_Syntax_node3(v___x_2315_, v___x_2325_, v___x_2327_, v___x_2338_, v___x_2340_);
v___x_2342_ = l_Lean_Syntax_node2(v___x_2315_, v___x_2323_, v___x_2324_, v___x_2341_);
v___x_2343_ = l_Lean_Syntax_node1(v___x_2315_, v___x_2321_, v___x_2342_);
v___x_2344_ = l_Lean_Syntax_node1(v___x_2315_, v___x_2320_, v___x_2343_);
v___x_2345_ = l_Lean_Syntax_node1(v___x_2315_, v___x_2319_, v___x_2344_);
v___x_2346_ = l_Lean_Syntax_node2(v___x_2315_, v___x_2316_, v___x_2318_, v___x_2345_);
v___x_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
return v___x_2347_;
}
case 2:
{
lean_object* v_toCold_2348_; lean_object* v_ref_2349_; lean_object* v_quotContext_2350_; lean_object* v_currMacroScope_2351_; uint8_t v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v_toCold_2348_ = lean_ctor_get(v_a_2291_, 0);
v_ref_2349_ = lean_ctor_get(v_a_2291_, 2);
v_quotContext_2350_ = lean_ctor_get(v_toCold_2348_, 8);
v_currMacroScope_2351_ = lean_ctor_get(v_toCold_2348_, 9);
v___x_2352_ = 0;
v___x_2353_ = l_Lean_SourceInfo_fromRef(v_ref_2349_, v___x_2352_);
v___x_2354_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2355_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2353_, 12);
v___x_2356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2353_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
v___x_2357_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2358_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2359_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2360_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2361_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2353_);
lean_ctor_set(v___x_2362_, 1, v___x_2360_);
v___x_2363_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2364_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2365_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2353_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
v___x_2366_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2367_ = l_Array_append___redArg(v___x_2366_, v_handlers_2295_);
lean_dec_ref(v_handlers_2295_);
v___x_2368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2353_);
lean_ctor_set(v___x_2368_, 1, v___x_2294_);
v___x_2369_ = lean_array_push(v___x_2367_, v___x_2368_);
v___x_2370_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29);
v___x_2371_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30));
lean_inc(v_currMacroScope_2351_);
lean_inc(v_quotContext_2350_);
v___x_2372_ = l_Lean_addMacroScope(v_quotContext_2350_, v___x_2371_, v_currMacroScope_2351_);
v___x_2373_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__32));
v___x_2374_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2353_);
lean_ctor_set(v___x_2374_, 1, v___x_2370_);
lean_ctor_set(v___x_2374_, 2, v___x_2372_);
lean_ctor_set(v___x_2374_, 3, v___x_2373_);
v___x_2375_ = lean_array_push(v___x_2369_, v___x_2374_);
v___x_2376_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2353_);
lean_ctor_set(v___x_2376_, 1, v___x_2359_);
lean_ctor_set(v___x_2376_, 2, v___x_2375_);
v___x_2377_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2378_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2353_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
v___x_2379_ = l_Lean_Syntax_node3(v___x_2353_, v___x_2363_, v___x_2365_, v___x_2376_, v___x_2378_);
v___x_2380_ = l_Lean_Syntax_node2(v___x_2353_, v___x_2361_, v___x_2362_, v___x_2379_);
v___x_2381_ = l_Lean_Syntax_node1(v___x_2353_, v___x_2359_, v___x_2380_);
v___x_2382_ = l_Lean_Syntax_node1(v___x_2353_, v___x_2358_, v___x_2381_);
v___x_2383_ = l_Lean_Syntax_node1(v___x_2353_, v___x_2357_, v___x_2382_);
v___x_2384_ = l_Lean_Syntax_node2(v___x_2353_, v___x_2354_, v___x_2356_, v___x_2383_);
v___x_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
return v___x_2385_;
}
default: 
{
lean_object* v_e_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v_e_2386_ = lean_ctor_get(v_default_2288_, 0);
lean_inc_ref(v_e_2386_);
lean_dec_ref_known(v_default_2288_, 1);
v___x_2387_ = lean_box(1);
v___x_2388_ = l_Lean_PrettyPrinter_delab(v_e_2386_, v___x_2387_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2425_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2391_ = v___x_2388_;
v_isShared_2392_ = v_isSharedCheck_2425_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2388_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2425_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v_ref_2393_; uint8_t v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2423_; 
v_ref_2393_ = lean_ctor_get(v_a_2291_, 2);
v___x_2394_ = 0;
v___x_2395_ = l_Lean_SourceInfo_fromRef(v_ref_2393_, v___x_2394_);
v___x_2396_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2397_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2395_, 11);
v___x_2398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2395_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
v___x_2399_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2400_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2401_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2402_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2403_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2404_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2395_);
lean_ctor_set(v___x_2404_, 1, v___x_2402_);
v___x_2405_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2406_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2395_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
v___x_2408_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2409_ = l_Array_append___redArg(v___x_2408_, v_handlers_2295_);
lean_dec_ref(v_handlers_2295_);
v___x_2410_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2395_);
lean_ctor_set(v___x_2410_, 1, v___x_2294_);
v___x_2411_ = lean_array_push(v___x_2409_, v___x_2410_);
v___x_2412_ = lean_array_push(v___x_2411_, v_a_2389_);
v___x_2413_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2395_);
lean_ctor_set(v___x_2413_, 1, v___x_2401_);
lean_ctor_set(v___x_2413_, 2, v___x_2412_);
v___x_2414_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2415_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2395_);
lean_ctor_set(v___x_2415_, 1, v___x_2414_);
v___x_2416_ = l_Lean_Syntax_node3(v___x_2395_, v___x_2405_, v___x_2407_, v___x_2413_, v___x_2415_);
v___x_2417_ = l_Lean_Syntax_node2(v___x_2395_, v___x_2403_, v___x_2404_, v___x_2416_);
v___x_2418_ = l_Lean_Syntax_node1(v___x_2395_, v___x_2401_, v___x_2417_);
v___x_2419_ = l_Lean_Syntax_node1(v___x_2395_, v___x_2400_, v___x_2418_);
v___x_2420_ = l_Lean_Syntax_node1(v___x_2395_, v___x_2399_, v___x_2419_);
v___x_2421_ = l_Lean_Syntax_node2(v___x_2395_, v___x_2396_, v___x_2398_, v___x_2420_);
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 0, v___x_2421_);
v___x_2423_ = v___x_2391_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
else
{
lean_dec_ref(v_handlers_2295_);
return v___x_2388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___boxed(lean_object* v_handlers_2426_, lean_object* v_default_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_handlers_2426_, v_default_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec_ref(v_handlers_2426_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(lean_object* v_e_2434_, lean_object* v___y_2435_){
_start:
{
uint8_t v___x_2437_; 
v___x_2437_ = l_Lean_Expr_hasMVar(v_e_2434_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2438_; 
v___x_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2438_, 0, v_e_2434_);
return v___x_2438_;
}
else
{
lean_object* v___x_2439_; lean_object* v_mctx_2440_; lean_object* v___x_2441_; lean_object* v_fst_2442_; lean_object* v_snd_2443_; lean_object* v___x_2444_; lean_object* v_cache_2445_; lean_object* v_zetaDeltaFVarIds_2446_; lean_object* v_postponed_2447_; lean_object* v_diag_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2457_; 
v___x_2439_ = lean_st_ref_get(v___y_2435_);
v_mctx_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc_ref(v_mctx_2440_);
lean_dec(v___x_2439_);
v___x_2441_ = l_Lean_instantiateMVarsCore(v_mctx_2440_, v_e_2434_);
v_fst_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_fst_2442_);
v_snd_2443_ = lean_ctor_get(v___x_2441_, 1);
lean_inc(v_snd_2443_);
lean_dec_ref(v___x_2441_);
v___x_2444_ = lean_st_ref_take(v___y_2435_);
v_cache_2445_ = lean_ctor_get(v___x_2444_, 1);
v_zetaDeltaFVarIds_2446_ = lean_ctor_get(v___x_2444_, 2);
v_postponed_2447_ = lean_ctor_get(v___x_2444_, 3);
v_diag_2448_ = lean_ctor_get(v___x_2444_, 4);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2457_ == 0)
{
lean_object* v_unused_2458_; 
v_unused_2458_ = lean_ctor_get(v___x_2444_, 0);
lean_dec(v_unused_2458_);
v___x_2450_ = v___x_2444_;
v_isShared_2451_ = v_isSharedCheck_2457_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_diag_2448_);
lean_inc(v_postponed_2447_);
lean_inc(v_zetaDeltaFVarIds_2446_);
lean_inc(v_cache_2445_);
lean_dec(v___x_2444_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2457_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v_snd_2443_);
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_snd_2443_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_cache_2445_);
lean_ctor_set(v_reuseFailAlloc_2456_, 2, v_zetaDeltaFVarIds_2446_);
lean_ctor_set(v_reuseFailAlloc_2456_, 3, v_postponed_2447_);
lean_ctor_set(v_reuseFailAlloc_2456_, 4, v_diag_2448_);
v___x_2453_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = lean_st_ref_put(v___y_2435_, v___x_2453_);
v___x_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2455_, 0, v_fst_2442_);
return v___x_2455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg___boxed(lean_object* v_e_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2459_, v___y_2460_);
lean_dec(v___y_2460_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(lean_object* v_e_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2463_, v___y_2469_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___boxed(lean_object* v_e_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(v_e_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(lean_object* v_x_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; 
lean_inc(v___y_2489_);
lean_inc_ref(v___y_2488_);
lean_inc(v___y_2487_);
lean_inc_ref(v___y_2486_);
v___x_2495_ = lean_apply_9(v_x_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, lean_box(0));
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed(lean_object* v_x_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(v_x_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(lean_object* v_mvarId_2507_, lean_object* v_x_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___f_2518_; lean_object* v___x_2519_; 
lean_inc(v___y_2512_);
lean_inc_ref(v___y_2511_);
lean_inc(v___y_2510_);
lean_inc_ref(v___y_2509_);
v___f_2518_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2518_, 0, v_x_2508_);
lean_closure_set(v___f_2518_, 1, v___y_2509_);
lean_closure_set(v___f_2518_, 2, v___y_2510_);
lean_closure_set(v___f_2518_, 3, v___y_2511_);
lean_closure_set(v___f_2518_, 4, v___y_2512_);
v___x_2519_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2507_, v___f_2518_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2519_) == 0)
{
return v___x_2519_;
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2519_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2519_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___boxed(lean_object* v_mvarId_2528_, lean_object* v_x_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2528_, v_x_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(lean_object* v_00_u03b1_2540_, lean_object* v_mvarId_2541_, lean_object* v_x_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v___x_2552_; 
v___x_2552_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2541_, v_x_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___boxed(lean_object* v_00_u03b1_2553_, lean_object* v_mvarId_2554_, lean_object* v_x_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(v_00_u03b1_2553_, v_mvarId_2554_, v_x_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(lean_object* v_a_2566_, lean_object* v_inv_2567_, lean_object* v_xs_2568_, uint8_t v___x_2569_, lean_object* v___x_2570_, lean_object* v_letMuts_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v___x_2581_; 
lean_inc_ref(v_letMuts_2571_);
lean_inc_ref(v_xs_2568_);
v___x_2581_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_a_2566_, v_inv_2567_, v_xs_2568_, v_letMuts_2571_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2658_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2584_ = v___x_2581_;
v_isShared_2585_ = v_isSharedCheck_2658_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2581_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2658_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
if (lean_obj_tag(v_a_2582_) == 1)
{
lean_object* v_val_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2653_; 
lean_del_object(v___x_2584_);
v_val_2586_ = lean_ctor_get(v_a_2582_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v_a_2582_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2588_ = v_a_2582_;
v_isShared_2589_ = v_isSharedCheck_2653_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_val_2586_);
lean_dec(v_a_2582_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2653_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v_snd_2590_; lean_object* v_fst_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2652_; 
v_snd_2590_ = lean_ctor_get(v_val_2586_, 1);
v_fst_2591_ = lean_ctor_get(v_val_2586_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_val_2586_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2593_ = v_val_2586_;
v_isShared_2594_ = v_isSharedCheck_2652_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_snd_2590_);
lean_inc(v_fst_2591_);
lean_dec(v_val_2586_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2652_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v_fst_2595_; lean_object* v_snd_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2651_; 
v_fst_2595_ = lean_ctor_get(v_snd_2590_, 0);
v_snd_2596_ = lean_ctor_get(v_snd_2590_, 1);
v_isSharedCheck_2651_ = !lean_is_exclusive(v_snd_2590_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2598_ = v_snd_2590_;
v_isShared_2599_ = v_isSharedCheck_2651_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_snd_2596_);
lean_inc(v_fst_2595_);
lean_dec(v_snd_2590_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2651_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v_lvl_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; uint8_t v___x_2609_; uint8_t v___x_2610_; lean_object* v___x_2611_; 
v_lvl_2600_ = lean_ctor_get(v_fst_2591_, 0);
lean_inc(v_lvl_2600_);
v___x_2601_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2591_);
lean_inc(v_fst_2595_);
v___x_2602_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2595_);
v___x_2603_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(v_lvl_2600_, v___x_2601_, v___x_2602_);
v___x_2604_ = lean_unsigned_to_nat(2u);
v___x_2605_ = lean_mk_empty_array_with_capacity(v___x_2604_);
v___x_2606_ = lean_array_push(v___x_2605_, v_xs_2568_);
lean_inc_ref(v_letMuts_2571_);
v___x_2607_ = lean_array_push(v___x_2606_, v_letMuts_2571_);
v___x_2608_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v___x_2603_);
v___x_2609_ = 0;
v___x_2610_ = 1;
v___x_2611_ = l_Lean_Meta_mkLambdaFVars(v___x_2607_, v___x_2608_, v___x_2609_, v___x_2569_, v___x_2609_, v___x_2569_, v___x_2610_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
lean_dec_ref(v___x_2607_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v_letMutsPred_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2611_, 1);
v_letMutsPred_2613_ = lean_ctor_get(v_fst_2595_, 2);
lean_inc_ref(v_letMutsPred_2613_);
lean_dec(v_fst_2595_);
v___x_2614_ = lean_mk_empty_array_with_capacity(v___x_2570_);
v___x_2615_ = lean_array_push(v___x_2614_, v_letMuts_2571_);
v___x_2616_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v_letMutsPred_2613_);
v___x_2617_ = l_Lean_Meta_mkLambdaFVars(v___x_2615_, v___x_2616_, v___x_2609_, v___x_2569_, v___x_2609_, v___x_2569_, v___x_2610_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
lean_dec_ref(v___x_2615_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2634_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2620_ = v___x_2617_;
v_isShared_2621_ = v_isSharedCheck_2634_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2617_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2634_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v_a_2618_);
v___x_2623_ = v___x_2598_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2618_);
lean_ctor_set(v_reuseFailAlloc_2633_, 1, v_snd_2596_);
v___x_2623_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
lean_object* v___x_2625_; 
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 1, v___x_2623_);
lean_ctor_set(v___x_2593_, 0, v_a_2612_);
v___x_2625_ = v___x_2593_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2612_);
lean_ctor_set(v_reuseFailAlloc_2632_, 1, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
lean_object* v___x_2627_; 
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 0, v___x_2625_);
v___x_2627_ = v___x_2588_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
lean_object* v___x_2629_; 
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v___x_2627_);
v___x_2629_ = v___x_2620_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2627_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
lean_dec(v_a_2612_);
lean_del_object(v___x_2598_);
lean_dec(v_snd_2596_);
lean_del_object(v___x_2593_);
lean_del_object(v___x_2588_);
v_a_2635_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2617_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2617_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_del_object(v___x_2598_);
lean_dec(v_snd_2596_);
lean_dec(v_fst_2595_);
lean_del_object(v___x_2593_);
lean_del_object(v___x_2588_);
lean_dec_ref(v_letMuts_2571_);
v_a_2643_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2611_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2611_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2654_; lean_object* v___x_2656_; 
lean_dec(v_a_2582_);
lean_dec_ref(v_letMuts_2571_);
lean_dec_ref(v_xs_2568_);
v___x_2654_ = lean_box(0);
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 0, v___x_2654_);
v___x_2656_ = v___x_2584_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2654_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
lean_dec_ref(v_letMuts_2571_);
lean_dec_ref(v_xs_2568_);
v_a_2659_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2581_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2581_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed(lean_object* v_a_2667_, lean_object* v_inv_2668_, lean_object* v_xs_2669_, lean_object* v___x_2670_, lean_object* v___x_2671_, lean_object* v_letMuts_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
uint8_t v___x_77262__boxed_2682_; lean_object* v_res_2683_; 
v___x_77262__boxed_2682_ = lean_unbox(v___x_2670_);
v_res_2683_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(v_a_2667_, v_inv_2668_, v_xs_2669_, v___x_77262__boxed_2682_, v___x_2671_, v_letMuts_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___x_2671_);
lean_dec_ref(v_a_2667_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(lean_object* v_k_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v_b_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v___x_2695_; 
lean_inc(v___y_2693_);
lean_inc_ref(v___y_2692_);
lean_inc(v___y_2691_);
lean_inc_ref(v___y_2690_);
lean_inc(v___y_2688_);
lean_inc_ref(v___y_2687_);
lean_inc(v___y_2686_);
lean_inc_ref(v___y_2685_);
v___x_2695_ = lean_apply_10(v_k_2684_, v_b_2689_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, lean_box(0));
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_k_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v_b_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(v_k_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v_b_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(lean_object* v_name_2708_, uint8_t v_bi_2709_, lean_object* v_type_2710_, lean_object* v_k_2711_, uint8_t v_kind_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v___f_2722_; lean_object* v___x_2723_; 
lean_inc(v___y_2716_);
lean_inc_ref(v___y_2715_);
lean_inc(v___y_2714_);
lean_inc_ref(v___y_2713_);
v___f_2722_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2722_, 0, v_k_2711_);
lean_closure_set(v___f_2722_, 1, v___y_2713_);
lean_closure_set(v___f_2722_, 2, v___y_2714_);
lean_closure_set(v___f_2722_, 3, v___y_2715_);
lean_closure_set(v___f_2722_, 4, v___y_2716_);
v___x_2723_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2708_, v_bi_2709_, v_type_2710_, v___f_2722_, v_kind_2712_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
if (lean_obj_tag(v___x_2723_) == 0)
{
return v___x_2723_;
}
else
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___x_2723_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2723_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___boxed(lean_object* v_name_2732_, lean_object* v_bi_2733_, lean_object* v_type_2734_, lean_object* v_k_2735_, lean_object* v_kind_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
uint8_t v_bi_boxed_2746_; uint8_t v_kind_boxed_2747_; lean_object* v_res_2748_; 
v_bi_boxed_2746_ = lean_unbox(v_bi_2733_);
v_kind_boxed_2747_ = lean_unbox(v_kind_2736_);
v_res_2748_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2732_, v_bi_boxed_2746_, v_type_2734_, v_k_2735_, v_kind_boxed_2747_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(lean_object* v_name_2749_, lean_object* v_type_2750_, lean_object* v_k_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
uint8_t v___x_2761_; uint8_t v___x_2762_; lean_object* v___x_2763_; 
v___x_2761_ = 0;
v___x_2762_ = 0;
v___x_2763_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2749_, v___x_2761_, v_type_2750_, v_k_2751_, v___x_2762_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg___boxed(lean_object* v_name_2764_, lean_object* v_type_2765_, lean_object* v_k_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_2764_, v_type_2765_, v_k_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(lean_object* v_a_2780_, lean_object* v_inv_2781_, uint8_t v___x_2782_, lean_object* v___x_2783_, lean_object* v_arg_2784_, lean_object* v_xs_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v___x_2795_; lean_object* v___f_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2795_ = lean_box(v___x_2782_);
v___f_2796_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed), 15, 5);
lean_closure_set(v___f_2796_, 0, v_a_2780_);
lean_closure_set(v___f_2796_, 1, v_inv_2781_);
lean_closure_set(v___f_2796_, 2, v_xs_2785_);
lean_closure_set(v___f_2796_, 3, v___x_2795_);
lean_closure_set(v___f_2796_, 4, v___x_2783_);
v___x_2797_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_2798_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_2797_, v_arg_2784_, v___f_2796_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed(lean_object* v_a_2799_, lean_object* v_inv_2800_, lean_object* v___x_2801_, lean_object* v___x_2802_, lean_object* v_arg_2803_, lean_object* v_xs_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
uint8_t v___x_77582__boxed_2814_; lean_object* v_res_2815_; 
v___x_77582__boxed_2814_ = lean_unbox(v___x_2801_);
v_res_2815_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(v_a_2799_, v_inv_2800_, v___x_77582__boxed_2814_, v___x_2802_, v_arg_2803_, v_xs_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
return v_res_2815_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2819_; 
v___x_2819_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2819_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2);
v___x_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2820_);
return v___x_2821_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4(void){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2822_ = lean_unsigned_to_nat(32u);
v___x_2823_ = lean_mk_empty_array_with_capacity(v___x_2822_);
v___x_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(lean_object* v_fst_2825_, lean_object* v_xs_2826_, lean_object* v_fst_2827_, lean_object* v_r_2828_, lean_object* v___x_2829_, lean_object* v_fst_2830_, uint8_t v___x_2831_, lean_object* v___x_2832_, lean_object* v_letMuts_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v___x_2843_; 
lean_inc_ref(v_fst_2825_);
v___x_2843_ = l_Lean_Meta_mkNone(v_fst_2825_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
lean_dec_ref_known(v___x_2843_, 1);
v___x_2845_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_2846_ = lean_unsigned_to_nat(2u);
v___x_2847_ = lean_mk_empty_array_with_capacity(v___x_2846_);
lean_inc_ref(v___x_2847_);
v___x_2848_ = lean_array_push(v___x_2847_, v_a_2844_);
lean_inc_ref(v_letMuts_2833_);
v___x_2849_ = lean_array_push(v___x_2848_, v_letMuts_2833_);
v___x_2850_ = l_Lean_Meta_mkAppM(v___x_2845_, v___x_2849_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
lean_inc_ref(v___x_2847_);
v___x_2852_ = lean_array_push(v___x_2847_, v_xs_2826_);
v___x_2853_ = lean_array_push(v___x_2852_, v_a_2851_);
v___x_2854_ = l_Lean_Expr_beta(v_fst_2827_, v___x_2853_);
v___x_2855_ = l_Lean_Meta_mkSome(v_fst_2825_, v_r_2828_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2855_, 1);
v___x_2857_ = lean_array_push(v___x_2847_, v_a_2856_);
v___x_2858_ = lean_array_push(v___x_2857_, v_letMuts_2833_);
v___x_2859_ = l_Lean_Meta_mkAppM(v___x_2845_, v___x_2858_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref_known(v___x_2859_, 1);
v___x_2861_ = lean_mk_empty_array_with_capacity(v___x_2829_);
lean_inc_ref(v___x_2861_);
v___x_2862_ = lean_array_push(v___x_2861_, v_a_2860_);
v___x_2863_ = l_Lean_Expr_beta(v_fst_2830_, v___x_2862_);
v___x_2864_ = l_Lean_Meta_getSimpTheorems___redArg(v___y_2841_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2866_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2864_, 1);
v___x_2866_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_2841_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; uint8_t v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref_known(v___x_2866_, 1);
v___x_2868_ = lean_unsigned_to_nat(100000u);
v___x_2869_ = 0;
v___x_2870_ = 0;
v___x_2871_ = lean_box(0);
v___x_2872_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_2872_, 0, v___x_2868_);
lean_ctor_set(v___x_2872_, 1, v___x_2846_);
lean_ctor_set(v___x_2872_, 2, v___x_2871_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3, v___x_2869_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 1, v___x_2831_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 2, v___x_2869_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 3, v___x_2831_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 4, v___x_2831_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 5, v___x_2831_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 6, v___x_2870_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 7, v___x_2831_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 8, v___x_2831_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 9, v___x_2869_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 10, v___x_2869_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 11, v___x_2869_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 12, v___x_2831_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 13, v___x_2831_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 14, v___x_2869_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 15, v___x_2869_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 16, v___x_2869_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 17, v___x_2831_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 18, v___x_2831_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 19, v___x_2831_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 20, v___x_2831_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 21, v___x_2831_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 22, v___x_2831_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 23, v___x_2831_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 24, v___x_2831_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 25, v___x_2831_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 26, v___x_2869_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 27, v___x_2869_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 28, v___x_2869_);
v___x_2873_ = lean_array_push(v___x_2861_, v_a_2865_);
v___x_2874_ = l_Lean_Options_empty;
v___x_2875_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2872_, v___x_2873_, v_a_2867_, v___x_2874_, v___y_2838_, v___y_2840_, v___y_2841_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2876_);
lean_dec_ref_known(v___x_2875_, 1);
v___x_2877_ = lean_mk_empty_array_with_capacity(v___x_2832_);
v___x_2878_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__1));
v___x_2879_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_2877_, v___x_2878_, v___x_2869_, v___y_2840_, v___y_2841_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; size_t v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc_n(v_a_2880_, 2);
lean_dec_ref_known(v___x_2879_, 1);
v___x_2881_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3);
lean_inc_n(v___x_2832_, 2);
v___x_2882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
lean_ctor_set(v___x_2882_, 1, v___x_2832_);
v___x_2883_ = lean_unsigned_to_nat(32u);
v___x_2884_ = lean_mk_empty_array_with_capacity(v___x_2883_);
v___x_2885_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4);
v___x_2886_ = ((size_t)5ULL);
v___x_2887_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2887_, 0, v___x_2885_);
lean_ctor_set(v___x_2887_, 1, v___x_2884_);
lean_ctor_set(v___x_2887_, 2, v___x_2832_);
lean_ctor_set(v___x_2887_, 3, v___x_2832_);
lean_ctor_set_usize(v___x_2887_, 4, v___x_2886_);
v___x_2888_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2881_);
lean_ctor_set(v___x_2888_, 1, v___x_2881_);
lean_ctor_set(v___x_2888_, 2, v___x_2881_);
lean_ctor_set(v___x_2888_, 3, v___x_2887_);
v___x_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2882_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
lean_inc(v_a_2876_);
v___x_2890_ = l_Lean_Meta_simp(v___x_2854_, v_a_2876_, v_a_2880_, v___x_2871_, v___x_2889_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v_fst_2892_; lean_object* v___x_2893_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
lean_dec_ref_known(v___x_2890_, 1);
v_fst_2892_ = lean_ctor_get(v_a_2891_, 0);
lean_inc(v_fst_2892_);
lean_dec(v_a_2891_);
v___x_2893_ = l_Lean_Meta_simp(v___x_2863_, v_a_2876_, v_a_2880_, v___x_2871_, v___x_2889_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
lean_dec_ref_known(v___x_2889_, 2);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v_fst_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2932_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2893_, 1);
v_fst_2895_ = lean_ctor_get(v_a_2894_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v_a_2894_);
if (v_isSharedCheck_2932_ == 0)
{
lean_object* v_unused_2933_; 
v_unused_2933_ = lean_ctor_get(v_a_2894_, 1);
lean_dec(v_unused_2933_);
v___x_2897_ = v_a_2894_;
v_isShared_2898_ = v_isSharedCheck_2932_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_fst_2895_);
lean_dec(v_a_2894_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2932_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v_expr_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v_expr_2899_ = lean_ctor_get(v_fst_2892_, 0);
lean_inc_ref(v_expr_2899_);
lean_dec(v_fst_2892_);
v___x_2900_ = lean_box(1);
v___x_2901_ = l_Lean_PrettyPrinter_delab(v_expr_2899_, v___x_2900_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v_expr_2903_; lean_object* v___x_2904_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref_known(v___x_2901_, 1);
v_expr_2903_ = lean_ctor_get(v_fst_2895_, 0);
lean_inc_ref(v_expr_2903_);
lean_dec(v_fst_2895_);
v___x_2904_ = l_Lean_PrettyPrinter_delab(v_expr_2903_, v___x_2900_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2915_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2907_ = v___x_2904_;
v_isShared_2908_ = v_isSharedCheck_2915_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2904_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2915_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 1, v_a_2905_);
lean_ctor_set(v___x_2897_, 0, v_a_2902_);
v___x_2910_ = v___x_2897_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2902_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
lean_object* v___x_2912_; 
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 0, v___x_2910_);
v___x_2912_ = v___x_2907_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2910_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec(v_a_2902_);
lean_del_object(v___x_2897_);
v_a_2916_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2904_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2904_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
else
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
lean_del_object(v___x_2897_);
lean_dec(v_fst_2895_);
v_a_2924_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2901_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2901_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec(v_fst_2892_);
v_a_2934_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2893_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2893_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_dec_ref_known(v___x_2889_, 2);
lean_dec(v_a_2880_);
lean_dec(v_a_2876_);
lean_dec_ref(v___x_2863_);
v_a_2942_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2890_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2890_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
lean_dec(v_a_2876_);
lean_dec_ref(v___x_2863_);
lean_dec_ref(v___x_2854_);
lean_dec(v___x_2832_);
v_a_2950_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2879_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2879_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
else
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
lean_dec_ref(v___x_2863_);
lean_dec_ref(v___x_2854_);
lean_dec(v___x_2832_);
v_a_2958_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2875_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2875_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_dec(v_a_2865_);
lean_dec_ref(v___x_2863_);
lean_dec_ref(v___x_2861_);
lean_dec_ref(v___x_2854_);
lean_dec(v___x_2832_);
v_a_2966_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2866_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2866_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_dec_ref(v___x_2863_);
lean_dec_ref(v___x_2861_);
lean_dec_ref(v___x_2854_);
lean_dec(v___x_2832_);
v_a_2974_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2864_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2864_);
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
lean_dec_ref(v___x_2854_);
lean_dec(v___x_2832_);
lean_dec_ref(v_fst_2830_);
v_a_2982_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2859_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2859_);
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
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v_letMuts_2833_);
lean_dec(v___x_2832_);
lean_dec_ref(v_fst_2830_);
v_a_2990_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2855_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2855_);
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
lean_dec_ref(v___x_2847_);
lean_dec_ref(v_letMuts_2833_);
lean_dec(v___x_2832_);
lean_dec_ref(v_fst_2830_);
lean_dec_ref(v_r_2828_);
lean_dec_ref(v_fst_2827_);
lean_dec_ref(v_xs_2826_);
lean_dec_ref(v_fst_2825_);
v_a_2998_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2850_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2850_);
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
lean_dec_ref(v_letMuts_2833_);
lean_dec(v___x_2832_);
lean_dec_ref(v_fst_2830_);
lean_dec_ref(v_r_2828_);
lean_dec_ref(v_fst_2827_);
lean_dec_ref(v_xs_2826_);
lean_dec_ref(v_fst_2825_);
v_a_3006_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_2843_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_2843_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed(lean_object** _args){
lean_object* v_fst_3014_ = _args[0];
lean_object* v_xs_3015_ = _args[1];
lean_object* v_fst_3016_ = _args[2];
lean_object* v_r_3017_ = _args[3];
lean_object* v___x_3018_ = _args[4];
lean_object* v_fst_3019_ = _args[5];
lean_object* v___x_3020_ = _args[6];
lean_object* v___x_3021_ = _args[7];
lean_object* v_letMuts_3022_ = _args[8];
lean_object* v___y_3023_ = _args[9];
lean_object* v___y_3024_ = _args[10];
lean_object* v___y_3025_ = _args[11];
lean_object* v___y_3026_ = _args[12];
lean_object* v___y_3027_ = _args[13];
lean_object* v___y_3028_ = _args[14];
lean_object* v___y_3029_ = _args[15];
lean_object* v___y_3030_ = _args[16];
lean_object* v___y_3031_ = _args[17];
_start:
{
uint8_t v___x_77658__boxed_3032_; lean_object* v_res_3033_; 
v___x_77658__boxed_3032_ = lean_unbox(v___x_3020_);
v_res_3033_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(v_fst_3014_, v_xs_3015_, v_fst_3016_, v_r_3017_, v___x_3018_, v_fst_3019_, v___x_77658__boxed_3032_, v___x_3021_, v_letMuts_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___x_3018_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(lean_object* v_fst_3034_, lean_object* v_xs_3035_, lean_object* v_fst_3036_, lean_object* v___x_3037_, lean_object* v_fst_3038_, uint8_t v___x_3039_, lean_object* v___x_3040_, lean_object* v_snd_3041_, lean_object* v_r_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v___x_3052_; lean_object* v___f_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3052_ = lean_box(v___x_3039_);
v___f_3053_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed), 18, 8);
lean_closure_set(v___f_3053_, 0, v_fst_3034_);
lean_closure_set(v___f_3053_, 1, v_xs_3035_);
lean_closure_set(v___f_3053_, 2, v_fst_3036_);
lean_closure_set(v___f_3053_, 3, v_r_3042_);
lean_closure_set(v___f_3053_, 4, v___x_3037_);
lean_closure_set(v___f_3053_, 5, v_fst_3038_);
lean_closure_set(v___f_3053_, 6, v___x_3052_);
lean_closure_set(v___f_3053_, 7, v___x_3040_);
v___x_3054_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3055_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3054_, v_snd_3041_, v___f_3053_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed(lean_object** _args){
lean_object* v_fst_3056_ = _args[0];
lean_object* v_xs_3057_ = _args[1];
lean_object* v_fst_3058_ = _args[2];
lean_object* v___x_3059_ = _args[3];
lean_object* v_fst_3060_ = _args[4];
lean_object* v___x_3061_ = _args[5];
lean_object* v___x_3062_ = _args[6];
lean_object* v_snd_3063_ = _args[7];
lean_object* v_r_3064_ = _args[8];
lean_object* v___y_3065_ = _args[9];
lean_object* v___y_3066_ = _args[10];
lean_object* v___y_3067_ = _args[11];
lean_object* v___y_3068_ = _args[12];
lean_object* v___y_3069_ = _args[13];
lean_object* v___y_3070_ = _args[14];
lean_object* v___y_3071_ = _args[15];
lean_object* v___y_3072_ = _args[16];
lean_object* v___y_3073_ = _args[17];
_start:
{
uint8_t v___x_78054__boxed_3074_; lean_object* v_res_3075_; 
v___x_78054__boxed_3074_ = lean_unbox(v___x_3061_);
v_res_3075_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(v_fst_3056_, v_xs_3057_, v_fst_3058_, v___x_3059_, v_fst_3060_, v___x_78054__boxed_3074_, v___x_3062_, v_snd_3063_, v_r_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(lean_object* v_fst_3079_, lean_object* v_fst_3080_, lean_object* v___x_3081_, lean_object* v_fst_3082_, uint8_t v___x_3083_, lean_object* v___x_3084_, lean_object* v_snd_3085_, lean_object* v_xs_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v___x_3096_; lean_object* v___f_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3096_ = lean_box(v___x_3083_);
lean_inc_ref(v_fst_3079_);
v___f_3097_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed), 18, 8);
lean_closure_set(v___f_3097_, 0, v_fst_3079_);
lean_closure_set(v___f_3097_, 1, v_xs_3086_);
lean_closure_set(v___f_3097_, 2, v_fst_3080_);
lean_closure_set(v___f_3097_, 3, v___x_3081_);
lean_closure_set(v___f_3097_, 4, v_fst_3082_);
lean_closure_set(v___f_3097_, 5, v___x_3096_);
lean_closure_set(v___f_3097_, 6, v___x_3084_);
lean_closure_set(v___f_3097_, 7, v_snd_3085_);
v___x_3098_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_3099_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3098_, v_fst_3079_, v___f_3097_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed(lean_object** _args){
lean_object* v_fst_3100_ = _args[0];
lean_object* v_fst_3101_ = _args[1];
lean_object* v___x_3102_ = _args[2];
lean_object* v_fst_3103_ = _args[3];
lean_object* v___x_3104_ = _args[4];
lean_object* v___x_3105_ = _args[5];
lean_object* v_snd_3106_ = _args[6];
lean_object* v_xs_3107_ = _args[7];
lean_object* v___y_3108_ = _args[8];
lean_object* v___y_3109_ = _args[9];
lean_object* v___y_3110_ = _args[10];
lean_object* v___y_3111_ = _args[11];
lean_object* v___y_3112_ = _args[12];
lean_object* v___y_3113_ = _args[13];
lean_object* v___y_3114_ = _args[14];
lean_object* v___y_3115_ = _args[15];
lean_object* v___y_3116_ = _args[16];
_start:
{
uint8_t v___x_78117__boxed_3117_; lean_object* v_res_3118_; 
v___x_78117__boxed_3117_ = lean_unbox(v___x_3104_);
v_res_3118_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(v_fst_3100_, v_fst_3101_, v___x_3102_, v_fst_3103_, v___x_78117__boxed_3117_, v___x_3105_, v_snd_3106_, v_xs_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(lean_object* v_as_3119_, size_t v_sz_3120_, size_t v_i_3121_, lean_object* v_b_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
uint8_t v___x_3128_; 
v___x_3128_ = lean_usize_dec_lt(v_i_3121_, v_sz_3120_);
if (v___x_3128_ == 0)
{
lean_object* v___x_3129_; 
v___x_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3129_, 0, v_b_3122_);
return v___x_3129_;
}
else
{
lean_object* v___x_3130_; lean_object* v_a_3131_; lean_object* v___x_3132_; 
v___x_3130_ = lean_box(1);
v_a_3131_ = lean_array_uget_borrowed(v_as_3119_, v_i_3121_);
lean_inc(v_a_3131_);
v___x_3132_ = l_Lean_PrettyPrinter_delab(v_a_3131_, v___x_3130_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; lean_object* v___x_3134_; size_t v___x_3135_; size_t v___x_3136_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_a_3133_);
lean_dec_ref_known(v___x_3132_, 1);
v___x_3134_ = lean_array_push(v_b_3122_, v_a_3133_);
v___x_3135_ = ((size_t)1ULL);
v___x_3136_ = lean_usize_add(v_i_3121_, v___x_3135_);
v_i_3121_ = v___x_3136_;
v_b_3122_ = v___x_3134_;
goto _start;
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_dec_ref(v_b_3122_);
v_a_3138_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3132_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3132_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg___boxed(lean_object* v_as_3146_, lean_object* v_sz_3147_, lean_object* v_i_3148_, lean_object* v_b_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
size_t v_sz_boxed_3155_; size_t v_i_boxed_3156_; lean_object* v_res_3157_; 
v_sz_boxed_3155_ = lean_unbox_usize(v_sz_3147_);
lean_dec(v_sz_3147_);
v_i_boxed_3156_ = lean_unbox_usize(v_i_3148_);
lean_dec(v_i_3148_);
v_res_3157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_3146_, v_sz_boxed_3155_, v_i_boxed_3156_, v_b_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec_ref(v_as_3146_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(lean_object* v_xs_3178_, lean_object* v_fst_3179_, lean_object* v_snd_3180_, lean_object* v___x_3181_, lean_object* v___x_3182_, lean_object* v___x_3183_, lean_object* v___x_3184_, lean_object* v___x_3185_, lean_object* v___x_3186_, lean_object* v___x_3187_, lean_object* v___x_3188_, lean_object* v_letMuts_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3199_ = lean_unsigned_to_nat(2u);
v___x_3200_ = lean_mk_empty_array_with_capacity(v___x_3199_);
v___x_3201_ = lean_array_push(v___x_3200_, v_xs_3178_);
v___x_3202_ = lean_array_push(v___x_3201_, v_letMuts_3189_);
v___x_3203_ = l_Lean_Expr_beta(v_fst_3179_, v___x_3202_);
v___x_3204_ = lean_box(1);
v___x_3205_ = l_Lean_PrettyPrinter_delab(v___x_3203_, v___x_3204_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3345_; 
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3208_ = v___x_3205_;
v_isShared_3209_ = v_isSharedCheck_3345_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3345_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v_points_3210_; lean_object* v_default_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3344_; 
v_points_3210_ = lean_ctor_get(v_snd_3180_, 0);
v_default_3211_ = lean_ctor_get(v_snd_3180_, 1);
v_isSharedCheck_3344_ = !lean_is_exclusive(v_snd_3180_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3213_ = v_snd_3180_;
v_isShared_3214_ = v_isSharedCheck_3344_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_default_3211_);
lean_inc(v_points_3210_);
lean_dec(v_snd_3180_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3344_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
uint8_t v___y_3216_; lean_object* v___x_3267_; uint8_t v___x_3268_; 
v___x_3267_ = lean_array_get_size(v_points_3210_);
v___x_3268_ = lean_nat_dec_eq(v___x_3267_, v___x_3186_);
if (v___x_3268_ == 0)
{
lean_del_object(v___x_3208_);
lean_dec_ref(v___x_3188_);
lean_dec_ref(v___x_3187_);
v___y_3216_ = v___x_3268_;
goto v___jp_3215_;
}
else
{
if (lean_obj_tag(v_default_3211_) == 3)
{
uint8_t v___x_3269_; 
lean_del_object(v___x_3208_);
lean_dec_ref(v___x_3188_);
lean_dec_ref(v___x_3187_);
v___x_3269_ = 0;
v___y_3216_ = v___x_3269_;
goto v___jp_3215_;
}
else
{
lean_del_object(v___x_3213_);
lean_dec_ref(v_points_3210_);
if (lean_obj_tag(v_default_3211_) == 2)
{
lean_object* v_toCold_3270_; lean_object* v_ref_3271_; lean_object* v_quotContext_3272_; lean_object* v_currMacroScope_3273_; uint8_t v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3305_; 
v_toCold_3270_ = lean_ctor_get(v___y_3196_, 0);
v_ref_3271_ = lean_ctor_get(v___y_3196_, 2);
v_quotContext_3272_ = lean_ctor_get(v_toCold_3270_, 8);
v_currMacroScope_3273_ = lean_ctor_get(v_toCold_3270_, 9);
v___x_3274_ = 0;
v___x_3275_ = l_Lean_SourceInfo_fromRef(v_ref_3271_, v___x_3274_);
v___x_3276_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3277_ = l_Lean_Name_mkStr3(v___x_3187_, v___x_3188_, v___x_3276_);
v___x_3278_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__7));
v___x_3279_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3275_, 11);
v___x_3280_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3275_);
lean_ctor_set(v___x_3280_, 1, v___x_3278_);
lean_ctor_set(v___x_3280_, 2, v___x_3279_);
v___x_3281_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3275_);
lean_ctor_set(v___x_3282_, 1, v___x_3281_);
v___x_3283_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3284_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3285_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_3286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3275_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = l_String_toRawSubstring_x27(v___x_3181_);
lean_inc_n(v_currMacroScope_3273_, 2);
lean_inc_n(v_quotContext_3272_, 2);
v___x_3288_ = l_Lean_addMacroScope(v_quotContext_3272_, v___x_3182_, v_currMacroScope_3273_);
v___x_3289_ = lean_box(0);
v___x_3290_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3275_);
lean_ctor_set(v___x_3290_, 1, v___x_3287_);
lean_ctor_set(v___x_3290_, 2, v___x_3288_);
lean_ctor_set(v___x_3290_, 3, v___x_3289_);
v___x_3291_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3275_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = l_String_toRawSubstring_x27(v___x_3183_);
v___x_3294_ = l_Lean_addMacroScope(v_quotContext_3272_, v___x_3184_, v_currMacroScope_3273_);
v___x_3295_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3275_);
lean_ctor_set(v___x_3295_, 1, v___x_3293_);
lean_ctor_set(v___x_3295_, 2, v___x_3294_);
lean_ctor_set(v___x_3295_, 3, v___x_3289_);
v___x_3296_ = l_Lean_Syntax_node3(v___x_3275_, v___x_3283_, v___x_3290_, v___x_3292_, v___x_3295_);
v___x_3297_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3298_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3275_);
lean_ctor_set(v___x_3298_, 1, v___x_3297_);
v___x_3299_ = l_Lean_Syntax_node3(v___x_3275_, v___x_3284_, v___x_3286_, v___x_3296_, v___x_3298_);
v___x_3300_ = l_Lean_Syntax_node1(v___x_3275_, v___x_3283_, v___x_3299_);
v___x_3301_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3302_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3275_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = l_Lean_Syntax_node5(v___x_3275_, v___x_3277_, v___x_3280_, v___x_3282_, v___x_3300_, v___x_3302_, v_a_3206_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v___x_3303_);
v___x_3305_ = v___x_3208_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3303_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
else
{
lean_object* v_toCold_3307_; lean_object* v_ref_3308_; lean_object* v_quotContext_3309_; lean_object* v_currMacroScope_3310_; uint8_t v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3342_; 
lean_dec(v_default_3211_);
v_toCold_3307_ = lean_ctor_get(v___y_3196_, 0);
v_ref_3308_ = lean_ctor_get(v___y_3196_, 2);
v_quotContext_3309_ = lean_ctor_get(v_toCold_3307_, 8);
v_currMacroScope_3310_ = lean_ctor_get(v_toCold_3307_, 9);
v___x_3311_ = 0;
v___x_3312_ = l_Lean_SourceInfo_fromRef(v_ref_3308_, v___x_3311_);
v___x_3313_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__9));
v___x_3314_ = l_Lean_Name_mkStr3(v___x_3187_, v___x_3188_, v___x_3313_);
v___x_3315_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__7));
v___x_3316_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3312_, 11);
v___x_3317_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3312_);
lean_ctor_set(v___x_3317_, 1, v___x_3315_);
lean_ctor_set(v___x_3317_, 2, v___x_3316_);
v___x_3318_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__10));
v___x_3319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3312_);
lean_ctor_set(v___x_3319_, 1, v___x_3318_);
v___x_3320_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3321_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3322_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_3323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3312_);
lean_ctor_set(v___x_3323_, 1, v___x_3322_);
v___x_3324_ = l_String_toRawSubstring_x27(v___x_3181_);
lean_inc_n(v_currMacroScope_3310_, 2);
lean_inc_n(v_quotContext_3309_, 2);
v___x_3325_ = l_Lean_addMacroScope(v_quotContext_3309_, v___x_3182_, v_currMacroScope_3310_);
v___x_3326_ = lean_box(0);
v___x_3327_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3312_);
lean_ctor_set(v___x_3327_, 1, v___x_3324_);
lean_ctor_set(v___x_3327_, 2, v___x_3325_);
lean_ctor_set(v___x_3327_, 3, v___x_3326_);
v___x_3328_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3329_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3312_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
v___x_3330_ = l_String_toRawSubstring_x27(v___x_3183_);
v___x_3331_ = l_Lean_addMacroScope(v_quotContext_3309_, v___x_3184_, v_currMacroScope_3310_);
v___x_3332_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3312_);
lean_ctor_set(v___x_3332_, 1, v___x_3330_);
lean_ctor_set(v___x_3332_, 2, v___x_3331_);
lean_ctor_set(v___x_3332_, 3, v___x_3326_);
v___x_3333_ = l_Lean_Syntax_node3(v___x_3312_, v___x_3320_, v___x_3327_, v___x_3329_, v___x_3332_);
v___x_3334_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3335_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3312_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v___x_3336_ = l_Lean_Syntax_node3(v___x_3312_, v___x_3321_, v___x_3323_, v___x_3333_, v___x_3335_);
v___x_3337_ = l_Lean_Syntax_node1(v___x_3312_, v___x_3320_, v___x_3336_);
v___x_3338_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3339_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3312_);
lean_ctor_set(v___x_3339_, 1, v___x_3338_);
v___x_3340_ = l_Lean_Syntax_node5(v___x_3312_, v___x_3314_, v___x_3317_, v___x_3319_, v___x_3337_, v___x_3339_, v_a_3206_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v___x_3340_);
v___x_3342_ = v___x_3208_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3340_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
v___jp_3215_:
{
lean_object* v_toCold_3217_; lean_object* v_ref_3218_; lean_object* v_quotContext_3219_; lean_object* v_currMacroScope_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3225_; 
v_toCold_3217_ = lean_ctor_get(v___y_3196_, 0);
v_ref_3218_ = lean_ctor_get(v___y_3196_, 2);
v_quotContext_3219_ = lean_ctor_get(v_toCold_3217_, 8);
v_currMacroScope_3220_ = lean_ctor_get(v_toCold_3217_, 9);
v___x_3221_ = l_Lean_SourceInfo_fromRef(v_ref_3218_, v___y_3216_);
v___x_3222_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_3223_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1));
lean_inc(v___x_3221_);
if (v_isShared_3214_ == 0)
{
lean_ctor_set_tag(v___x_3213_, 2);
lean_ctor_set(v___x_3213_, 1, v___x_3222_);
lean_ctor_set(v___x_3213_, 0, v___x_3221_);
v___x_3225_ = v___x_3213_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3221_);
lean_ctor_set(v_reuseFailAlloc_3266_, 1, v___x_3222_);
v___x_3225_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; size_t v_sz_3253_; size_t v___x_3254_; lean_object* v___x_3255_; 
v___x_3226_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_3227_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3228_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3229_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
lean_inc_n(v___x_3221_, 11);
v___x_3230_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3221_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
v___x_3231_ = l_String_toRawSubstring_x27(v___x_3181_);
lean_inc_n(v_currMacroScope_3220_, 2);
lean_inc_n(v_quotContext_3219_, 2);
v___x_3232_ = l_Lean_addMacroScope(v_quotContext_3219_, v___x_3182_, v_currMacroScope_3220_);
v___x_3233_ = lean_box(0);
v___x_3234_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3221_);
lean_ctor_set(v___x_3234_, 1, v___x_3231_);
lean_ctor_set(v___x_3234_, 2, v___x_3232_);
lean_ctor_set(v___x_3234_, 3, v___x_3233_);
v___x_3235_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3236_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3221_);
lean_ctor_set(v___x_3236_, 1, v___x_3235_);
v___x_3237_ = l_String_toRawSubstring_x27(v___x_3183_);
v___x_3238_ = l_Lean_addMacroScope(v_quotContext_3219_, v___x_3184_, v_currMacroScope_3220_);
v___x_3239_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3221_);
lean_ctor_set(v___x_3239_, 1, v___x_3237_);
lean_ctor_set(v___x_3239_, 2, v___x_3238_);
lean_ctor_set(v___x_3239_, 3, v___x_3233_);
v___x_3240_ = l_Lean_Syntax_node3(v___x_3221_, v___x_3227_, v___x_3234_, v___x_3236_, v___x_3239_);
v___x_3241_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3242_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3221_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = l_Lean_Syntax_node3(v___x_3221_, v___x_3228_, v___x_3230_, v___x_3240_, v___x_3242_);
v___x_3244_ = l_Lean_Syntax_node1(v___x_3221_, v___x_3227_, v___x_3243_);
v___x_3245_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3246_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3221_);
lean_ctor_set(v___x_3246_, 1, v___x_3227_);
lean_ctor_set(v___x_3246_, 2, v___x_3245_);
v___x_3247_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3248_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3221_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = l_Lean_Syntax_node4(v___x_3221_, v___x_3226_, v___x_3244_, v___x_3246_, v___x_3248_, v_a_3206_);
v___x_3250_ = l_Lean_Syntax_node2(v___x_3221_, v___x_3223_, v___x_3225_, v___x_3249_);
v___x_3251_ = lean_mk_empty_array_with_capacity(v___x_3185_);
v___x_3252_ = lean_array_push(v___x_3251_, v___x_3250_);
v_sz_3253_ = lean_array_size(v_points_3210_);
v___x_3254_ = ((size_t)0ULL);
v___x_3255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_points_3210_, v_sz_3253_, v___x_3254_, v___x_3252_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
lean_dec_ref(v_points_3210_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_a_3256_; lean_object* v___x_3257_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_a_3256_);
lean_dec_ref_known(v___x_3255_, 1);
v___x_3257_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3256_, v_default_3211_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
lean_dec(v_a_3256_);
return v___x_3257_;
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec(v_default_3211_);
v_a_3258_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3255_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3255_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
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
lean_dec_ref(v___x_3188_);
lean_dec_ref(v___x_3187_);
lean_dec(v___x_3184_);
lean_dec_ref(v___x_3183_);
lean_dec(v___x_3182_);
lean_dec_ref(v___x_3181_);
lean_dec_ref(v_snd_3180_);
return v___x_3205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed(lean_object** _args){
lean_object* v_xs_3346_ = _args[0];
lean_object* v_fst_3347_ = _args[1];
lean_object* v_snd_3348_ = _args[2];
lean_object* v___x_3349_ = _args[3];
lean_object* v___x_3350_ = _args[4];
lean_object* v___x_3351_ = _args[5];
lean_object* v___x_3352_ = _args[6];
lean_object* v___x_3353_ = _args[7];
lean_object* v___x_3354_ = _args[8];
lean_object* v___x_3355_ = _args[9];
lean_object* v___x_3356_ = _args[10];
lean_object* v_letMuts_3357_ = _args[11];
lean_object* v___y_3358_ = _args[12];
lean_object* v___y_3359_ = _args[13];
lean_object* v___y_3360_ = _args[14];
lean_object* v___y_3361_ = _args[15];
lean_object* v___y_3362_ = _args[16];
lean_object* v___y_3363_ = _args[17];
lean_object* v___y_3364_ = _args[18];
lean_object* v___y_3365_ = _args[19];
lean_object* v___y_3366_ = _args[20];
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(v_xs_3346_, v_fst_3347_, v_snd_3348_, v___x_3349_, v___x_3350_, v___x_3351_, v___x_3352_, v___x_3353_, v___x_3354_, v___x_3355_, v___x_3356_, v_letMuts_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___x_3354_);
lean_dec(v___x_3353_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(lean_object* v_fst_3368_, lean_object* v_snd_3369_, lean_object* v___x_3370_, lean_object* v___x_3371_, lean_object* v___x_3372_, lean_object* v___x_3373_, lean_object* v___x_3374_, lean_object* v___x_3375_, lean_object* v_arg_3376_, lean_object* v_xs_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___f_3389_; lean_object* v___x_3390_; 
v___x_3387_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3388_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___f_3389_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed), 21, 11);
lean_closure_set(v___f_3389_, 0, v_xs_3377_);
lean_closure_set(v___f_3389_, 1, v_fst_3368_);
lean_closure_set(v___f_3389_, 2, v_snd_3369_);
lean_closure_set(v___f_3389_, 3, v___x_3370_);
lean_closure_set(v___f_3389_, 4, v___x_3371_);
lean_closure_set(v___f_3389_, 5, v___x_3387_);
lean_closure_set(v___f_3389_, 6, v___x_3388_);
lean_closure_set(v___f_3389_, 7, v___x_3372_);
lean_closure_set(v___f_3389_, 8, v___x_3373_);
lean_closure_set(v___f_3389_, 9, v___x_3374_);
lean_closure_set(v___f_3389_, 10, v___x_3375_);
v___x_3390_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3388_, v_arg_3376_, v___f_3389_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed(lean_object** _args){
lean_object* v_fst_3391_ = _args[0];
lean_object* v_snd_3392_ = _args[1];
lean_object* v___x_3393_ = _args[2];
lean_object* v___x_3394_ = _args[3];
lean_object* v___x_3395_ = _args[4];
lean_object* v___x_3396_ = _args[5];
lean_object* v___x_3397_ = _args[6];
lean_object* v___x_3398_ = _args[7];
lean_object* v_arg_3399_ = _args[8];
lean_object* v_xs_3400_ = _args[9];
lean_object* v___y_3401_ = _args[10];
lean_object* v___y_3402_ = _args[11];
lean_object* v___y_3403_ = _args[12];
lean_object* v___y_3404_ = _args[13];
lean_object* v___y_3405_ = _args[14];
lean_object* v___y_3406_ = _args[15];
lean_object* v___y_3407_ = _args[16];
lean_object* v___y_3408_ = _args[17];
lean_object* v___y_3409_ = _args[18];
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(v_fst_3391_, v_snd_3392_, v___x_3393_, v___x_3394_, v___x_3395_, v___x_3396_, v___x_3397_, v___x_3398_, v_arg_3399_, v_xs_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(lean_object* v_as_3411_, size_t v_sz_3412_, size_t v_i_3413_, lean_object* v_b_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
uint8_t v___x_3420_; 
v___x_3420_ = lean_usize_dec_lt(v_i_3413_, v_sz_3412_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; 
v___x_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3421_, 0, v_b_3414_);
return v___x_3421_;
}
else
{
lean_object* v_a_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v_a_3422_ = lean_array_uget_borrowed(v_as_3411_, v_i_3413_);
v___x_3423_ = lean_box(1);
lean_inc(v_a_3422_);
v___x_3424_ = l_Lean_PrettyPrinter_delab(v_a_3422_, v___x_3423_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; lean_object* v___x_3426_; size_t v___x_3427_; size_t v___x_3428_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref_known(v___x_3424_, 1);
v___x_3426_ = lean_array_push(v_b_3414_, v_a_3425_);
v___x_3427_ = ((size_t)1ULL);
v___x_3428_ = lean_usize_add(v_i_3413_, v___x_3427_);
v_i_3413_ = v___x_3428_;
v_b_3414_ = v___x_3426_;
goto _start;
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec_ref(v_b_3414_);
v_a_3430_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3424_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3424_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg___boxed(lean_object* v_as_3438_, lean_object* v_sz_3439_, lean_object* v_i_3440_, lean_object* v_b_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
size_t v_sz_boxed_3447_; size_t v_i_boxed_3448_; lean_object* v_res_3449_; 
v_sz_boxed_3447_ = lean_unbox_usize(v_sz_3439_);
lean_dec(v_sz_3439_);
v_i_boxed_3448_ = lean_unbox_usize(v_i_3440_);
lean_dec(v_i_3440_);
v_res_3449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_3438_, v_sz_boxed_3447_, v_i_boxed_3448_, v_b_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec_ref(v_as_3438_);
return v_res_3449_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3(void){
_start:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3457_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__2));
v___x_3458_ = l_String_toRawSubstring_x27(v___x_3457_);
return v___x_3458_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9(void){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__8));
v___x_3469_ = l_String_toRawSubstring_x27(v___x_3468_);
return v___x_3469_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12(void){
_start:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3473_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__0));
v___x_3474_ = l_String_toRawSubstring_x27(v___x_3473_);
return v___x_3474_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13(void){
_start:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3475_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3476_ = l_String_toRawSubstring_x27(v___x_3475_);
return v___x_3476_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16(void){
_start:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3479_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__15));
v___x_3480_ = l_String_toRawSubstring_x27(v___x_3479_);
return v___x_3480_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19(void){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3484_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__18));
v___x_3485_ = l_String_toRawSubstring_x27(v___x_3484_);
return v___x_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(lean_object* v___x_3495_, lean_object* v___x_3496_, lean_object* v___f_3497_, lean_object* v_a_3498_, lean_object* v_inv_3499_, lean_object* v_arg_3500_, lean_object* v___x_3501_, uint8_t v___x_3502_, lean_object* v___x_3503_, lean_object* v___x_3504_, lean_object* v___x_3505_, lean_object* v___x_3506_, lean_object* v___x_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v_a_3518_; lean_object* v___x_3521_; 
lean_inc_ref(v___x_3496_);
lean_inc(v___x_3495_);
v___x_3521_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3495_, v___x_3496_, v___f_3497_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; lean_object* v___x_3523_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3522_);
lean_dec_ref_known(v___x_3521_, 1);
v___x_3523_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(v_a_3498_, v_inv_3499_, v_arg_3500_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3524_);
lean_dec_ref_known(v___x_3523_, 1);
if (lean_obj_tag(v_a_3524_) == 1)
{
lean_object* v_val_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_4010_; 
lean_dec_ref(v_arg_3500_);
v_val_3525_ = lean_ctor_get(v_a_3524_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v_a_3524_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_3527_ = v_a_3524_;
v_isShared_3528_ = v_isSharedCheck_4010_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_val_3525_);
lean_dec(v_a_3524_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_4010_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
if (lean_obj_tag(v_a_3522_) == 1)
{
lean_object* v_val_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3932_; 
lean_del_object(v___x_3527_);
v_val_3529_ = lean_ctor_get(v_a_3522_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v_a_3522_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3531_ = v_a_3522_;
v_isShared_3532_ = v_isSharedCheck_3932_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_val_3529_);
lean_dec(v_a_3522_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3932_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v_snd_3533_; lean_object* v_fst_3534_; lean_object* v_snd_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3931_; 
v_snd_3533_ = lean_ctor_get(v_val_3529_, 1);
lean_inc(v_snd_3533_);
v_fst_3534_ = lean_ctor_get(v_val_3525_, 0);
v_snd_3535_ = lean_ctor_get(v_val_3525_, 1);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_val_3525_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3537_ = v_val_3525_;
v_isShared_3538_ = v_isSharedCheck_3931_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_snd_3535_);
lean_inc(v_fst_3534_);
lean_dec(v_val_3525_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3931_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v_fst_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3929_; 
v_fst_3539_ = lean_ctor_get(v_val_3529_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v_val_3529_);
if (v_isSharedCheck_3929_ == 0)
{
lean_object* v_unused_3930_; 
v_unused_3930_ = lean_ctor_get(v_val_3529_, 1);
lean_dec(v_unused_3930_);
v___x_3541_ = v_val_3529_;
v_isShared_3542_ = v_isSharedCheck_3929_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_fst_3539_);
lean_dec(v_val_3529_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3929_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v_fst_3543_; lean_object* v_snd_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3928_; 
v_fst_3543_ = lean_ctor_get(v_snd_3533_, 0);
v_snd_3544_ = lean_ctor_get(v_snd_3533_, 1);
v_isSharedCheck_3928_ = !lean_is_exclusive(v_snd_3533_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3546_ = v_snd_3533_;
v_isShared_3547_ = v_isSharedCheck_3928_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_snd_3544_);
lean_inc(v_fst_3543_);
lean_dec(v_snd_3533_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3928_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3548_; lean_object* v___f_3549_; lean_object* v___x_3550_; 
v___x_3548_ = lean_box(v___x_3502_);
lean_inc(v___x_3503_);
v___f_3549_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed), 17, 7);
lean_closure_set(v___f_3549_, 0, v_fst_3534_);
lean_closure_set(v___f_3549_, 1, v_fst_3539_);
lean_closure_set(v___f_3549_, 2, v___x_3501_);
lean_closure_set(v___f_3549_, 3, v_fst_3543_);
lean_closure_set(v___f_3549_, 4, v___x_3548_);
lean_closure_set(v___f_3549_, 5, v___x_3503_);
lean_closure_set(v___f_3549_, 6, v_snd_3535_);
lean_inc(v___x_3495_);
v___x_3550_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3495_, v___x_3496_, v___f_3549_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v_fst_3552_; lean_object* v_snd_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3919_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3551_);
lean_dec_ref_known(v___x_3550_, 1);
v_fst_3552_ = lean_ctor_get(v_a_3551_, 0);
v_snd_3553_ = lean_ctor_get(v_a_3551_, 1);
v_isSharedCheck_3919_ = !lean_is_exclusive(v_a_3551_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3555_ = v_a_3551_;
v_isShared_3556_ = v_isSharedCheck_3919_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_snd_3553_);
lean_inc(v_fst_3552_);
lean_dec(v_a_3551_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3919_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v_points_3557_; lean_object* v_default_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3918_; 
v_points_3557_ = lean_ctor_get(v_snd_3544_, 0);
v_default_3558_ = lean_ctor_get(v_snd_3544_, 1);
v_isSharedCheck_3918_ = !lean_is_exclusive(v_snd_3544_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3560_ = v_snd_3544_;
v_isShared_3561_ = v_isSharedCheck_3918_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_default_3558_);
lean_inc(v_points_3557_);
lean_dec(v_snd_3544_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3918_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3562_; uint8_t v___x_3563_; 
v___x_3562_ = lean_array_get_size(v_points_3557_);
v___x_3563_ = lean_nat_dec_eq(v___x_3562_, v___x_3503_);
if (v___x_3563_ == 0)
{
lean_object* v___x_3564_; size_t v_sz_3565_; size_t v___x_3566_; lean_object* v___x_3567_; 
lean_del_object(v___x_3531_);
v___x_3564_ = lean_mk_empty_array_with_capacity(v___x_3503_);
lean_dec(v___x_3503_);
v_sz_3565_ = lean_array_size(v_points_3557_);
v___x_3566_ = ((size_t)0ULL);
v___x_3567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_points_3557_, v_sz_3565_, v___x_3566_, v___x_3564_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
lean_dec_ref(v_points_3557_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3569_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_a_3568_);
lean_dec_ref_known(v___x_3567_, 1);
v___x_3569_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3568_, v_default_3558_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
lean_dec(v_a_3568_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v_toCold_3570_; lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3653_; 
v_toCold_3570_ = lean_ctor_get(v___y_3514_, 0);
lean_inc_ref(v_toCold_3570_);
v_a_3571_ = lean_ctor_get(v___x_3569_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3573_ = v___x_3569_;
v_isShared_3574_ = v_isSharedCheck_3653_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3569_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3653_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v_ref_3575_; lean_object* v_quotContext_3576_; lean_object* v_currMacroScope_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3587_; 
v_ref_3575_ = lean_ctor_get(v___y_3514_, 2);
lean_inc(v_ref_3575_);
lean_dec_ref(v___y_3514_);
v_quotContext_3576_ = lean_ctor_get(v_toCold_3570_, 8);
lean_inc_n(v_quotContext_3576_, 2);
v_currMacroScope_3577_ = lean_ctor_get(v_toCold_3570_, 9);
lean_inc_n(v_currMacroScope_3577_, 2);
lean_dec_ref(v_toCold_3570_);
v___x_3578_ = l_Lean_SourceInfo_fromRef(v_ref_3575_, v___x_3563_);
lean_dec(v_ref_3575_);
v___x_3579_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3580_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3581_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3504_);
v___x_3582_ = l_Lean_Name_mkStr2(v___x_3504_, v___x_3581_);
v___x_3583_ = l_Lean_addMacroScope(v_quotContext_3576_, v___x_3582_, v_currMacroScope_3577_);
v___x_3584_ = l_Lean_Name_mkStr4(v___x_3505_, v___x_3506_, v___x_3504_, v___x_3581_);
v___x_3585_ = lean_box(0);
lean_inc(v___x_3584_);
if (v_isShared_3561_ == 0)
{
lean_ctor_set_tag(v___x_3560_, 1);
lean_ctor_set(v___x_3560_, 1, v___x_3585_);
lean_ctor_set(v___x_3560_, 0, v___x_3584_);
v___x_3587_ = v___x_3560_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3584_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v___x_3585_);
v___x_3587_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
lean_object* v___x_3589_; 
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v___x_3584_);
v___x_3589_ = v___x_3573_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3584_);
v___x_3589_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3591_; 
if (v_isShared_3556_ == 0)
{
lean_ctor_set_tag(v___x_3555_, 1);
lean_ctor_set(v___x_3555_, 1, v___x_3585_);
lean_ctor_set(v___x_3555_, 0, v___x_3589_);
v___x_3591_ = v___x_3555_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3589_);
lean_ctor_set(v_reuseFailAlloc_3650_, 1, v___x_3585_);
v___x_3591_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
lean_object* v___x_3593_; 
if (v_isShared_3547_ == 0)
{
lean_ctor_set_tag(v___x_3546_, 1);
lean_ctor_set(v___x_3546_, 1, v___x_3591_);
lean_ctor_set(v___x_3546_, 0, v___x_3587_);
v___x_3593_ = v___x_3546_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v___x_3587_);
lean_ctor_set(v_reuseFailAlloc_3649_, 1, v___x_3591_);
v___x_3593_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3599_; 
lean_inc_n(v___x_3578_, 2);
v___x_3594_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3578_);
lean_ctor_set(v___x_3594_, 1, v___x_3580_);
lean_ctor_set(v___x_3594_, 2, v___x_3583_);
lean_ctor_set(v___x_3594_, 3, v___x_3593_);
v___x_3595_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3596_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3597_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3542_ == 0)
{
lean_ctor_set_tag(v___x_3541_, 2);
lean_ctor_set(v___x_3541_, 1, v___x_3597_);
lean_ctor_set(v___x_3541_, 0, v___x_3578_);
v___x_3599_ = v___x_3541_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3578_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v___x_3597_);
v___x_3599_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3606_; 
v___x_3600_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3601_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3577_);
lean_inc(v_quotContext_3576_);
v___x_3602_ = l_Lean_addMacroScope(v_quotContext_3576_, v___x_3601_, v_currMacroScope_3577_);
lean_inc_n(v___x_3578_, 2);
v___x_3603_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3578_);
lean_ctor_set(v___x_3603_, 1, v___x_3600_);
lean_ctor_set(v___x_3603_, 2, v___x_3602_);
lean_ctor_set(v___x_3603_, 3, v___x_3585_);
v___x_3604_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3538_ == 0)
{
lean_ctor_set_tag(v___x_3537_, 2);
lean_ctor_set(v___x_3537_, 1, v___x_3604_);
lean_ctor_set(v___x_3537_, 0, v___x_3578_);
v___x_3606_ = v___x_3537_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3578_);
lean_ctor_set(v_reuseFailAlloc_3647_, 1, v___x_3604_);
v___x_3606_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3607_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_3608_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1));
lean_inc_n(v___x_3578_, 19);
v___x_3609_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3578_);
lean_ctor_set(v___x_3609_, 1, v___x_3607_);
v___x_3610_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_3611_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3612_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3577_, 4);
lean_inc_n(v_quotContext_3576_, 4);
v___x_3613_ = l_Lean_addMacroScope(v_quotContext_3576_, v___x_3612_, v_currMacroScope_3577_);
v___x_3614_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3578_);
lean_ctor_set(v___x_3614_, 1, v___x_3611_);
lean_ctor_set(v___x_3614_, 2, v___x_3613_);
lean_ctor_set(v___x_3614_, 3, v___x_3585_);
v___x_3615_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3616_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3617_ = l_Lean_addMacroScope(v_quotContext_3576_, v___x_3616_, v_currMacroScope_3577_);
v___x_3618_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3578_);
lean_ctor_set(v___x_3618_, 1, v___x_3615_);
lean_ctor_set(v___x_3618_, 2, v___x_3617_);
lean_ctor_set(v___x_3618_, 3, v___x_3585_);
lean_inc_ref(v___x_3618_);
v___x_3619_ = l_Lean_Syntax_node2(v___x_3578_, v___x_3595_, v___x_3614_, v___x_3618_);
v___x_3620_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3621_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3578_);
lean_ctor_set(v___x_3621_, 1, v___x_3595_);
lean_ctor_set(v___x_3621_, 2, v___x_3620_);
v___x_3622_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3623_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3578_);
lean_ctor_set(v___x_3623_, 1, v___x_3622_);
lean_inc_ref(v___x_3623_);
lean_inc_ref(v___x_3621_);
v___x_3624_ = l_Lean_Syntax_node4(v___x_3578_, v___x_3610_, v___x_3619_, v___x_3621_, v___x_3623_, v_snd_3553_);
lean_inc_ref(v___x_3609_);
v___x_3625_ = l_Lean_Syntax_node2(v___x_3578_, v___x_3608_, v___x_3609_, v___x_3624_);
v___x_3626_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3627_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3578_);
lean_ctor_set(v___x_3627_, 1, v___x_3626_);
lean_inc_ref_n(v___x_3627_, 2);
lean_inc_ref_n(v___x_3606_, 2);
lean_inc_ref_n(v___x_3599_, 2);
v___x_3628_ = l_Lean_Syntax_node5(v___x_3578_, v___x_3596_, v___x_3599_, v___x_3603_, v___x_3606_, v___x_3625_, v___x_3627_);
v___x_3629_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3630_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3631_ = l_Lean_addMacroScope(v_quotContext_3576_, v___x_3630_, v_currMacroScope_3577_);
v___x_3632_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3578_);
lean_ctor_set(v___x_3632_, 1, v___x_3629_);
lean_ctor_set(v___x_3632_, 2, v___x_3631_);
lean_ctor_set(v___x_3632_, 3, v___x_3585_);
v___x_3633_ = l_String_toRawSubstring_x27(v___x_3507_);
v___x_3634_ = l_Lean_addMacroScope(v_quotContext_3576_, v___x_3495_, v_currMacroScope_3577_);
v___x_3635_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3578_);
lean_ctor_set(v___x_3635_, 1, v___x_3633_);
lean_ctor_set(v___x_3635_, 2, v___x_3634_);
lean_ctor_set(v___x_3635_, 3, v___x_3585_);
v___x_3636_ = l_Lean_Syntax_node2(v___x_3578_, v___x_3595_, v___x_3635_, v___x_3618_);
v___x_3637_ = l_Lean_Syntax_node4(v___x_3578_, v___x_3610_, v___x_3636_, v___x_3621_, v___x_3623_, v_fst_3552_);
v___x_3638_ = l_Lean_Syntax_node2(v___x_3578_, v___x_3608_, v___x_3609_, v___x_3637_);
v___x_3639_ = l_Lean_Syntax_node5(v___x_3578_, v___x_3596_, v___x_3599_, v___x_3632_, v___x_3606_, v___x_3638_, v___x_3627_);
v___x_3640_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3641_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3642_ = l_Lean_addMacroScope(v_quotContext_3576_, v___x_3641_, v_currMacroScope_3577_);
v___x_3643_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3578_);
lean_ctor_set(v___x_3643_, 1, v___x_3640_);
lean_ctor_set(v___x_3643_, 2, v___x_3642_);
lean_ctor_set(v___x_3643_, 3, v___x_3585_);
v___x_3644_ = l_Lean_Syntax_node5(v___x_3578_, v___x_3596_, v___x_3599_, v___x_3643_, v___x_3606_, v_a_3571_, v___x_3627_);
v___x_3645_ = l_Lean_Syntax_node3(v___x_3578_, v___x_3595_, v___x_3628_, v___x_3639_, v___x_3644_);
v___x_3646_ = l_Lean_Syntax_node2(v___x_3578_, v___x_3579_, v___x_3594_, v___x_3645_);
v_a_3518_ = v___x_3646_;
goto v___jp_3517_;
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
lean_del_object(v___x_3560_);
lean_del_object(v___x_3555_);
lean_dec(v_snd_3553_);
lean_dec(v_fst_3552_);
lean_del_object(v___x_3546_);
lean_del_object(v___x_3541_);
lean_del_object(v___x_3537_);
lean_dec_ref(v___y_3514_);
lean_dec_ref(v___x_3507_);
lean_dec_ref(v___x_3506_);
lean_dec_ref(v___x_3505_);
lean_dec_ref(v___x_3504_);
lean_dec(v___x_3495_);
return v___x_3569_;
}
}
else
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3661_; 
lean_del_object(v___x_3560_);
lean_dec(v_default_3558_);
lean_del_object(v___x_3555_);
lean_dec(v_snd_3553_);
lean_dec(v_fst_3552_);
lean_del_object(v___x_3546_);
lean_del_object(v___x_3541_);
lean_del_object(v___x_3537_);
lean_dec_ref(v___y_3514_);
lean_dec_ref(v___x_3507_);
lean_dec_ref(v___x_3506_);
lean_dec_ref(v___x_3505_);
lean_dec_ref(v___x_3504_);
lean_dec(v___x_3495_);
v_a_3654_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3656_ = v___x_3567_;
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3567_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3659_; 
if (v_isShared_3657_ == 0)
{
v___x_3659_ = v___x_3656_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
}
else
{
lean_dec_ref(v_points_3557_);
lean_dec(v___x_3503_);
switch(lean_obj_tag(v_default_3558_))
{
case 2:
{
lean_object* v_toCold_3662_; lean_object* v_ref_3663_; lean_object* v_quotContext_3664_; lean_object* v_currMacroScope_3665_; uint8_t v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3676_; 
v_toCold_3662_ = lean_ctor_get(v___y_3514_, 0);
lean_inc_ref(v_toCold_3662_);
v_ref_3663_ = lean_ctor_get(v___y_3514_, 2);
lean_inc(v_ref_3663_);
lean_dec_ref(v___y_3514_);
v_quotContext_3664_ = lean_ctor_get(v_toCold_3662_, 8);
lean_inc_n(v_quotContext_3664_, 2);
v_currMacroScope_3665_ = lean_ctor_get(v_toCold_3662_, 9);
lean_inc_n(v_currMacroScope_3665_, 2);
lean_dec_ref(v_toCold_3662_);
v___x_3666_ = 0;
v___x_3667_ = l_Lean_SourceInfo_fromRef(v_ref_3663_, v___x_3666_);
lean_dec(v_ref_3663_);
v___x_3668_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3669_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3670_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3504_);
v___x_3671_ = l_Lean_Name_mkStr2(v___x_3504_, v___x_3670_);
v___x_3672_ = l_Lean_addMacroScope(v_quotContext_3664_, v___x_3671_, v_currMacroScope_3665_);
lean_inc_ref(v___x_3506_);
lean_inc_ref(v___x_3505_);
v___x_3673_ = l_Lean_Name_mkStr4(v___x_3505_, v___x_3506_, v___x_3504_, v___x_3670_);
v___x_3674_ = lean_box(0);
lean_inc(v___x_3673_);
if (v_isShared_3561_ == 0)
{
lean_ctor_set_tag(v___x_3560_, 1);
lean_ctor_set(v___x_3560_, 1, v___x_3674_);
lean_ctor_set(v___x_3560_, 0, v___x_3673_);
v___x_3676_ = v___x_3560_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3752_, 1, v___x_3674_);
v___x_3676_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3678_; 
if (v_isShared_3532_ == 0)
{
lean_ctor_set_tag(v___x_3531_, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3673_);
v___x_3678_ = v___x_3531_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v___x_3673_);
v___x_3678_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
lean_object* v___x_3680_; 
if (v_isShared_3556_ == 0)
{
lean_ctor_set_tag(v___x_3555_, 1);
lean_ctor_set(v___x_3555_, 1, v___x_3674_);
lean_ctor_set(v___x_3555_, 0, v___x_3678_);
v___x_3680_ = v___x_3555_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3678_);
lean_ctor_set(v_reuseFailAlloc_3750_, 1, v___x_3674_);
v___x_3680_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
lean_object* v___x_3682_; 
if (v_isShared_3547_ == 0)
{
lean_ctor_set_tag(v___x_3546_, 1);
lean_ctor_set(v___x_3546_, 1, v___x_3680_);
lean_ctor_set(v___x_3546_, 0, v___x_3676_);
v___x_3682_ = v___x_3546_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v___x_3676_);
lean_ctor_set(v_reuseFailAlloc_3749_, 1, v___x_3680_);
v___x_3682_ = v_reuseFailAlloc_3749_;
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
if (v_isShared_3542_ == 0)
{
lean_ctor_set_tag(v___x_3541_, 2);
lean_ctor_set(v___x_3541_, 1, v___x_3686_);
lean_ctor_set(v___x_3541_, 0, v___x_3667_);
v___x_3688_ = v___x_3541_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v___x_3686_);
v___x_3688_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3695_; 
v___x_3689_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3690_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3665_);
lean_inc(v_quotContext_3664_);
v___x_3691_ = l_Lean_addMacroScope(v_quotContext_3664_, v___x_3690_, v_currMacroScope_3665_);
lean_inc_n(v___x_3667_, 2);
v___x_3692_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3667_);
lean_ctor_set(v___x_3692_, 1, v___x_3689_);
lean_ctor_set(v___x_3692_, 2, v___x_3691_);
lean_ctor_set(v___x_3692_, 3, v___x_3674_);
v___x_3693_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3538_ == 0)
{
lean_ctor_set_tag(v___x_3537_, 2);
lean_ctor_set(v___x_3537_, 1, v___x_3693_);
lean_ctor_set(v___x_3537_, 0, v___x_3667_);
v___x_3695_ = v___x_3537_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3747_, 1, v___x_3693_);
v___x_3695_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
v___x_3696_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_3697_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1));
lean_inc_n(v___x_3667_, 22);
v___x_3698_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3667_);
lean_ctor_set(v___x_3698_, 1, v___x_3696_);
v___x_3699_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_3700_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3701_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3665_, 5);
lean_inc_n(v_quotContext_3664_, 5);
v___x_3702_ = l_Lean_addMacroScope(v_quotContext_3664_, v___x_3701_, v_currMacroScope_3665_);
v___x_3703_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3667_);
lean_ctor_set(v___x_3703_, 1, v___x_3700_);
lean_ctor_set(v___x_3703_, 2, v___x_3702_);
lean_ctor_set(v___x_3703_, 3, v___x_3674_);
v___x_3704_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3705_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3706_ = l_Lean_addMacroScope(v_quotContext_3664_, v___x_3705_, v_currMacroScope_3665_);
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
v___x_3713_ = l_Lean_Syntax_node4(v___x_3667_, v___x_3699_, v___x_3708_, v___x_3710_, v___x_3712_, v_snd_3553_);
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
v___x_3720_ = l_Lean_addMacroScope(v_quotContext_3664_, v___x_3719_, v_currMacroScope_3665_);
v___x_3721_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3667_);
lean_ctor_set(v___x_3721_, 1, v___x_3718_);
lean_ctor_set(v___x_3721_, 2, v___x_3720_);
lean_ctor_set(v___x_3721_, 3, v___x_3674_);
v___x_3722_ = l_String_toRawSubstring_x27(v___x_3507_);
v___x_3723_ = l_Lean_addMacroScope(v_quotContext_3664_, v___x_3495_, v_currMacroScope_3665_);
v___x_3724_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3667_);
lean_ctor_set(v___x_3724_, 1, v___x_3722_);
lean_ctor_set(v___x_3724_, 2, v___x_3723_);
lean_ctor_set(v___x_3724_, 3, v___x_3674_);
v___x_3725_ = l_Lean_Syntax_node2(v___x_3667_, v___x_3684_, v___x_3724_, v___x_3707_);
v___x_3726_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3727_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3728_ = l_Lean_addMacroScope(v_quotContext_3664_, v___x_3727_, v_currMacroScope_3665_);
v___x_3729_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3667_);
lean_ctor_set(v___x_3729_, 1, v___x_3726_);
lean_ctor_set(v___x_3729_, 2, v___x_3728_);
lean_ctor_set(v___x_3729_, 3, v___x_3674_);
v___x_3730_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29);
v___x_3731_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__0));
v___x_3732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__7));
v___x_3733_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30));
v___x_3734_ = l_Lean_addMacroScope(v_quotContext_3664_, v___x_3733_, v_currMacroScope_3665_);
v___x_3735_ = l_Lean_Name_mkStr4(v___x_3505_, v___x_3506_, v___x_3731_, v___x_3732_);
v___x_3736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3735_);
lean_ctor_set(v___x_3736_, 1, v___x_3674_);
v___x_3737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
lean_ctor_set(v___x_3737_, 1, v___x_3674_);
v___x_3738_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3667_);
lean_ctor_set(v___x_3738_, 1, v___x_3730_);
lean_ctor_set(v___x_3738_, 2, v___x_3734_);
lean_ctor_set(v___x_3738_, 3, v___x_3737_);
v___x_3739_ = l_Lean_Syntax_node5(v___x_3667_, v___x_3685_, v___x_3688_, v___x_3729_, v___x_3695_, v___x_3738_, v___x_3716_);
v___x_3740_ = l_Lean_Syntax_node1(v___x_3667_, v___x_3684_, v___x_3739_);
v___x_3741_ = l_Lean_Syntax_node2(v___x_3667_, v___x_3668_, v_fst_3552_, v___x_3740_);
v___x_3742_ = l_Lean_Syntax_node4(v___x_3667_, v___x_3699_, v___x_3725_, v___x_3710_, v___x_3712_, v___x_3741_);
v___x_3743_ = l_Lean_Syntax_node2(v___x_3667_, v___x_3697_, v___x_3698_, v___x_3742_);
v___x_3744_ = l_Lean_Syntax_node5(v___x_3667_, v___x_3685_, v___x_3688_, v___x_3721_, v___x_3695_, v___x_3743_, v___x_3716_);
v___x_3745_ = l_Lean_Syntax_node2(v___x_3667_, v___x_3684_, v___x_3717_, v___x_3744_);
v___x_3746_ = l_Lean_Syntax_node2(v___x_3667_, v___x_3668_, v___x_3683_, v___x_3745_);
v_a_3518_ = v___x_3746_;
goto v___jp_3517_;
}
}
}
}
}
}
}
case 3:
{
lean_object* v_e_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
lean_del_object(v___x_3531_);
v_e_3753_ = lean_ctor_get(v_default_3558_, 0);
lean_inc_ref(v_e_3753_);
lean_dec_ref_known(v_default_3558_, 1);
v___x_3754_ = lean_box(1);
v___x_3755_ = l_Lean_PrettyPrinter_delab(v_e_3753_, v___x_3754_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_toCold_3756_; lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3842_; 
v_toCold_3756_ = lean_ctor_get(v___y_3514_, 0);
lean_inc_ref(v_toCold_3756_);
v_a_3757_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3759_ = v___x_3755_;
v_isShared_3760_ = v_isSharedCheck_3842_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3755_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3842_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v_ref_3761_; lean_object* v_quotContext_3762_; lean_object* v_currMacroScope_3763_; uint8_t v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3774_; 
v_ref_3761_ = lean_ctor_get(v___y_3514_, 2);
lean_inc(v_ref_3761_);
lean_dec_ref(v___y_3514_);
v_quotContext_3762_ = lean_ctor_get(v_toCold_3756_, 8);
lean_inc_n(v_quotContext_3762_, 2);
v_currMacroScope_3763_ = lean_ctor_get(v_toCold_3756_, 9);
lean_inc_n(v_currMacroScope_3763_, 2);
lean_dec_ref(v_toCold_3756_);
v___x_3764_ = 0;
v___x_3765_ = l_Lean_SourceInfo_fromRef(v_ref_3761_, v___x_3764_);
lean_dec(v_ref_3761_);
v___x_3766_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3767_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3768_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3504_);
v___x_3769_ = l_Lean_Name_mkStr2(v___x_3504_, v___x_3768_);
v___x_3770_ = l_Lean_addMacroScope(v_quotContext_3762_, v___x_3769_, v_currMacroScope_3763_);
v___x_3771_ = l_Lean_Name_mkStr4(v___x_3505_, v___x_3506_, v___x_3504_, v___x_3768_);
v___x_3772_ = lean_box(0);
lean_inc(v___x_3771_);
if (v_isShared_3561_ == 0)
{
lean_ctor_set_tag(v___x_3560_, 1);
lean_ctor_set(v___x_3560_, 1, v___x_3772_);
lean_ctor_set(v___x_3560_, 0, v___x_3771_);
v___x_3774_ = v___x_3560_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v___x_3771_);
lean_ctor_set(v_reuseFailAlloc_3841_, 1, v___x_3772_);
v___x_3774_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
lean_object* v___x_3776_; 
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v___x_3771_);
v___x_3776_ = v___x_3759_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3771_);
v___x_3776_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
lean_object* v___x_3778_; 
if (v_isShared_3556_ == 0)
{
lean_ctor_set_tag(v___x_3555_, 1);
lean_ctor_set(v___x_3555_, 1, v___x_3772_);
lean_ctor_set(v___x_3555_, 0, v___x_3776_);
v___x_3778_ = v___x_3555_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3776_);
lean_ctor_set(v_reuseFailAlloc_3839_, 1, v___x_3772_);
v___x_3778_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
lean_object* v___x_3780_; 
if (v_isShared_3547_ == 0)
{
lean_ctor_set_tag(v___x_3546_, 1);
lean_ctor_set(v___x_3546_, 1, v___x_3778_);
lean_ctor_set(v___x_3546_, 0, v___x_3774_);
v___x_3780_ = v___x_3546_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v___x_3774_);
lean_ctor_set(v_reuseFailAlloc_3838_, 1, v___x_3778_);
v___x_3780_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3786_; 
lean_inc_n(v___x_3765_, 2);
v___x_3781_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3765_);
lean_ctor_set(v___x_3781_, 1, v___x_3767_);
lean_ctor_set(v___x_3781_, 2, v___x_3770_);
lean_ctor_set(v___x_3781_, 3, v___x_3780_);
v___x_3782_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3783_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3784_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3542_ == 0)
{
lean_ctor_set_tag(v___x_3541_, 2);
lean_ctor_set(v___x_3541_, 1, v___x_3784_);
lean_ctor_set(v___x_3541_, 0, v___x_3765_);
v___x_3786_ = v___x_3541_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___x_3765_);
lean_ctor_set(v_reuseFailAlloc_3837_, 1, v___x_3784_);
v___x_3786_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3793_; 
v___x_3787_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3788_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3763_);
lean_inc(v_quotContext_3762_);
v___x_3789_ = l_Lean_addMacroScope(v_quotContext_3762_, v___x_3788_, v_currMacroScope_3763_);
lean_inc_n(v___x_3765_, 2);
v___x_3790_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3765_);
lean_ctor_set(v___x_3790_, 1, v___x_3787_);
lean_ctor_set(v___x_3790_, 2, v___x_3789_);
lean_ctor_set(v___x_3790_, 3, v___x_3772_);
v___x_3791_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3538_ == 0)
{
lean_ctor_set_tag(v___x_3537_, 2);
lean_ctor_set(v___x_3537_, 1, v___x_3791_);
lean_ctor_set(v___x_3537_, 0, v___x_3765_);
v___x_3793_ = v___x_3537_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3765_);
lean_ctor_set(v_reuseFailAlloc_3836_, 1, v___x_3791_);
v___x_3793_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3794_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_3795_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1));
lean_inc_n(v___x_3765_, 21);
v___x_3796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3765_);
lean_ctor_set(v___x_3796_, 1, v___x_3794_);
v___x_3797_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_3798_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3799_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3763_, 4);
lean_inc_n(v_quotContext_3762_, 4);
v___x_3800_ = l_Lean_addMacroScope(v_quotContext_3762_, v___x_3799_, v_currMacroScope_3763_);
v___x_3801_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3765_);
lean_ctor_set(v___x_3801_, 1, v___x_3798_);
lean_ctor_set(v___x_3801_, 2, v___x_3800_);
lean_ctor_set(v___x_3801_, 3, v___x_3772_);
v___x_3802_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3803_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3804_ = l_Lean_addMacroScope(v_quotContext_3762_, v___x_3803_, v_currMacroScope_3763_);
v___x_3805_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3765_);
lean_ctor_set(v___x_3805_, 1, v___x_3802_);
lean_ctor_set(v___x_3805_, 2, v___x_3804_);
lean_ctor_set(v___x_3805_, 3, v___x_3772_);
lean_inc_ref(v___x_3805_);
v___x_3806_ = l_Lean_Syntax_node2(v___x_3765_, v___x_3782_, v___x_3801_, v___x_3805_);
v___x_3807_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3808_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3765_);
lean_ctor_set(v___x_3808_, 1, v___x_3782_);
lean_ctor_set(v___x_3808_, 2, v___x_3807_);
v___x_3809_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3810_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3765_);
lean_ctor_set(v___x_3810_, 1, v___x_3809_);
lean_inc_ref(v___x_3810_);
lean_inc_ref(v___x_3808_);
v___x_3811_ = l_Lean_Syntax_node4(v___x_3765_, v___x_3797_, v___x_3806_, v___x_3808_, v___x_3810_, v_snd_3553_);
lean_inc_ref(v___x_3796_);
v___x_3812_ = l_Lean_Syntax_node2(v___x_3765_, v___x_3795_, v___x_3796_, v___x_3811_);
v___x_3813_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3814_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3765_);
lean_ctor_set(v___x_3814_, 1, v___x_3813_);
lean_inc_ref_n(v___x_3814_, 2);
lean_inc_ref_n(v___x_3793_, 2);
lean_inc_ref_n(v___x_3786_, 2);
v___x_3815_ = l_Lean_Syntax_node5(v___x_3765_, v___x_3783_, v___x_3786_, v___x_3790_, v___x_3793_, v___x_3812_, v___x_3814_);
v___x_3816_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3817_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3818_ = l_Lean_addMacroScope(v_quotContext_3762_, v___x_3817_, v_currMacroScope_3763_);
v___x_3819_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3765_);
lean_ctor_set(v___x_3819_, 1, v___x_3816_);
lean_ctor_set(v___x_3819_, 2, v___x_3818_);
lean_ctor_set(v___x_3819_, 3, v___x_3772_);
v___x_3820_ = l_String_toRawSubstring_x27(v___x_3507_);
v___x_3821_ = l_Lean_addMacroScope(v_quotContext_3762_, v___x_3495_, v_currMacroScope_3763_);
v___x_3822_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3765_);
lean_ctor_set(v___x_3822_, 1, v___x_3820_);
lean_ctor_set(v___x_3822_, 2, v___x_3821_);
lean_ctor_set(v___x_3822_, 3, v___x_3772_);
v___x_3823_ = l_Lean_Syntax_node2(v___x_3765_, v___x_3782_, v___x_3822_, v___x_3805_);
v___x_3824_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3825_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3826_ = l_Lean_addMacroScope(v_quotContext_3762_, v___x_3825_, v_currMacroScope_3763_);
v___x_3827_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3765_);
lean_ctor_set(v___x_3827_, 1, v___x_3824_);
lean_ctor_set(v___x_3827_, 2, v___x_3826_);
lean_ctor_set(v___x_3827_, 3, v___x_3772_);
v___x_3828_ = l_Lean_Syntax_node5(v___x_3765_, v___x_3783_, v___x_3786_, v___x_3827_, v___x_3793_, v_a_3757_, v___x_3814_);
v___x_3829_ = l_Lean_Syntax_node1(v___x_3765_, v___x_3782_, v___x_3828_);
v___x_3830_ = l_Lean_Syntax_node2(v___x_3765_, v___x_3766_, v_fst_3552_, v___x_3829_);
v___x_3831_ = l_Lean_Syntax_node4(v___x_3765_, v___x_3797_, v___x_3823_, v___x_3808_, v___x_3810_, v___x_3830_);
v___x_3832_ = l_Lean_Syntax_node2(v___x_3765_, v___x_3795_, v___x_3796_, v___x_3831_);
v___x_3833_ = l_Lean_Syntax_node5(v___x_3765_, v___x_3783_, v___x_3786_, v___x_3819_, v___x_3793_, v___x_3832_, v___x_3814_);
v___x_3834_ = l_Lean_Syntax_node2(v___x_3765_, v___x_3782_, v___x_3815_, v___x_3833_);
v___x_3835_ = l_Lean_Syntax_node2(v___x_3765_, v___x_3766_, v___x_3781_, v___x_3834_);
v_a_3518_ = v___x_3835_;
goto v___jp_3517_;
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
lean_del_object(v___x_3560_);
lean_del_object(v___x_3555_);
lean_dec(v_snd_3553_);
lean_dec(v_fst_3552_);
lean_del_object(v___x_3546_);
lean_del_object(v___x_3541_);
lean_del_object(v___x_3537_);
lean_dec_ref(v___y_3514_);
lean_dec_ref(v___x_3507_);
lean_dec_ref(v___x_3506_);
lean_dec_ref(v___x_3505_);
lean_dec_ref(v___x_3504_);
lean_dec(v___x_3495_);
return v___x_3755_;
}
}
default: 
{
lean_object* v_toCold_3843_; lean_object* v_ref_3844_; lean_object* v_quotContext_3845_; lean_object* v_currMacroScope_3846_; uint8_t v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3857_; 
lean_dec(v_default_3558_);
v_toCold_3843_ = lean_ctor_get(v___y_3514_, 0);
lean_inc_ref(v_toCold_3843_);
v_ref_3844_ = lean_ctor_get(v___y_3514_, 2);
lean_inc(v_ref_3844_);
lean_dec_ref(v___y_3514_);
v_quotContext_3845_ = lean_ctor_get(v_toCold_3843_, 8);
lean_inc_n(v_quotContext_3845_, 2);
v_currMacroScope_3846_ = lean_ctor_get(v_toCold_3843_, 9);
lean_inc_n(v_currMacroScope_3846_, 2);
lean_dec_ref(v_toCold_3843_);
v___x_3847_ = 0;
v___x_3848_ = l_Lean_SourceInfo_fromRef(v_ref_3844_, v___x_3847_);
lean_dec(v_ref_3844_);
v___x_3849_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3850_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3851_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3504_);
v___x_3852_ = l_Lean_Name_mkStr2(v___x_3504_, v___x_3851_);
v___x_3853_ = l_Lean_addMacroScope(v_quotContext_3845_, v___x_3852_, v_currMacroScope_3846_);
v___x_3854_ = l_Lean_Name_mkStr4(v___x_3505_, v___x_3506_, v___x_3504_, v___x_3851_);
v___x_3855_ = lean_box(0);
lean_inc(v___x_3854_);
if (v_isShared_3561_ == 0)
{
lean_ctor_set_tag(v___x_3560_, 1);
lean_ctor_set(v___x_3560_, 1, v___x_3855_);
lean_ctor_set(v___x_3560_, 0, v___x_3854_);
v___x_3857_ = v___x_3560_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3854_);
lean_ctor_set(v_reuseFailAlloc_3917_, 1, v___x_3855_);
v___x_3857_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
lean_object* v___x_3859_; 
if (v_isShared_3532_ == 0)
{
lean_ctor_set_tag(v___x_3531_, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3854_);
v___x_3859_ = v___x_3531_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3854_);
v___x_3859_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
lean_object* v___x_3861_; 
if (v_isShared_3556_ == 0)
{
lean_ctor_set_tag(v___x_3555_, 1);
lean_ctor_set(v___x_3555_, 1, v___x_3855_);
lean_ctor_set(v___x_3555_, 0, v___x_3859_);
v___x_3861_ = v___x_3555_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v___x_3855_);
v___x_3861_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3863_; 
if (v_isShared_3547_ == 0)
{
lean_ctor_set_tag(v___x_3546_, 1);
lean_ctor_set(v___x_3546_, 1, v___x_3861_);
lean_ctor_set(v___x_3546_, 0, v___x_3857_);
v___x_3863_ = v___x_3546_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3857_);
lean_ctor_set(v_reuseFailAlloc_3914_, 1, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3869_; 
lean_inc_n(v___x_3848_, 2);
v___x_3864_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3848_);
lean_ctor_set(v___x_3864_, 1, v___x_3850_);
lean_ctor_set(v___x_3864_, 2, v___x_3853_);
lean_ctor_set(v___x_3864_, 3, v___x_3863_);
v___x_3865_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3866_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3867_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3542_ == 0)
{
lean_ctor_set_tag(v___x_3541_, 2);
lean_ctor_set(v___x_3541_, 1, v___x_3867_);
lean_ctor_set(v___x_3541_, 0, v___x_3848_);
v___x_3869_ = v___x_3541_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3848_);
lean_ctor_set(v_reuseFailAlloc_3913_, 1, v___x_3867_);
v___x_3869_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3876_; 
v___x_3870_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3871_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3846_);
lean_inc(v_quotContext_3845_);
v___x_3872_ = l_Lean_addMacroScope(v_quotContext_3845_, v___x_3871_, v_currMacroScope_3846_);
lean_inc_n(v___x_3848_, 2);
v___x_3873_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3848_);
lean_ctor_set(v___x_3873_, 1, v___x_3870_);
lean_ctor_set(v___x_3873_, 2, v___x_3872_);
lean_ctor_set(v___x_3873_, 3, v___x_3855_);
v___x_3874_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3538_ == 0)
{
lean_ctor_set_tag(v___x_3537_, 2);
lean_ctor_set(v___x_3537_, 1, v___x_3874_);
lean_ctor_set(v___x_3537_, 0, v___x_3848_);
v___x_3876_ = v___x_3537_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3848_);
lean_ctor_set(v_reuseFailAlloc_3912_, 1, v___x_3874_);
v___x_3876_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3877_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_3878_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1));
lean_inc_n(v___x_3848_, 17);
v___x_3879_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3848_);
lean_ctor_set(v___x_3879_, 1, v___x_3877_);
v___x_3880_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_3881_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3882_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3846_, 3);
lean_inc_n(v_quotContext_3845_, 3);
v___x_3883_ = l_Lean_addMacroScope(v_quotContext_3845_, v___x_3882_, v_currMacroScope_3846_);
v___x_3884_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3848_);
lean_ctor_set(v___x_3884_, 1, v___x_3881_);
lean_ctor_set(v___x_3884_, 2, v___x_3883_);
lean_ctor_set(v___x_3884_, 3, v___x_3855_);
v___x_3885_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3886_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3887_ = l_Lean_addMacroScope(v_quotContext_3845_, v___x_3886_, v_currMacroScope_3846_);
v___x_3888_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3848_);
lean_ctor_set(v___x_3888_, 1, v___x_3885_);
lean_ctor_set(v___x_3888_, 2, v___x_3887_);
lean_ctor_set(v___x_3888_, 3, v___x_3855_);
lean_inc_ref(v___x_3888_);
v___x_3889_ = l_Lean_Syntax_node2(v___x_3848_, v___x_3865_, v___x_3884_, v___x_3888_);
v___x_3890_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3891_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3848_);
lean_ctor_set(v___x_3891_, 1, v___x_3865_);
lean_ctor_set(v___x_3891_, 2, v___x_3890_);
v___x_3892_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3893_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3848_);
lean_ctor_set(v___x_3893_, 1, v___x_3892_);
lean_inc_ref(v___x_3893_);
lean_inc_ref(v___x_3891_);
v___x_3894_ = l_Lean_Syntax_node4(v___x_3848_, v___x_3880_, v___x_3889_, v___x_3891_, v___x_3893_, v_snd_3553_);
lean_inc_ref(v___x_3879_);
v___x_3895_ = l_Lean_Syntax_node2(v___x_3848_, v___x_3878_, v___x_3879_, v___x_3894_);
v___x_3896_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3897_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3848_);
lean_ctor_set(v___x_3897_, 1, v___x_3896_);
lean_inc_ref(v___x_3897_);
lean_inc_ref(v___x_3876_);
lean_inc_ref(v___x_3869_);
v___x_3898_ = l_Lean_Syntax_node5(v___x_3848_, v___x_3866_, v___x_3869_, v___x_3873_, v___x_3876_, v___x_3895_, v___x_3897_);
v___x_3899_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3900_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3901_ = l_Lean_addMacroScope(v_quotContext_3845_, v___x_3900_, v_currMacroScope_3846_);
v___x_3902_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3848_);
lean_ctor_set(v___x_3902_, 1, v___x_3899_);
lean_ctor_set(v___x_3902_, 2, v___x_3901_);
lean_ctor_set(v___x_3902_, 3, v___x_3855_);
v___x_3903_ = l_String_toRawSubstring_x27(v___x_3507_);
v___x_3904_ = l_Lean_addMacroScope(v_quotContext_3845_, v___x_3495_, v_currMacroScope_3846_);
v___x_3905_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3848_);
lean_ctor_set(v___x_3905_, 1, v___x_3903_);
lean_ctor_set(v___x_3905_, 2, v___x_3904_);
lean_ctor_set(v___x_3905_, 3, v___x_3855_);
v___x_3906_ = l_Lean_Syntax_node2(v___x_3848_, v___x_3865_, v___x_3905_, v___x_3888_);
v___x_3907_ = l_Lean_Syntax_node4(v___x_3848_, v___x_3880_, v___x_3906_, v___x_3891_, v___x_3893_, v_fst_3552_);
v___x_3908_ = l_Lean_Syntax_node2(v___x_3848_, v___x_3878_, v___x_3879_, v___x_3907_);
v___x_3909_ = l_Lean_Syntax_node5(v___x_3848_, v___x_3866_, v___x_3869_, v___x_3902_, v___x_3876_, v___x_3908_, v___x_3897_);
v___x_3910_ = l_Lean_Syntax_node2(v___x_3848_, v___x_3865_, v___x_3898_, v___x_3909_);
v___x_3911_ = l_Lean_Syntax_node2(v___x_3848_, v___x_3849_, v___x_3864_, v___x_3910_);
v_a_3518_ = v___x_3911_;
goto v___jp_3517_;
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
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
lean_del_object(v___x_3546_);
lean_dec(v_snd_3544_);
lean_del_object(v___x_3541_);
lean_del_object(v___x_3537_);
lean_del_object(v___x_3531_);
lean_dec_ref(v___y_3514_);
lean_dec_ref(v___x_3507_);
lean_dec_ref(v___x_3506_);
lean_dec_ref(v___x_3505_);
lean_dec_ref(v___x_3504_);
lean_dec(v___x_3503_);
lean_dec(v___x_3495_);
v_a_3920_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3550_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___x_3550_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
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
lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_4007_; 
lean_dec(v_a_3522_);
lean_dec(v___x_3503_);
lean_dec(v___x_3501_);
lean_dec_ref(v___x_3496_);
v_isSharedCheck_4007_ = !lean_is_exclusive(v_val_3525_);
if (v_isSharedCheck_4007_ == 0)
{
lean_object* v_unused_4008_; lean_object* v_unused_4009_; 
v_unused_4008_ = lean_ctor_get(v_val_3525_, 1);
lean_dec(v_unused_4008_);
v_unused_4009_ = lean_ctor_get(v_val_3525_, 0);
lean_dec(v_unused_4009_);
v___x_3934_ = v_val_3525_;
v_isShared_3935_ = v_isSharedCheck_4007_;
goto v_resetjp_3933_;
}
else
{
lean_dec(v_val_3525_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_4007_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v_toCold_3936_; lean_object* v_ref_3937_; lean_object* v_quotContext_3938_; lean_object* v_currMacroScope_3939_; uint8_t v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3950_; 
v_toCold_3936_ = lean_ctor_get(v___y_3514_, 0);
lean_inc_ref(v_toCold_3936_);
v_ref_3937_ = lean_ctor_get(v___y_3514_, 2);
lean_inc(v_ref_3937_);
lean_dec_ref(v___y_3514_);
v_quotContext_3938_ = lean_ctor_get(v_toCold_3936_, 8);
lean_inc_n(v_quotContext_3938_, 2);
v_currMacroScope_3939_ = lean_ctor_get(v_toCold_3936_, 9);
lean_inc_n(v_currMacroScope_3939_, 2);
lean_dec_ref(v_toCold_3936_);
v___x_3940_ = 0;
v___x_3941_ = l_Lean_SourceInfo_fromRef(v_ref_3937_, v___x_3940_);
lean_dec(v_ref_3937_);
v___x_3942_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3943_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3944_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3504_);
v___x_3945_ = l_Lean_Name_mkStr2(v___x_3504_, v___x_3944_);
v___x_3946_ = l_Lean_addMacroScope(v_quotContext_3938_, v___x_3945_, v_currMacroScope_3939_);
v___x_3947_ = l_Lean_Name_mkStr4(v___x_3505_, v___x_3506_, v___x_3504_, v___x_3944_);
v___x_3948_ = lean_box(0);
lean_inc(v___x_3947_);
if (v_isShared_3935_ == 0)
{
lean_ctor_set_tag(v___x_3934_, 1);
lean_ctor_set(v___x_3934_, 1, v___x_3948_);
lean_ctor_set(v___x_3934_, 0, v___x_3947_);
v___x_3950_ = v___x_3934_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v___x_3947_);
lean_ctor_set(v_reuseFailAlloc_4006_, 1, v___x_3948_);
v___x_3950_ = v_reuseFailAlloc_4006_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
lean_object* v___x_3952_; 
if (v_isShared_3528_ == 0)
{
lean_ctor_set_tag(v___x_3527_, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3947_);
v___x_3952_ = v___x_3527_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___x_3947_);
v___x_3952_ = v_reuseFailAlloc_4005_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_3953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3952_);
lean_ctor_set(v___x_3953_, 1, v___x_3948_);
v___x_3954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3950_);
lean_ctor_set(v___x_3954_, 1, v___x_3953_);
lean_inc_n(v___x_3941_, 23);
v___x_3955_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3941_);
lean_ctor_set(v___x_3955_, 1, v___x_3943_);
lean_ctor_set(v___x_3955_, 2, v___x_3946_);
lean_ctor_set(v___x_3955_, 3, v___x_3954_);
v___x_3956_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3957_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3958_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
v___x_3959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3941_);
lean_ctor_set(v___x_3959_, 1, v___x_3958_);
v___x_3960_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3961_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc_n(v_currMacroScope_3939_, 4);
lean_inc_n(v_quotContext_3938_, 4);
v___x_3962_ = l_Lean_addMacroScope(v_quotContext_3938_, v___x_3961_, v_currMacroScope_3939_);
v___x_3963_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3941_);
lean_ctor_set(v___x_3963_, 1, v___x_3960_);
lean_ctor_set(v___x_3963_, 2, v___x_3962_);
lean_ctor_set(v___x_3963_, 3, v___x_3948_);
v___x_3964_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
v___x_3965_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3941_);
lean_ctor_set(v___x_3965_, 1, v___x_3964_);
v___x_3966_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_3967_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1));
v___x_3968_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3941_);
lean_ctor_set(v___x_3968_, 1, v___x_3966_);
v___x_3969_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_3970_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3971_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_3972_ = l_Lean_addMacroScope(v_quotContext_3938_, v___x_3971_, v_currMacroScope_3939_);
v___x_3973_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3941_);
lean_ctor_set(v___x_3973_, 1, v___x_3970_);
lean_ctor_set(v___x_3973_, 2, v___x_3972_);
lean_ctor_set(v___x_3973_, 3, v___x_3948_);
v___x_3974_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3975_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3976_ = l_Lean_addMacroScope(v_quotContext_3938_, v___x_3975_, v_currMacroScope_3939_);
v___x_3977_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3941_);
lean_ctor_set(v___x_3977_, 1, v___x_3974_);
lean_ctor_set(v___x_3977_, 2, v___x_3976_);
lean_ctor_set(v___x_3977_, 3, v___x_3948_);
lean_inc_ref(v___x_3977_);
v___x_3978_ = l_Lean_Syntax_node2(v___x_3941_, v___x_3956_, v___x_3973_, v___x_3977_);
v___x_3979_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3980_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3941_);
lean_ctor_set(v___x_3980_, 1, v___x_3956_);
lean_ctor_set(v___x_3980_, 2, v___x_3979_);
v___x_3981_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3982_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3941_);
lean_ctor_set(v___x_3982_, 1, v___x_3981_);
v___x_3983_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_3984_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
v___x_3985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3941_);
lean_ctor_set(v___x_3985_, 1, v___x_3984_);
v___x_3986_ = l_Lean_Syntax_node1(v___x_3941_, v___x_3983_, v___x_3985_);
lean_inc(v___x_3986_);
lean_inc_ref(v___x_3982_);
lean_inc_ref(v___x_3980_);
v___x_3987_ = l_Lean_Syntax_node4(v___x_3941_, v___x_3969_, v___x_3978_, v___x_3980_, v___x_3982_, v___x_3986_);
lean_inc_ref(v___x_3968_);
v___x_3988_ = l_Lean_Syntax_node2(v___x_3941_, v___x_3967_, v___x_3968_, v___x_3987_);
v___x_3989_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3941_);
lean_ctor_set(v___x_3990_, 1, v___x_3989_);
lean_inc_ref(v___x_3990_);
lean_inc_ref(v___x_3965_);
lean_inc_ref(v___x_3959_);
v___x_3991_ = l_Lean_Syntax_node5(v___x_3941_, v___x_3957_, v___x_3959_, v___x_3963_, v___x_3965_, v___x_3988_, v___x_3990_);
v___x_3992_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3993_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3994_ = l_Lean_addMacroScope(v_quotContext_3938_, v___x_3993_, v_currMacroScope_3939_);
v___x_3995_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3941_);
lean_ctor_set(v___x_3995_, 1, v___x_3992_);
lean_ctor_set(v___x_3995_, 2, v___x_3994_);
lean_ctor_set(v___x_3995_, 3, v___x_3948_);
v___x_3996_ = l_String_toRawSubstring_x27(v___x_3507_);
v___x_3997_ = l_Lean_addMacroScope(v_quotContext_3938_, v___x_3495_, v_currMacroScope_3939_);
v___x_3998_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3941_);
lean_ctor_set(v___x_3998_, 1, v___x_3996_);
lean_ctor_set(v___x_3998_, 2, v___x_3997_);
lean_ctor_set(v___x_3998_, 3, v___x_3948_);
v___x_3999_ = l_Lean_Syntax_node2(v___x_3941_, v___x_3956_, v___x_3998_, v___x_3977_);
v___x_4000_ = l_Lean_Syntax_node4(v___x_3941_, v___x_3969_, v___x_3999_, v___x_3980_, v___x_3982_, v___x_3986_);
v___x_4001_ = l_Lean_Syntax_node2(v___x_3941_, v___x_3967_, v___x_3968_, v___x_4000_);
v___x_4002_ = l_Lean_Syntax_node5(v___x_3941_, v___x_3957_, v___x_3959_, v___x_3995_, v___x_3965_, v___x_4001_, v___x_3990_);
v___x_4003_ = l_Lean_Syntax_node2(v___x_3941_, v___x_3956_, v___x_3991_, v___x_4002_);
v___x_4004_ = l_Lean_Syntax_node2(v___x_3941_, v___x_3942_, v___x_3955_, v___x_4003_);
v_a_3518_ = v___x_4004_;
goto v___jp_3517_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3524_);
lean_dec_ref(v___x_3504_);
if (lean_obj_tag(v_a_3522_) == 1)
{
lean_object* v_val_4011_; lean_object* v_snd_4012_; lean_object* v_fst_4013_; lean_object* v_snd_4014_; lean_object* v___f_4015_; lean_object* v___x_4016_; 
v_val_4011_ = lean_ctor_get(v_a_3522_, 0);
lean_inc(v_val_4011_);
lean_dec_ref_known(v_a_3522_, 1);
v_snd_4012_ = lean_ctor_get(v_val_4011_, 1);
lean_inc(v_snd_4012_);
v_fst_4013_ = lean_ctor_get(v_val_4011_, 0);
lean_inc(v_fst_4013_);
lean_dec(v_val_4011_);
v_snd_4014_ = lean_ctor_get(v_snd_4012_, 1);
lean_inc(v_snd_4014_);
lean_dec(v_snd_4012_);
lean_inc(v___x_3495_);
v___f_4015_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed), 19, 9);
lean_closure_set(v___f_4015_, 0, v_fst_4013_);
lean_closure_set(v___f_4015_, 1, v_snd_4014_);
lean_closure_set(v___f_4015_, 2, v___x_3507_);
lean_closure_set(v___f_4015_, 3, v___x_3495_);
lean_closure_set(v___f_4015_, 4, v___x_3501_);
lean_closure_set(v___f_4015_, 5, v___x_3503_);
lean_closure_set(v___f_4015_, 6, v___x_3505_);
lean_closure_set(v___f_4015_, 7, v___x_3506_);
lean_closure_set(v___f_4015_, 8, v_arg_3500_);
v___x_4016_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3495_, v___x_3496_, v___f_4015_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
lean_dec_ref(v___y_3514_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v_a_4017_; 
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
lean_inc(v_a_4017_);
lean_dec_ref_known(v___x_4016_, 1);
v_a_3518_ = v_a_4017_;
goto v___jp_3517_;
}
else
{
return v___x_4016_;
}
}
else
{
lean_object* v_toCold_4018_; lean_object* v_ref_4019_; lean_object* v_quotContext_4020_; lean_object* v_currMacroScope_4021_; uint8_t v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
lean_dec(v_a_3522_);
lean_dec(v___x_3503_);
lean_dec(v___x_3501_);
lean_dec_ref(v_arg_3500_);
lean_dec_ref(v___x_3496_);
v_toCold_4018_ = lean_ctor_get(v___y_3514_, 0);
lean_inc_ref(v_toCold_4018_);
v_ref_4019_ = lean_ctor_get(v___y_3514_, 2);
lean_inc(v_ref_4019_);
lean_dec_ref(v___y_3514_);
v_quotContext_4020_ = lean_ctor_get(v_toCold_4018_, 8);
lean_inc_n(v_quotContext_4020_, 2);
v_currMacroScope_4021_ = lean_ctor_get(v_toCold_4018_, 9);
lean_inc_n(v_currMacroScope_4021_, 2);
lean_dec_ref(v_toCold_4018_);
v___x_4022_ = 0;
v___x_4023_ = l_Lean_SourceInfo_fromRef(v_ref_4019_, v___x_4022_);
lean_dec(v_ref_4019_);
v___x_4024_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__9));
v___x_4025_ = l_Lean_Name_mkStr3(v___x_3505_, v___x_3506_, v___x_4024_);
v___x_4026_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__7));
v___x_4027_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_4023_, 13);
v___x_4028_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4023_);
lean_ctor_set(v___x_4028_, 1, v___x_4026_);
lean_ctor_set(v___x_4028_, 2, v___x_4027_);
v___x_4029_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__10));
v___x_4030_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4023_);
lean_ctor_set(v___x_4030_, 1, v___x_4029_);
v___x_4031_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_4032_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_4033_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_4034_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4023_);
lean_ctor_set(v___x_4034_, 1, v___x_4033_);
v___x_4035_ = l_String_toRawSubstring_x27(v___x_3507_);
v___x_4036_ = l_Lean_addMacroScope(v_quotContext_4020_, v___x_3495_, v_currMacroScope_4021_);
v___x_4037_ = lean_box(0);
v___x_4038_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4023_);
lean_ctor_set(v___x_4038_, 1, v___x_4035_);
lean_ctor_set(v___x_4038_, 2, v___x_4036_);
lean_ctor_set(v___x_4038_, 3, v___x_4037_);
v___x_4039_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_4040_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4023_);
lean_ctor_set(v___x_4040_, 1, v___x_4039_);
v___x_4041_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4042_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4043_ = l_Lean_addMacroScope(v_quotContext_4020_, v___x_4042_, v_currMacroScope_4021_);
v___x_4044_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4023_);
lean_ctor_set(v___x_4044_, 1, v___x_4041_);
lean_ctor_set(v___x_4044_, 2, v___x_4043_);
lean_ctor_set(v___x_4044_, 3, v___x_4037_);
v___x_4045_ = l_Lean_Syntax_node3(v___x_4023_, v___x_4031_, v___x_4038_, v___x_4040_, v___x_4044_);
v___x_4046_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_4047_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4023_);
lean_ctor_set(v___x_4047_, 1, v___x_4046_);
v___x_4048_ = l_Lean_Syntax_node3(v___x_4023_, v___x_4032_, v___x_4034_, v___x_4045_, v___x_4047_);
v___x_4049_ = l_Lean_Syntax_node1(v___x_4023_, v___x_4031_, v___x_4048_);
v___x_4050_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_4051_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4023_);
lean_ctor_set(v___x_4051_, 1, v___x_4050_);
v___x_4052_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_4053_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
v___x_4054_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4023_);
lean_ctor_set(v___x_4054_, 1, v___x_4053_);
v___x_4055_ = l_Lean_Syntax_node1(v___x_4023_, v___x_4052_, v___x_4054_);
v___x_4056_ = l_Lean_Syntax_node5(v___x_4023_, v___x_4025_, v___x_4028_, v___x_4030_, v___x_4049_, v___x_4051_, v___x_4055_);
v_a_3518_ = v___x_4056_;
goto v___jp_3517_;
}
}
}
else
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4064_; 
lean_dec(v_a_3522_);
lean_dec_ref(v___y_3514_);
lean_dec_ref(v___x_3507_);
lean_dec_ref(v___x_3506_);
lean_dec_ref(v___x_3505_);
lean_dec_ref(v___x_3504_);
lean_dec(v___x_3503_);
lean_dec(v___x_3501_);
lean_dec_ref(v_arg_3500_);
lean_dec_ref(v___x_3496_);
lean_dec(v___x_3495_);
v_a_4057_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4059_ = v___x_3523_;
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v___x_3523_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
}
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_dec_ref(v___y_3514_);
lean_dec_ref(v___x_3507_);
lean_dec_ref(v___x_3506_);
lean_dec_ref(v___x_3505_);
lean_dec_ref(v___x_3504_);
lean_dec(v___x_3503_);
lean_dec(v___x_3501_);
lean_dec_ref(v_arg_3500_);
lean_dec(v_inv_3499_);
lean_dec_ref(v___x_3496_);
lean_dec(v___x_3495_);
v_a_4065_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_3521_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_3521_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
v___jp_3517_:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3519_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_a_3518_);
v___x_3520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3519_);
return v___x_3520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed(lean_object** _args){
lean_object* v___x_4073_ = _args[0];
lean_object* v___x_4074_ = _args[1];
lean_object* v___f_4075_ = _args[2];
lean_object* v_a_4076_ = _args[3];
lean_object* v_inv_4077_ = _args[4];
lean_object* v_arg_4078_ = _args[5];
lean_object* v___x_4079_ = _args[6];
lean_object* v___x_4080_ = _args[7];
lean_object* v___x_4081_ = _args[8];
lean_object* v___x_4082_ = _args[9];
lean_object* v___x_4083_ = _args[10];
lean_object* v___x_4084_ = _args[11];
lean_object* v___x_4085_ = _args[12];
lean_object* v___y_4086_ = _args[13];
lean_object* v___y_4087_ = _args[14];
lean_object* v___y_4088_ = _args[15];
lean_object* v___y_4089_ = _args[16];
lean_object* v___y_4090_ = _args[17];
lean_object* v___y_4091_ = _args[18];
lean_object* v___y_4092_ = _args[19];
lean_object* v___y_4093_ = _args[20];
lean_object* v___y_4094_ = _args[21];
_start:
{
uint8_t v___x_79181__boxed_4095_; lean_object* v_res_4096_; 
v___x_79181__boxed_4095_ = lean_unbox(v___x_4080_);
v_res_4096_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(v___x_4073_, v___x_4074_, v___f_4075_, v_a_4076_, v_inv_4077_, v_arg_4078_, v___x_4079_, v___x_79181__boxed_4095_, v___x_4081_, v___x_4082_, v___x_4083_, v___x_4084_, v___x_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
lean_dec(v___y_4093_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
lean_dec_ref(v_a_4076_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(lean_object* v_msgData_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v___x_4103_; lean_object* v_env_4104_; uint8_t v___x_4105_; lean_object* v_env_4106_; lean_object* v___x_4107_; lean_object* v_toCold_4108_; lean_object* v_mctx_4109_; lean_object* v_lctx_4110_; lean_object* v_options_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4103_ = lean_st_ref_get(v___y_4101_);
v_env_4104_ = lean_ctor_get(v___x_4103_, 0);
lean_inc_ref(v_env_4104_);
lean_dec(v___x_4103_);
v___x_4105_ = 0;
v_env_4106_ = l_Lean_Environment_setRecordingDeps(v_env_4104_, v___x_4105_);
v___x_4107_ = lean_st_ref_get(v___y_4099_);
v_toCold_4108_ = lean_ctor_get(v___y_4100_, 0);
v_mctx_4109_ = lean_ctor_get(v___x_4107_, 0);
lean_inc_ref(v_mctx_4109_);
lean_dec(v___x_4107_);
v_lctx_4110_ = lean_ctor_get(v___y_4098_, 2);
v_options_4111_ = lean_ctor_get(v_toCold_4108_, 2);
lean_inc_ref(v_options_4111_);
lean_inc_ref(v_lctx_4110_);
v___x_4112_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4112_, 0, v_env_4106_);
lean_ctor_set(v___x_4112_, 1, v_mctx_4109_);
lean_ctor_set(v___x_4112_, 2, v_lctx_4110_);
lean_ctor_set(v___x_4112_, 3, v_options_4111_);
v___x_4113_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4112_);
lean_ctor_set(v___x_4113_, 1, v_msgData_4097_);
v___x_4114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4113_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1___boxed(lean_object* v_msgData_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msgData_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(lean_object* v_msg_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
lean_object* v_ref_4128_; lean_object* v___x_4129_; lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4138_; 
v_ref_4128_ = lean_ctor_get(v___y_4125_, 2);
v___x_4129_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msg_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
v_a_4130_ = lean_ctor_get(v___x_4129_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4132_ = v___x_4129_;
v_isShared_4133_ = v_isSharedCheck_4138_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4129_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4138_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4134_; lean_object* v___x_4136_; 
lean_inc(v_ref_4128_);
v___x_4134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4134_, 0, v_ref_4128_);
lean_ctor_set(v___x_4134_, 1, v_a_4130_);
if (v_isShared_4133_ == 0)
{
lean_ctor_set_tag(v___x_4132_, 1);
lean_ctor_set(v___x_4132_, 0, v___x_4134_);
v___x_4136_ = v___x_4132_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v___x_4134_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg___boxed(lean_object* v_msg_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(lean_object* v_as_4152_, size_t v_i_4153_, size_t v_stop_4154_, lean_object* v_b_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v_a_4166_; lean_object* v___y_4171_; lean_object* v_a_4174_; uint8_t v___x_4176_; 
v___x_4176_ = lean_usize_dec_eq(v_i_4153_, v_stop_4154_);
if (v___x_4176_ == 0)
{
lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___x_4177_ = lean_array_uget_borrowed(v_as_4152_, v_i_4153_);
v___x_4178_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_4157_, v___y_4159_, v___y_4161_, v___y_4163_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_object* v_a_4179_; lean_object* v___y_4181_; lean_object* v_a_4182_; lean_object* v_ref_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v_a_4179_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_a_4179_);
lean_dec_ref_known(v___x_4178_, 1);
v_ref_4197_ = lean_ctor_get(v___y_4162_, 2);
v___x_4198_ = l_Lean_SourceInfo_fromRef(v_ref_4197_, v___x_4176_);
v___x_4199_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__0));
v___x_4200_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__1));
lean_inc(v___x_4198_);
v___x_4201_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4201_, 0, v___x_4198_);
lean_ctor_set(v___x_4201_, 1, v___x_4199_);
v___x_4202_ = l_Lean_Syntax_node1(v___x_4198_, v___x_4200_, v___x_4201_);
lean_inc(v___x_4177_);
v___x_4203_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v___x_4177_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4205_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc(v_a_4204_);
lean_dec_ref_known(v___x_4203_, 1);
v___x_4205_ = l_Lean_Elab_Tactic_evalTacticAt(v___x_4202_, v_a_4204_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; lean_object* v___x_4207_; 
lean_dec(v_a_4179_);
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref_known(v___x_4205_, 1);
v___x_4207_ = lean_array_mk(v_a_4206_);
v_a_4174_ = v___x_4207_;
goto v___jp_4173_;
}
else
{
lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4215_; 
v_a_4208_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4210_ = v___x_4205_;
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4205_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4213_; 
lean_inc(v_a_4208_);
if (v_isShared_4211_ == 0)
{
v___x_4213_ = v___x_4210_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4208_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
v___y_4181_ = v___x_4213_;
v_a_4182_ = v_a_4208_;
goto v___jp_4180_;
}
}
}
}
else
{
lean_object* v_a_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4223_; 
lean_dec(v___x_4202_);
v_a_4216_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4218_ = v___x_4203_;
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_a_4216_);
lean_dec(v___x_4203_);
v___x_4218_ = lean_box(0);
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
v_resetjp_4217_:
{
lean_object* v___x_4221_; 
lean_inc(v_a_4216_);
if (v_isShared_4219_ == 0)
{
v___x_4221_ = v___x_4218_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_a_4216_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
v___y_4181_ = v___x_4221_;
v_a_4182_ = v_a_4216_;
goto v___jp_4180_;
}
}
}
v___jp_4180_:
{
uint8_t v___x_4183_; 
v___x_4183_ = l_Lean_Exception_isInterrupt(v_a_4182_);
if (v___x_4183_ == 0)
{
uint8_t v___x_4184_; 
v___x_4184_ = l_Lean_Exception_isRuntime(v_a_4182_);
if (v___x_4184_ == 0)
{
lean_object* v___x_4185_; 
lean_dec_ref(v___y_4181_);
v___x_4185_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_4179_, v___x_4184_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
lean_dec_ref_known(v___x_4185_, 1);
v___x_4186_ = lean_unsigned_to_nat(1u);
v___x_4187_ = lean_mk_empty_array_with_capacity(v___x_4186_);
lean_inc(v___x_4177_);
v___x_4188_ = lean_array_push(v___x_4187_, v___x_4177_);
v_a_4174_ = v___x_4188_;
goto v___jp_4173_;
}
else
{
lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4196_; 
lean_dec_ref(v_b_4155_);
v_a_4189_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4191_ = v___x_4185_;
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_dec(v___x_4185_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4194_; 
if (v_isShared_4192_ == 0)
{
v___x_4194_ = v___x_4191_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_a_4189_);
v___x_4194_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
return v___x_4194_;
}
}
}
}
else
{
lean_dec(v_a_4179_);
lean_dec_ref(v_b_4155_);
v___y_4171_ = v___y_4181_;
goto v___jp_4170_;
}
}
else
{
lean_dec_ref(v_a_4182_);
lean_dec(v_a_4179_);
lean_dec_ref(v_b_4155_);
v___y_4171_ = v___y_4181_;
goto v___jp_4170_;
}
}
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
lean_dec_ref(v_b_4155_);
v_a_4224_ = lean_ctor_get(v___x_4178_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4178_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4178_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4178_);
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
lean_object* v___x_4232_; 
v___x_4232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4232_, 0, v_b_4155_);
return v___x_4232_;
}
v___jp_4165_:
{
size_t v___x_4167_; size_t v___x_4168_; 
v___x_4167_ = ((size_t)1ULL);
v___x_4168_ = lean_usize_add(v_i_4153_, v___x_4167_);
v_i_4153_ = v___x_4168_;
v_b_4155_ = v_a_4166_;
goto _start;
}
v___jp_4170_:
{
if (lean_obj_tag(v___y_4171_) == 0)
{
lean_object* v_a_4172_; 
v_a_4172_ = lean_ctor_get(v___y_4171_, 0);
lean_inc(v_a_4172_);
lean_dec_ref_known(v___y_4171_, 1);
v_a_4166_ = v_a_4172_;
goto v___jp_4165_;
}
else
{
return v___y_4171_;
}
}
v___jp_4173_:
{
lean_object* v___x_4175_; 
v___x_4175_ = l_Array_append___redArg(v_b_4155_, v_a_4174_);
lean_dec_ref(v_a_4174_);
v_a_4166_ = v___x_4175_;
goto v___jp_4165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___boxed(lean_object* v_as_4233_, lean_object* v_i_4234_, lean_object* v_stop_4235_, lean_object* v_b_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_){
_start:
{
size_t v_i_boxed_4246_; size_t v_stop_boxed_4247_; lean_object* v_res_4248_; 
v_i_boxed_4246_ = lean_unbox_usize(v_i_4234_);
lean_dec(v_i_4234_);
v_stop_boxed_4247_ = lean_unbox_usize(v_stop_4235_);
lean_dec(v_stop_4235_);
v_res_4248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_as_4233_, v_i_boxed_4246_, v_stop_boxed_4247_, v_b_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
lean_dec(v___y_4244_);
lean_dec_ref(v___y_4243_);
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4241_);
lean_dec(v___y_4240_);
lean_dec_ref(v___y_4239_);
lean_dec(v___y_4238_);
lean_dec_ref(v___y_4237_);
lean_dec_ref(v_as_4233_);
return v_res_4248_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1(void){
_start:
{
lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4250_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__0));
v___x_4251_ = l_Lean_stringToMessageData(v___x_4250_);
return v___x_4251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant(lean_object* v_vcs_4267_, lean_object* v_inv_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_){
_start:
{
lean_object* v___x_4278_; 
lean_inc(v_inv_4268_);
v___x_4278_ = l_Lean_MVarId_getType(v_inv_4268_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_);
if (lean_obj_tag(v___x_4278_) == 0)
{
lean_object* v_a_4279_; lean_object* v___x_4280_; lean_object* v_a_4281_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___x_4295_; uint8_t v___x_4296_; 
v_a_4279_ = lean_ctor_get(v___x_4278_, 0);
lean_inc(v_a_4279_);
lean_dec_ref_known(v___x_4278_, 1);
v___x_4280_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_a_4279_, v_a_4274_);
v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
lean_inc_n(v_a_4281_, 2);
lean_dec_ref(v___x_4280_);
v___x_4295_ = l_Lean_Expr_cleanupAnnotations(v_a_4281_);
v___x_4296_ = l_Lean_Expr_isApp(v___x_4295_);
if (v___x_4296_ == 0)
{
lean_dec_ref(v___x_4295_);
lean_dec(v_inv_4268_);
v___y_4283_ = v_a_4269_;
v___y_4284_ = v_a_4270_;
v___y_4285_ = v_a_4271_;
v___y_4286_ = v_a_4272_;
v___y_4287_ = v_a_4273_;
v___y_4288_ = v_a_4274_;
v___y_4289_ = v_a_4275_;
v___y_4290_ = v_a_4276_;
goto v___jp_4282_;
}
else
{
lean_object* v___x_4297_; uint8_t v___x_4298_; 
v___x_4297_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4295_);
v___x_4298_ = l_Lean_Expr_isApp(v___x_4297_);
if (v___x_4298_ == 0)
{
lean_dec_ref(v___x_4297_);
lean_dec(v_inv_4268_);
v___y_4283_ = v_a_4269_;
v___y_4284_ = v_a_4270_;
v___y_4285_ = v_a_4271_;
v___y_4286_ = v_a_4272_;
v___y_4287_ = v_a_4273_;
v___y_4288_ = v_a_4274_;
v___y_4289_ = v_a_4275_;
v___y_4290_ = v_a_4276_;
goto v___jp_4282_;
}
else
{
lean_object* v_arg_4299_; lean_object* v___x_4300_; uint8_t v___x_4301_; 
v_arg_4299_ = lean_ctor_get(v___x_4297_, 1);
lean_inc_ref(v_arg_4299_);
v___x_4300_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4297_);
v___x_4301_ = l_Lean_Expr_isApp(v___x_4300_);
if (v___x_4301_ == 0)
{
lean_dec_ref(v___x_4300_);
lean_dec_ref(v_arg_4299_);
lean_dec(v_inv_4268_);
v___y_4283_ = v_a_4269_;
v___y_4284_ = v_a_4270_;
v___y_4285_ = v_a_4271_;
v___y_4286_ = v_a_4272_;
v___y_4287_ = v_a_4273_;
v___y_4288_ = v_a_4274_;
v___y_4289_ = v_a_4275_;
v___y_4290_ = v_a_4276_;
goto v___jp_4282_;
}
else
{
lean_object* v_arg_4302_; lean_object* v___x_4303_; uint8_t v___x_4304_; 
v_arg_4302_ = lean_ctor_get(v___x_4300_, 1);
lean_inc_ref(v_arg_4302_);
v___x_4303_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4300_);
v___x_4304_ = l_Lean_Expr_isApp(v___x_4303_);
if (v___x_4304_ == 0)
{
lean_dec_ref(v___x_4303_);
lean_dec_ref(v_arg_4302_);
lean_dec_ref(v_arg_4299_);
lean_dec(v_inv_4268_);
v___y_4283_ = v_a_4269_;
v___y_4284_ = v_a_4270_;
v___y_4285_ = v_a_4271_;
v___y_4286_ = v_a_4272_;
v___y_4287_ = v_a_4273_;
v___y_4288_ = v_a_4274_;
v___y_4289_ = v_a_4275_;
v___y_4290_ = v_a_4276_;
goto v___jp_4282_;
}
else
{
lean_object* v_arg_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; uint8_t v___x_4311_; 
v_arg_4305_ = lean_ctor_get(v___x_4303_, 1);
lean_inc_ref(v_arg_4305_);
v___x_4306_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4303_);
v___x_4307_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1));
v___x_4308_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3));
v___x_4309_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__2));
v___x_4310_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__3));
v___x_4311_ = l_Lean_Expr_isConstOf(v___x_4306_, v___x_4310_);
if (v___x_4311_ == 0)
{
lean_dec_ref(v___x_4306_);
lean_dec_ref(v_arg_4305_);
lean_dec_ref(v_arg_4302_);
lean_dec_ref(v_arg_4299_);
lean_dec(v_inv_4268_);
v___y_4283_ = v_a_4269_;
v___y_4284_ = v_a_4270_;
v___y_4285_ = v_a_4271_;
v___y_4286_ = v_a_4272_;
v___y_4287_ = v_a_4273_;
v___y_4288_ = v_a_4274_;
v___y_4289_ = v_a_4275_;
v___y_4290_ = v_a_4276_;
goto v___jp_4282_;
}
else
{
lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v_a_4318_; lean_object* v___x_4329_; lean_object* v___x_4330_; uint8_t v___x_4331_; 
lean_dec(v_a_4281_);
v___x_4312_ = lean_unsigned_to_nat(1u);
v___x_4313_ = l_Lean_Expr_constLevels_x21(v___x_4306_);
lean_dec_ref(v___x_4306_);
v___x_4314_ = lean_unsigned_to_nat(0u);
v___x_4315_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__4));
lean_inc(v___x_4313_);
v___x_4316_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v___x_4313_, v___x_4313_, v___x_4312_, v___x_4315_);
lean_dec(v___x_4313_);
v___x_4329_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__8));
v___x_4330_ = lean_array_get_size(v_vcs_4267_);
v___x_4331_ = lean_nat_dec_lt(v___x_4314_, v___x_4330_);
if (v___x_4331_ == 0)
{
v_a_4318_ = v___x_4329_;
goto v___jp_4317_;
}
else
{
size_t v___x_4332_; size_t v___x_4333_; lean_object* v___x_4334_; 
v___x_4332_ = ((size_t)0ULL);
v___x_4333_ = lean_usize_of_nat(v___x_4330_);
v___x_4334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_vcs_4267_, v___x_4332_, v___x_4333_, v___x_4329_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v_a_4335_; 
v_a_4335_ = lean_ctor_get(v___x_4334_, 0);
lean_inc(v_a_4335_);
lean_dec_ref_known(v___x_4334_, 1);
v_a_4318_ = v_a_4335_;
goto v___jp_4317_;
}
else
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4343_; 
lean_dec(v___x_4316_);
lean_dec_ref(v_arg_4305_);
lean_dec_ref(v_arg_4302_);
lean_dec_ref(v_arg_4299_);
lean_dec(v_inv_4268_);
v_a_4336_ = lean_ctor_get(v___x_4334_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4338_ = v___x_4334_;
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4334_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4341_; 
if (v_isShared_4339_ == 0)
{
v___x_4341_ = v___x_4338_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_a_4336_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
}
}
v___jp_4317_:
{
lean_object* v___x_4319_; lean_object* v___f_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___f_4327_; lean_object* v___x_4328_; 
v___x_4319_ = lean_box(v___x_4311_);
lean_inc_ref(v_arg_4299_);
lean_inc_n(v_inv_4268_, 2);
lean_inc_ref(v_a_4318_);
v___f_4320_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed), 15, 5);
lean_closure_set(v___f_4320_, 0, v_a_4318_);
lean_closure_set(v___f_4320_, 1, v_inv_4268_);
lean_closure_set(v___f_4320_, 2, v___x_4319_);
lean_closure_set(v___f_4320_, 3, v___x_4312_);
lean_closure_set(v___f_4320_, 4, v_arg_4299_);
v___x_4321_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__5));
v___x_4322_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__6));
v___x_4323_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__7));
v___x_4324_ = l_Lean_mkConst(v___x_4323_, v___x_4316_);
v___x_4325_ = l_Lean_mkAppB(v___x_4324_, v_arg_4305_, v_arg_4302_);
v___x_4326_ = lean_box(v___x_4311_);
v___f_4327_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed), 22, 13);
lean_closure_set(v___f_4327_, 0, v___x_4322_);
lean_closure_set(v___f_4327_, 1, v___x_4325_);
lean_closure_set(v___f_4327_, 2, v___f_4320_);
lean_closure_set(v___f_4327_, 3, v_a_4318_);
lean_closure_set(v___f_4327_, 4, v_inv_4268_);
lean_closure_set(v___f_4327_, 5, v_arg_4299_);
lean_closure_set(v___f_4327_, 6, v___x_4312_);
lean_closure_set(v___f_4327_, 7, v___x_4326_);
lean_closure_set(v___f_4327_, 8, v___x_4314_);
lean_closure_set(v___f_4327_, 9, v___x_4309_);
lean_closure_set(v___f_4327_, 10, v___x_4307_);
lean_closure_set(v___f_4327_, 11, v___x_4308_);
lean_closure_set(v___f_4327_, 12, v___x_4321_);
v___x_4328_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_inv_4268_, v___f_4327_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_);
return v___x_4328_;
}
}
}
}
}
}
v___jp_4282_:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; 
v___x_4291_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1, &l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1);
v___x_4292_ = l_Lean_MessageData_ofExpr(v_a_4281_);
v___x_4293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4293_, 0, v___x_4291_);
lean_ctor_set(v___x_4293_, 1, v___x_4292_);
v___x_4294_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v___x_4293_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
return v___x_4294_;
}
}
else
{
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
lean_dec(v_inv_4268_);
v_a_4344_ = lean_ctor_get(v___x_4278_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4278_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4346_ = v___x_4278_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v___x_4278_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_a_4344_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___boxed(lean_object* v_vcs_4352_, lean_object* v_inv_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l_Lean_Elab_Tactic_Do_suggestInvariant(v_vcs_4352_, v_inv_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_);
lean_dec(v_a_4361_);
lean_dec_ref(v_a_4360_);
lean_dec(v_a_4359_);
lean_dec_ref(v_a_4358_);
lean_dec(v_a_4357_);
lean_dec_ref(v_a_4356_);
lean_dec(v_a_4355_);
lean_dec_ref(v_a_4354_);
lean_dec_ref(v_vcs_4352_);
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(lean_object* v_00_u03b1_4364_, lean_object* v_msg_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_){
_start:
{
lean_object* v___x_4375_; 
v___x_4375_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4365_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___boxed(lean_object* v_00_u03b1_4376_, lean_object* v_msg_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_){
_start:
{
lean_object* v_res_4387_; 
v_res_4387_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(v_00_u03b1_4376_, v_msg_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
lean_dec(v___y_4385_);
lean_dec_ref(v___y_4384_);
lean_dec(v___y_4383_);
lean_dec_ref(v___y_4382_);
lean_dec(v___y_4381_);
lean_dec_ref(v___y_4380_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4378_);
return v_res_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(lean_object* v_00_u03b1_4388_, lean_object* v_name_4389_, uint8_t v_bi_4390_, lean_object* v_type_4391_, lean_object* v_k_4392_, uint8_t v_kind_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_){
_start:
{
lean_object* v___x_4403_; 
v___x_4403_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_4389_, v_bi_4390_, v_type_4391_, v_k_4392_, v_kind_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_);
return v___x_4403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4404_, lean_object* v_name_4405_, lean_object* v_bi_4406_, lean_object* v_type_4407_, lean_object* v_k_4408_, lean_object* v_kind_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
uint8_t v_bi_boxed_4419_; uint8_t v_kind_boxed_4420_; lean_object* v_res_4421_; 
v_bi_boxed_4419_ = lean_unbox(v_bi_4406_);
v_kind_boxed_4420_ = lean_unbox(v_kind_4409_);
v_res_4421_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(v_00_u03b1_4404_, v_name_4405_, v_bi_boxed_4419_, v_type_4407_, v_k_4408_, v_kind_boxed_4420_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
lean_dec(v___y_4417_);
lean_dec_ref(v___y_4416_);
lean_dec(v___y_4415_);
lean_dec_ref(v___y_4414_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
return v_res_4421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(lean_object* v_00_u03b1_4422_, lean_object* v_name_4423_, lean_object* v_type_4424_, lean_object* v_k_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
lean_object* v___x_4435_; 
v___x_4435_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_4423_, v_type_4424_, v_k_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___boxed(lean_object* v_00_u03b1_4436_, lean_object* v_name_4437_, lean_object* v_type_4438_, lean_object* v_k_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_){
_start:
{
lean_object* v_res_4449_; 
v_res_4449_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(v_00_u03b1_4436_, v_name_4437_, v_type_4438_, v_k_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4444_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
lean_dec(v___y_4441_);
lean_dec_ref(v___y_4440_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(lean_object* v_as_4450_, size_t v_sz_4451_, size_t v_i_4452_, lean_object* v_b_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
lean_object* v___x_4463_; 
v___x_4463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_4450_, v_sz_4451_, v_i_4452_, v_b_4453_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___boxed(lean_object* v_as_4464_, lean_object* v_sz_4465_, lean_object* v_i_4466_, lean_object* v_b_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
size_t v_sz_boxed_4477_; size_t v_i_boxed_4478_; lean_object* v_res_4479_; 
v_sz_boxed_4477_ = lean_unbox_usize(v_sz_4465_);
lean_dec(v_sz_4465_);
v_i_boxed_4478_ = lean_unbox_usize(v_i_4466_);
lean_dec(v_i_4466_);
v_res_4479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(v_as_4464_, v_sz_boxed_4477_, v_i_boxed_4478_, v_b_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
lean_dec(v___y_4471_);
lean_dec_ref(v___y_4470_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
lean_dec_ref(v_as_4464_);
return v_res_4479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(lean_object* v_as_4480_, size_t v_sz_4481_, size_t v_i_4482_, lean_object* v_b_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
lean_object* v___x_4493_; 
v___x_4493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_4480_, v_sz_4481_, v_i_4482_, v_b_4483_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
return v___x_4493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___boxed(lean_object* v_as_4494_, lean_object* v_sz_4495_, lean_object* v_i_4496_, lean_object* v_b_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
size_t v_sz_boxed_4507_; size_t v_i_boxed_4508_; lean_object* v_res_4509_; 
v_sz_boxed_4507_ = lean_unbox_usize(v_sz_4495_);
lean_dec(v_sz_4495_);
v_i_boxed_4508_ = lean_unbox_usize(v_i_4496_);
lean_dec(v_i_4496_);
v_res_4509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(v_as_4494_, v_sz_boxed_4507_, v_i_boxed_4508_, v_b_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
lean_dec_ref(v_as_4494_);
return v_res_4509_;
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
