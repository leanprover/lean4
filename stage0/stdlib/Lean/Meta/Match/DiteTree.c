// Lean compiler output
// Module: Lean.Meta.Match.DiteTree
// Imports: public import Lean.Meta.Basic import Lean.Meta.Tactic.Contradiction import Lean.Meta.Tactic.Subst import Lean.Meta.Tactic.Refl import Lean.Meta.Tactic.Replace import Lean.Meta.Tactic.Simp.Rewrite import Lean.Meta.Match.Value import Lean.Util.ForEachExpr
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
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_normMatchValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_normLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_whnfCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_modifyTargetEqLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGenDiseqFalseProof_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_isValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_isValue___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Float"};
static const lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 69, 114, 85, 163, 177, 220, 67)}};
static const lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Float32"};
static const lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 232, 182, 48, 64, 193, 160, 231)}};
static const lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___closed__3 = (const lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__0 = (const lean_object*)&l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_DiteTree_instInhabitedNode_default;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_instInhabitedNode;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__4___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_visit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_visit___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_visit_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0_spec__1(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1_spec__3_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__2_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ndrec_symm"};
static const lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 160, 179, 99, 219, 64, 47, 167)}};
static const lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__3;
static const lean_string_object l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "dite_ndrec_symm_eq"};
static const lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(194, 73, 54, 171, 152, 243, 9, 82)}};
static const lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_substKept_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_substKept_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_substKept(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_substKept___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visitSplit_spec__1___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visitSplit_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_whnfCore___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visit___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visitSplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visitSplit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visitSplit_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visitSplit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Match_splitDiteTree_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Match_splitDiteTree_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_splitDiteTree_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_splitDiteTree_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Match_splitDiteTree___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "equality expected"};
static const lean_object* l_Lean_Meta_Match_splitDiteTree___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Match_splitDiteTree___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Match_splitDiteTree___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_splitDiteTree___lam__0___closed__1;
static const lean_array_object l_Lean_Meta_Match_splitDiteTree___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Match_splitDiteTree___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Match_splitDiteTree___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Match_splitDiteTree___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "`dite (x = v) (Eq.ndrec_symm m) e` expected"};
static const lean_object* l_Lean_Meta_Match_splitDiteTree___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Match_splitDiteTree___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Match_splitDiteTree___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_splitDiteTree___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_splitDiteTree___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_splitDiteTree___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_splitDiteTree(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_splitDiteTree___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_splitDiteTree_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_splitDiteTree_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_isValue(lean_object* v_v_1_){
_start:
{
uint8_t v___x_2_; 
v___x_2_ = l_Lean_Expr_hasFVar(v_v_1_);
if (v___x_2_ == 0)
{
uint8_t v___x_3_; 
v___x_3_ = l_Lean_Expr_hasLooseBVars(v_v_1_);
if (v___x_3_ == 0)
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_v_1_);
if (v___x_4_ == 0)
{
uint8_t v___x_5_; 
v___x_5_ = 1;
return v___x_5_;
}
else
{
return v___x_3_;
}
}
else
{
return v___x_2_;
}
}
else
{
uint8_t v___x_6_; 
v___x_6_ = 0;
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_isValue___boxed(lean_object* v_v_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_isValue(v_v_7_);
lean_dec_ref(v_v_7_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___lam__0(lean_object* v_x_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_FVarId_getType___redArg(v_x_10_, v___y_11_, v___y_13_, v___y_14_);
if (lean_obj_tag(v___x_16_) == 0)
{
lean_object* v_a_17_; lean_object* v___x_18_; 
v_a_17_ = lean_ctor_get(v___x_16_, 0);
lean_inc(v_a_17_);
lean_dec_ref_known(v___x_16_, 1);
v___x_18_ = lean_whnf(v_a_17_, v___y_11_, v___y_12_, v___y_13_, v___y_14_);
return v___x_18_;
}
else
{
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
lean_dec(v___y_12_);
lean_dec_ref(v___y_11_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___lam__0___boxed(lean_object* v_x_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___lam__0(v_x_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest(lean_object* v_x_32_, lean_object* v_v_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v___y_59_; lean_object* v___x_91_; uint8_t v_transparency_92_; uint8_t v___x_93_; uint8_t v___x_94_; 
v___x_91_ = l_Lean_Meta_Context_config(v_a_34_);
v_transparency_92_ = lean_ctor_get_uint8(v___x_91_, 9);
lean_dec_ref(v___x_91_);
v___x_93_ = 5;
v___x_94_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_92_, v___x_93_);
if (v___x_94_ == 0)
{
lean_object* v_keyedConfig_95_; uint8_t v_trackZetaDelta_96_; lean_object* v_zetaDeltaSet_97_; lean_object* v_lctx_98_; lean_object* v_localInstances_99_; lean_object* v_defEqCtx_x3f_100_; lean_object* v_synthPendingDepth_101_; lean_object* v_customCanUnfoldPredicate_x3f_102_; uint8_t v_univApprox_103_; uint8_t v_inTypeClassResolution_104_; uint8_t v_cacheInferType_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_keyedConfig_95_ = lean_ctor_get(v_a_34_, 0);
v_trackZetaDelta_96_ = lean_ctor_get_uint8(v_a_34_, sizeof(void*)*7);
v_zetaDeltaSet_97_ = lean_ctor_get(v_a_34_, 1);
v_lctx_98_ = lean_ctor_get(v_a_34_, 2);
v_localInstances_99_ = lean_ctor_get(v_a_34_, 3);
v_defEqCtx_x3f_100_ = lean_ctor_get(v_a_34_, 4);
v_synthPendingDepth_101_ = lean_ctor_get(v_a_34_, 5);
v_customCanUnfoldPredicate_x3f_102_ = lean_ctor_get(v_a_34_, 6);
v_univApprox_103_ = lean_ctor_get_uint8(v_a_34_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_104_ = lean_ctor_get_uint8(v_a_34_, sizeof(void*)*7 + 2);
v_cacheInferType_105_ = lean_ctor_get_uint8(v_a_34_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_95_);
v___x_106_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_93_, v_keyedConfig_95_);
lean_inc(v_customCanUnfoldPredicate_x3f_102_);
lean_inc(v_synthPendingDepth_101_);
lean_inc(v_defEqCtx_x3f_100_);
lean_inc_ref(v_localInstances_99_);
lean_inc_ref(v_lctx_98_);
lean_inc(v_zetaDeltaSet_97_);
v___x_107_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v_zetaDeltaSet_97_);
lean_ctor_set(v___x_107_, 2, v_lctx_98_);
lean_ctor_set(v___x_107_, 3, v_localInstances_99_);
lean_ctor_set(v___x_107_, 4, v_defEqCtx_x3f_100_);
lean_ctor_set(v___x_107_, 5, v_synthPendingDepth_101_);
lean_ctor_set(v___x_107_, 6, v_customCanUnfoldPredicate_x3f_102_);
lean_ctor_set_uint8(v___x_107_, sizeof(void*)*7, v_trackZetaDelta_96_);
lean_ctor_set_uint8(v___x_107_, sizeof(void*)*7 + 1, v_univApprox_103_);
lean_ctor_set_uint8(v___x_107_, sizeof(void*)*7 + 2, v_inTypeClassResolution_104_);
lean_ctor_set_uint8(v___x_107_, sizeof(void*)*7 + 3, v_cacheInferType_105_);
lean_inc(v_a_37_);
lean_inc_ref(v_a_36_);
lean_inc(v_a_35_);
lean_inc(v_x_32_);
v___x_108_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___lam__0(v_x_32_, v___x_107_, v_a_35_, v_a_36_, v_a_37_);
v___y_59_ = v___x_108_;
goto v___jp_58_;
}
else
{
lean_object* v___x_109_; 
lean_inc(v_a_37_);
lean_inc_ref(v_a_36_);
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
lean_inc(v_x_32_);
v___x_109_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___lam__0(v_x_32_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
v___y_59_ = v___x_109_;
goto v___jp_58_;
}
v___jp_39_:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Meta_normMatchValue(v_v_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_40_) == 0)
{
lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_49_; 
v_a_41_ = lean_ctor_get(v___x_40_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_49_ == 0)
{
v___x_43_ = v___x_40_;
v_isShared_44_ = v_isSharedCheck_49_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_dec(v___x_40_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_49_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_45_; lean_object* v___x_47_; 
v___x_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_45_, 0, v_x_32_);
lean_ctor_set(v___x_45_, 1, v_a_41_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 0, v___x_45_);
v___x_47_ = v___x_43_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v___x_45_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
else
{
lean_object* v_a_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_57_; 
lean_dec(v_x_32_);
v_a_50_ = lean_ctor_get(v___x_40_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_57_ == 0)
{
v___x_52_ = v___x_40_;
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_a_50_);
lean_dec(v___x_40_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_55_; 
if (v_isShared_53_ == 0)
{
v___x_55_ = v___x_52_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_a_50_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
}
v___jp_58_:
{
if (lean_obj_tag(v___y_59_) == 0)
{
lean_object* v_a_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v_a_60_ = lean_ctor_get(v___y_59_, 0);
lean_inc(v_a_60_);
lean_dec_ref_known(v___y_59_, 1);
v___x_61_ = ((lean_object*)(l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___closed__1));
v___x_62_ = l_Lean_Expr_isConstOf(v_a_60_, v___x_61_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_63_ = ((lean_object*)(l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___closed__3));
v___x_64_ = l_Lean_Expr_isConstOf(v_a_60_, v___x_63_);
lean_dec(v_a_60_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Meta_normLitValue(v_v_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_74_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_74_ == 0)
{
v___x_68_ = v___x_65_;
v_isShared_69_ = v_isSharedCheck_74_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_a_66_);
lean_dec(v___x_65_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_74_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v_x_32_);
lean_ctor_set(v___x_70_, 1, v_a_66_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 0, v___x_70_);
v___x_72_ = v___x_68_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
else
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
lean_dec(v_x_32_);
v_a_75_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_65_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_65_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
else
{
goto v___jp_39_;
}
}
else
{
lean_dec(v_a_60_);
goto v___jp_39_;
}
}
else
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_90_; 
lean_dec_ref(v_v_33_);
lean_dec(v_x_32_);
v_a_83_ = lean_ctor_get(v___y_59_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v___y_59_);
if (v_isSharedCheck_90_ == 0)
{
v___x_85_ = v___y_59_;
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___y_59_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_a_83_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest___boxed(lean_object* v_x_110_, lean_object* v_v_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest(v_x_110_, v_v_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
return v_res_117_;
}
}
static lean_object* _init_l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__1(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_120_ = lean_box(0);
v___x_121_ = lean_unsigned_to_nat(16u);
v___x_122_ = lean_mk_array(v___x_121_, v___x_120_);
return v___x_122_;
}
}
static lean_object* _init_l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__2(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_123_ = lean_obj_once(&l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__1, &l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__1_once, _init_l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__1);
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v___x_123_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__3(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = lean_obj_once(&l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__2, &l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__2_once, _init_l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__2);
v___x_127_ = ((lean_object*)(l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__0));
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Meta_Match_DiteTree_instInhabitedNode_default(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__3, &l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__3_once, _init_l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__3);
return v___x_129_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_instInhabitedNode(void){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Meta_Match_DiteTree_instInhabitedNode_default;
return v___x_130_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0_spec__0___redArg(lean_object* v_a_131_, lean_object* v_x_132_){
_start:
{
if (lean_obj_tag(v_x_132_) == 0)
{
uint8_t v___x_133_; 
v___x_133_ = 0;
return v___x_133_;
}
else
{
lean_object* v_key_134_; lean_object* v_tail_135_; uint8_t v___x_136_; 
v_key_134_ = lean_ctor_get(v_x_132_, 0);
v_tail_135_ = lean_ctor_get(v_x_132_, 2);
v___x_136_ = l_Lean_instBEqFVarId_beq(v_key_134_, v_a_131_);
if (v___x_136_ == 0)
{
v_x_132_ = v_tail_135_;
goto _start;
}
else
{
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_138_, lean_object* v_x_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0_spec__0___redArg(v_a_138_, v_x_139_);
lean_dec(v_x_139_);
lean_dec(v_a_138_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0___redArg(lean_object* v_m_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_buckets_144_; lean_object* v___x_145_; uint64_t v___x_146_; uint64_t v___x_147_; uint64_t v___x_148_; uint64_t v_fold_149_; uint64_t v___x_150_; uint64_t v___x_151_; uint64_t v___x_152_; size_t v___x_153_; size_t v___x_154_; size_t v___x_155_; size_t v___x_156_; size_t v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v_buckets_144_ = lean_ctor_get(v_m_142_, 1);
v___x_145_ = lean_array_get_size(v_buckets_144_);
v___x_146_ = l_Lean_instHashableFVarId_hash(v_a_143_);
v___x_147_ = 32ULL;
v___x_148_ = lean_uint64_shift_right(v___x_146_, v___x_147_);
v_fold_149_ = lean_uint64_xor(v___x_146_, v___x_148_);
v___x_150_ = 16ULL;
v___x_151_ = lean_uint64_shift_right(v_fold_149_, v___x_150_);
v___x_152_ = lean_uint64_xor(v_fold_149_, v___x_151_);
v___x_153_ = lean_uint64_to_usize(v___x_152_);
v___x_154_ = lean_usize_of_nat(v___x_145_);
v___x_155_ = ((size_t)1ULL);
v___x_156_ = lean_usize_sub(v___x_154_, v___x_155_);
v___x_157_ = lean_usize_land(v___x_153_, v___x_156_);
v___x_158_ = lean_array_uget_borrowed(v_buckets_144_, v___x_157_);
v___x_159_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0_spec__0___redArg(v_a_143_, v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0___redArg___boxed(lean_object* v_m_160_, lean_object* v_a_161_){
_start:
{
uint8_t v_res_162_; lean_object* v_r_163_; 
v_res_162_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0___redArg(v_m_160_, v_a_161_);
lean_dec(v_a_161_);
lean_dec_ref(v_m_160_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__3___redArg(lean_object* v_a_164_, lean_object* v_b_165_, lean_object* v_x_166_){
_start:
{
if (lean_obj_tag(v_x_166_) == 0)
{
lean_dec(v_b_165_);
lean_dec(v_a_164_);
return v_x_166_;
}
else
{
lean_object* v_key_167_; lean_object* v_value_168_; lean_object* v_tail_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_181_; 
v_key_167_ = lean_ctor_get(v_x_166_, 0);
v_value_168_ = lean_ctor_get(v_x_166_, 1);
v_tail_169_ = lean_ctor_get(v_x_166_, 2);
v_isSharedCheck_181_ = !lean_is_exclusive(v_x_166_);
if (v_isSharedCheck_181_ == 0)
{
v___x_171_ = v_x_166_;
v_isShared_172_ = v_isSharedCheck_181_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_tail_169_);
lean_inc(v_value_168_);
lean_inc(v_key_167_);
lean_dec(v_x_166_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_181_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
uint8_t v___x_173_; 
v___x_173_ = l_Lean_instBEqFVarId_beq(v_key_167_, v_a_164_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_174_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__3___redArg(v_a_164_, v_b_165_, v_tail_169_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 2, v___x_174_);
v___x_176_ = v___x_171_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_key_167_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_value_168_);
lean_ctor_set(v_reuseFailAlloc_177_, 2, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
else
{
lean_object* v___x_179_; 
lean_dec(v_value_168_);
lean_dec(v_key_167_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 1, v_b_165_);
lean_ctor_set(v___x_171_, 0, v_a_164_);
v___x_179_ = v___x_171_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_164_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v_b_165_);
lean_ctor_set(v_reuseFailAlloc_180_, 2, v_tail_169_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
if (lean_obj_tag(v_x_183_) == 0)
{
return v_x_182_;
}
else
{
lean_object* v_key_184_; lean_object* v_value_185_; lean_object* v_tail_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_209_; 
v_key_184_ = lean_ctor_get(v_x_183_, 0);
v_value_185_ = lean_ctor_get(v_x_183_, 1);
v_tail_186_ = lean_ctor_get(v_x_183_, 2);
v_isSharedCheck_209_ = !lean_is_exclusive(v_x_183_);
if (v_isSharedCheck_209_ == 0)
{
v___x_188_ = v_x_183_;
v_isShared_189_ = v_isSharedCheck_209_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_tail_186_);
lean_inc(v_value_185_);
lean_inc(v_key_184_);
lean_dec(v_x_183_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_209_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; uint64_t v___x_191_; uint64_t v___x_192_; uint64_t v___x_193_; uint64_t v_fold_194_; uint64_t v___x_195_; uint64_t v___x_196_; uint64_t v___x_197_; size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; size_t v___x_201_; size_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_190_ = lean_array_get_size(v_x_182_);
v___x_191_ = l_Lean_instHashableFVarId_hash(v_key_184_);
v___x_192_ = 32ULL;
v___x_193_ = lean_uint64_shift_right(v___x_191_, v___x_192_);
v_fold_194_ = lean_uint64_xor(v___x_191_, v___x_193_);
v___x_195_ = 16ULL;
v___x_196_ = lean_uint64_shift_right(v_fold_194_, v___x_195_);
v___x_197_ = lean_uint64_xor(v_fold_194_, v___x_196_);
v___x_198_ = lean_uint64_to_usize(v___x_197_);
v___x_199_ = lean_usize_of_nat(v___x_190_);
v___x_200_ = ((size_t)1ULL);
v___x_201_ = lean_usize_sub(v___x_199_, v___x_200_);
v___x_202_ = lean_usize_land(v___x_198_, v___x_201_);
v___x_203_ = lean_array_uget_borrowed(v_x_182_, v___x_202_);
lean_inc(v___x_203_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 2, v___x_203_);
v___x_205_ = v___x_188_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_key_184_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_value_185_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v___x_203_);
v___x_205_ = v_reuseFailAlloc_208_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; 
v___x_206_ = lean_array_uset(v_x_182_, v___x_202_, v___x_205_);
v_x_182_ = v___x_206_;
v_x_183_ = v_tail_186_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__2_spec__3___redArg(lean_object* v_i_210_, lean_object* v_source_211_, lean_object* v_target_212_){
_start:
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = lean_array_get_size(v_source_211_);
v___x_214_ = lean_nat_dec_lt(v_i_210_, v___x_213_);
if (v___x_214_ == 0)
{
lean_dec_ref(v_source_211_);
lean_dec(v_i_210_);
return v_target_212_;
}
else
{
lean_object* v_es_215_; lean_object* v___x_216_; lean_object* v_source_217_; lean_object* v_target_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_es_215_ = lean_array_fget(v_source_211_, v_i_210_);
v___x_216_ = lean_box(0);
v_source_217_ = lean_array_fset(v_source_211_, v_i_210_, v___x_216_);
v_target_218_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__2_spec__3_spec__4___redArg(v_target_212_, v_es_215_);
v___x_219_ = lean_unsigned_to_nat(1u);
v___x_220_ = lean_nat_add(v_i_210_, v___x_219_);
lean_dec(v_i_210_);
v_i_210_ = v___x_220_;
v_source_211_ = v_source_217_;
v_target_212_ = v_target_218_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__2___redArg(lean_object* v_data_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v_nbuckets_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_223_ = lean_array_get_size(v_data_222_);
v___x_224_ = lean_unsigned_to_nat(2u);
v_nbuckets_225_ = lean_nat_mul(v___x_223_, v___x_224_);
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = lean_box(0);
v___x_228_ = lean_mk_array(v_nbuckets_225_, v___x_227_);
v___x_229_ = lean_array_propagate_mark(v_data_222_, v___x_228_);
v___x_230_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__2_spec__3___redArg(v___x_226_, v_data_222_, v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1___redArg(lean_object* v_m_231_, lean_object* v_a_232_, lean_object* v_b_233_){
_start:
{
lean_object* v_size_234_; lean_object* v_buckets_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_278_; 
v_size_234_ = lean_ctor_get(v_m_231_, 0);
v_buckets_235_ = lean_ctor_get(v_m_231_, 1);
v_isSharedCheck_278_ = !lean_is_exclusive(v_m_231_);
if (v_isSharedCheck_278_ == 0)
{
v___x_237_ = v_m_231_;
v_isShared_238_ = v_isSharedCheck_278_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_buckets_235_);
lean_inc(v_size_234_);
lean_dec(v_m_231_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_278_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; uint64_t v___x_240_; uint64_t v___x_241_; uint64_t v___x_242_; uint64_t v_fold_243_; uint64_t v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; size_t v___x_247_; size_t v___x_248_; size_t v___x_249_; size_t v___x_250_; size_t v___x_251_; lean_object* v_bkt_252_; uint8_t v___x_253_; 
v___x_239_ = lean_array_get_size(v_buckets_235_);
v___x_240_ = l_Lean_instHashableFVarId_hash(v_a_232_);
v___x_241_ = 32ULL;
v___x_242_ = lean_uint64_shift_right(v___x_240_, v___x_241_);
v_fold_243_ = lean_uint64_xor(v___x_240_, v___x_242_);
v___x_244_ = 16ULL;
v___x_245_ = lean_uint64_shift_right(v_fold_243_, v___x_244_);
v___x_246_ = lean_uint64_xor(v_fold_243_, v___x_245_);
v___x_247_ = lean_uint64_to_usize(v___x_246_);
v___x_248_ = lean_usize_of_nat(v___x_239_);
v___x_249_ = ((size_t)1ULL);
v___x_250_ = lean_usize_sub(v___x_248_, v___x_249_);
v___x_251_ = lean_usize_land(v___x_247_, v___x_250_);
v_bkt_252_ = lean_array_uget_borrowed(v_buckets_235_, v___x_251_);
v___x_253_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0_spec__0___redArg(v_a_232_, v_bkt_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v_size_x27_255_; lean_object* v___x_256_; lean_object* v_buckets_x27_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_254_ = lean_unsigned_to_nat(1u);
v_size_x27_255_ = lean_nat_add(v_size_234_, v___x_254_);
lean_dec(v_size_234_);
lean_inc(v_bkt_252_);
v___x_256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_256_, 0, v_a_232_);
lean_ctor_set(v___x_256_, 1, v_b_233_);
lean_ctor_set(v___x_256_, 2, v_bkt_252_);
v_buckets_x27_257_ = lean_array_uset(v_buckets_235_, v___x_251_, v___x_256_);
v___x_258_ = lean_unsigned_to_nat(4u);
v___x_259_ = lean_nat_mul(v_size_x27_255_, v___x_258_);
v___x_260_ = lean_unsigned_to_nat(3u);
v___x_261_ = lean_nat_div(v___x_259_, v___x_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_array_get_size(v_buckets_x27_257_);
v___x_263_ = lean_nat_dec_le(v___x_261_, v___x_262_);
lean_dec(v___x_261_);
if (v___x_263_ == 0)
{
lean_object* v_val_264_; lean_object* v___x_266_; 
v_val_264_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__2___redArg(v_buckets_x27_257_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v_val_264_);
lean_ctor_set(v___x_237_, 0, v_size_x27_255_);
v___x_266_ = v___x_237_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_size_x27_255_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v_val_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
else
{
lean_object* v___x_269_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v_buckets_x27_257_);
lean_ctor_set(v___x_237_, 0, v_size_x27_255_);
v___x_269_ = v___x_237_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_size_x27_255_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_buckets_x27_257_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
else
{
lean_object* v___x_271_; lean_object* v_buckets_x27_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
lean_inc(v_bkt_252_);
v___x_271_ = lean_box(0);
v_buckets_x27_272_ = lean_array_uset(v_buckets_235_, v___x_251_, v___x_271_);
v___x_273_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__3___redArg(v_a_232_, v_b_233_, v_bkt_252_);
v___x_274_ = lean_array_uset(v_buckets_x27_272_, v___x_251_, v___x_273_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v___x_274_);
v___x_276_ = v___x_237_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_size_234_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg(lean_object* v_e_285_, lean_object* v_a_286_){
_start:
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = l_Lean_Expr_cleanupAnnotations(v_e_285_);
v___x_295_ = l_Lean_Expr_isApp(v___x_294_);
if (v___x_295_ == 0)
{
lean_dec_ref(v___x_294_);
goto v___jp_291_;
}
else
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = l_Lean_Expr_appFnCleanup___redArg(v___x_294_);
lean_dec_ref(v___x_294_);
v___x_297_ = l_Lean_Expr_isApp(v___x_296_);
if (v___x_297_ == 0)
{
lean_dec_ref(v___x_296_);
goto v___jp_291_;
}
else
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = l_Lean_Expr_appFnCleanup___redArg(v___x_296_);
lean_dec_ref(v___x_296_);
v___x_299_ = l_Lean_Expr_isApp(v___x_298_);
if (v___x_299_ == 0)
{
lean_dec_ref(v___x_298_);
goto v___jp_291_;
}
else
{
lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_300_ = l_Lean_Expr_appFnCleanup___redArg(v___x_298_);
lean_dec_ref(v___x_298_);
v___x_301_ = l_Lean_Expr_isApp(v___x_300_);
if (v___x_301_ == 0)
{
lean_dec_ref(v___x_300_);
goto v___jp_291_;
}
else
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = l_Lean_Expr_appFnCleanup___redArg(v___x_300_);
v___x_303_ = l_Lean_Expr_isApp(v___x_302_);
if (v___x_303_ == 0)
{
lean_dec_ref(v___x_302_);
lean_dec_ref(v___x_300_);
goto v___jp_291_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_304_ = l_Lean_Expr_appFnCleanup___redArg(v___x_302_);
lean_dec_ref(v___x_302_);
v___x_305_ = ((lean_object*)(l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__1));
v___x_306_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_305_);
lean_dec_ref(v___x_304_);
if (v___x_306_ == 0)
{
lean_dec_ref(v___x_300_);
goto v___jp_291_;
}
else
{
lean_object* v_arg_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v_arg_307_ = lean_ctor_get(v___x_300_, 1);
lean_inc_ref(v_arg_307_);
lean_dec_ref(v___x_300_);
v___x_308_ = l_Lean_Expr_cleanupAnnotations(v_arg_307_);
lean_dec_ref(v_arg_307_);
v___x_309_ = l_Lean_Expr_isApp(v___x_308_);
if (v___x_309_ == 0)
{
lean_dec_ref(v___x_308_);
goto v___jp_288_;
}
else
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = l_Lean_Expr_appFnCleanup___redArg(v___x_308_);
v___x_311_ = l_Lean_Expr_isApp(v___x_310_);
if (v___x_311_ == 0)
{
lean_dec_ref(v___x_310_);
lean_dec_ref(v___x_308_);
goto v___jp_288_;
}
else
{
lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_312_ = l_Lean_Expr_appFnCleanup___redArg(v___x_310_);
v___x_313_ = l_Lean_Expr_isApp(v___x_312_);
if (v___x_313_ == 0)
{
lean_dec_ref(v___x_312_);
lean_dec_ref(v___x_310_);
lean_dec_ref(v___x_308_);
goto v___jp_288_;
}
else
{
lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_314_ = l_Lean_Expr_appFnCleanup___redArg(v___x_312_);
lean_dec_ref(v___x_312_);
v___x_315_ = ((lean_object*)(l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__3));
v___x_316_ = l_Lean_Expr_isConstOf(v___x_314_, v___x_315_);
lean_dec_ref(v___x_314_);
if (v___x_316_ == 0)
{
lean_dec_ref(v___x_310_);
lean_dec_ref(v___x_308_);
goto v___jp_288_;
}
else
{
lean_object* v_arg_317_; 
v_arg_317_ = lean_ctor_get(v___x_310_, 1);
lean_inc_ref(v_arg_317_);
lean_dec_ref(v___x_310_);
if (lean_obj_tag(v_arg_317_) == 1)
{
lean_object* v_fvarId_318_; lean_object* v_arg_319_; uint8_t v___x_320_; 
v_fvarId_318_ = lean_ctor_get(v_arg_317_, 0);
lean_inc(v_fvarId_318_);
lean_dec_ref_known(v_arg_317_, 1);
v_arg_319_ = lean_ctor_get(v___x_308_, 1);
lean_inc_ref(v_arg_319_);
lean_dec_ref(v___x_308_);
v___x_320_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_isValue(v_arg_319_);
lean_dec_ref(v_arg_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec(v_fvarId_318_);
v___x_321_ = lean_box(0);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
else
{
lean_object* v___x_323_; lean_object* v_fst_325_; lean_object* v_snd_326_; lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_323_ = lean_st_ref_take(v_a_286_);
v___x_329_ = lean_box(0);
v___x_330_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0___redArg(v___x_323_, v_fvarId_318_);
if (v___x_330_ == 0)
{
lean_object* v_size_331_; lean_object* v___x_332_; 
v_size_331_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_size_331_);
v___x_332_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1___redArg(v___x_323_, v_fvarId_318_, v_size_331_);
v_fst_325_ = v___x_329_;
v_snd_326_ = v___x_332_;
goto v___jp_324_;
}
else
{
lean_dec(v_fvarId_318_);
v_fst_325_ = v___x_329_;
v_snd_326_ = v___x_323_;
goto v___jp_324_;
}
v___jp_324_:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_st_ref_put(v_a_286_, v_snd_326_);
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v_fst_325_);
return v___x_328_;
}
}
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec_ref(v_arg_317_);
lean_dec_ref(v___x_308_);
v___x_333_ = lean_box(0);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
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
v___jp_288_:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_box(0);
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
v___jp_291_:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_box(0);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___boxed(lean_object* v_e_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg(v_e_335_, v_a_336_);
lean_dec(v_a_336_);
lean_dec_ref(v_e_335_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit(lean_object* v_e_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg(v_e_339_, v_a_340_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___boxed(lean_object* v_e_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit(v_e_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec(v_a_348_);
lean_dec_ref(v_e_347_);
return v_res_354_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0(lean_object* v_00_u03b2_355_, lean_object* v_m_356_, lean_object* v_a_357_){
_start:
{
uint8_t v___x_358_; 
v___x_358_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0___redArg(v_m_356_, v_a_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0___boxed(lean_object* v_00_u03b2_359_, lean_object* v_m_360_, lean_object* v_a_361_){
_start:
{
uint8_t v_res_362_; lean_object* v_r_363_; 
v_res_362_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0(v_00_u03b2_359_, v_m_360_, v_a_361_);
lean_dec(v_a_361_);
lean_dec_ref(v_m_360_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1(lean_object* v_00_u03b2_364_, lean_object* v_m_365_, lean_object* v_a_366_, lean_object* v_b_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1___redArg(v_m_365_, v_a_366_, v_b_367_);
return v___x_368_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0_spec__0(lean_object* v_00_u03b2_369_, lean_object* v_a_370_, lean_object* v_x_371_){
_start:
{
uint8_t v___x_372_; 
v___x_372_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0_spec__0___redArg(v_a_370_, v_x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_373_, lean_object* v_a_374_, lean_object* v_x_375_){
_start:
{
uint8_t v_res_376_; lean_object* v_r_377_; 
v_res_376_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0_spec__0(v_00_u03b2_373_, v_a_374_, v_x_375_);
lean_dec(v_x_375_);
lean_dec(v_a_374_);
v_r_377_ = lean_box(v_res_376_);
return v_r_377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__2(lean_object* v_00_u03b2_378_, lean_object* v_data_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__2___redArg(v_data_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__3(lean_object* v_00_u03b2_381_, lean_object* v_a_382_, lean_object* v_b_383_, lean_object* v_x_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__3___redArg(v_a_382_, v_b_383_, v_x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_386_, lean_object* v_i_387_, lean_object* v_source_388_, lean_object* v_target_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__2_spec__3___redArg(v_i_387_, v_source_388_, v_target_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_391_, lean_object* v_x_392_, lean_object* v_x_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__1_spec__2_spec__3_spec__4___redArg(v_x_392_, v_x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___lam__0(lean_object* v_e_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_411_; 
v___x_402_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg(v_e_395_, v___y_396_);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; 
v_unused_412_ = lean_ctor_get(v___x_402_, 0);
lean_dec(v_unused_412_);
v___x_404_ = v___x_402_;
v_isShared_405_ = v_isSharedCheck_411_;
goto v_resetjp_403_;
}
else
{
lean_dec(v___x_402_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_411_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_406_ = 1;
v___x_407_ = lean_box(v___x_406_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_407_);
v___x_409_ = v___x_404_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___lam__0___boxed(lean_object* v_e_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___lam__0(v_e_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v_e_413_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0_spec__1___redArg(lean_object* v_a_421_, lean_object* v_x_422_){
_start:
{
if (lean_obj_tag(v_x_422_) == 0)
{
lean_object* v___x_423_; 
v___x_423_ = lean_box(0);
return v___x_423_;
}
else
{
lean_object* v_key_424_; lean_object* v_value_425_; lean_object* v_tail_426_; uint8_t v___x_427_; 
v_key_424_ = lean_ctor_get(v_x_422_, 0);
v_value_425_ = lean_ctor_get(v_x_422_, 1);
v_tail_426_ = lean_ctor_get(v_x_422_, 2);
v___x_427_ = lean_expr_eqv(v_key_424_, v_a_421_);
if (v___x_427_ == 0)
{
v_x_422_ = v_tail_426_;
goto _start;
}
else
{
lean_object* v___x_429_; 
lean_inc(v_value_425_);
v___x_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_429_, 0, v_value_425_);
return v___x_429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_430_, lean_object* v_x_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0_spec__1___redArg(v_a_430_, v_x_431_);
lean_dec(v_x_431_);
lean_dec_ref(v_a_430_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0___redArg(lean_object* v_m_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_buckets_435_; lean_object* v___x_436_; uint64_t v___x_437_; uint64_t v___x_438_; uint64_t v___x_439_; uint64_t v_fold_440_; uint64_t v___x_441_; uint64_t v___x_442_; uint64_t v___x_443_; size_t v___x_444_; size_t v___x_445_; size_t v___x_446_; size_t v___x_447_; size_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_buckets_435_ = lean_ctor_get(v_m_433_, 1);
v___x_436_ = lean_array_get_size(v_buckets_435_);
v___x_437_ = l_Lean_Expr_hash(v_a_434_);
v___x_438_ = 32ULL;
v___x_439_ = lean_uint64_shift_right(v___x_437_, v___x_438_);
v_fold_440_ = lean_uint64_xor(v___x_437_, v___x_439_);
v___x_441_ = 16ULL;
v___x_442_ = lean_uint64_shift_right(v_fold_440_, v___x_441_);
v___x_443_ = lean_uint64_xor(v_fold_440_, v___x_442_);
v___x_444_ = lean_uint64_to_usize(v___x_443_);
v___x_445_ = lean_usize_of_nat(v___x_436_);
v___x_446_ = ((size_t)1ULL);
v___x_447_ = lean_usize_sub(v___x_445_, v___x_446_);
v___x_448_ = lean_usize_land(v___x_444_, v___x_447_);
v___x_449_ = lean_array_uget_borrowed(v_buckets_435_, v___x_448_);
v___x_450_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0_spec__1___redArg(v_a_434_, v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0___redArg___boxed(lean_object* v_m_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0___redArg(v_m_451_, v_a_452_);
lean_dec_ref(v_a_452_);
lean_dec_ref(v_m_451_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
if (lean_obj_tag(v_x_455_) == 0)
{
return v_x_454_;
}
else
{
lean_object* v_key_456_; lean_object* v_value_457_; lean_object* v_tail_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_481_; 
v_key_456_ = lean_ctor_get(v_x_455_, 0);
v_value_457_ = lean_ctor_get(v_x_455_, 1);
v_tail_458_ = lean_ctor_get(v_x_455_, 2);
v_isSharedCheck_481_ = !lean_is_exclusive(v_x_455_);
if (v_isSharedCheck_481_ == 0)
{
v___x_460_ = v_x_455_;
v_isShared_461_ = v_isSharedCheck_481_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_tail_458_);
lean_inc(v_value_457_);
lean_inc(v_key_456_);
lean_dec(v_x_455_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_481_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; uint64_t v___x_463_; uint64_t v___x_464_; uint64_t v___x_465_; uint64_t v_fold_466_; uint64_t v___x_467_; uint64_t v___x_468_; uint64_t v___x_469_; size_t v___x_470_; size_t v___x_471_; size_t v___x_472_; size_t v___x_473_; size_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_462_ = lean_array_get_size(v_x_454_);
v___x_463_ = l_Lean_Expr_hash(v_key_456_);
v___x_464_ = 32ULL;
v___x_465_ = lean_uint64_shift_right(v___x_463_, v___x_464_);
v_fold_466_ = lean_uint64_xor(v___x_463_, v___x_465_);
v___x_467_ = 16ULL;
v___x_468_ = lean_uint64_shift_right(v_fold_466_, v___x_467_);
v___x_469_ = lean_uint64_xor(v_fold_466_, v___x_468_);
v___x_470_ = lean_uint64_to_usize(v___x_469_);
v___x_471_ = lean_usize_of_nat(v___x_462_);
v___x_472_ = ((size_t)1ULL);
v___x_473_ = lean_usize_sub(v___x_471_, v___x_472_);
v___x_474_ = lean_usize_land(v___x_470_, v___x_473_);
v___x_475_ = lean_array_uget_borrowed(v_x_454_, v___x_474_);
lean_inc(v___x_475_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 2, v___x_475_);
v___x_477_ = v___x_460_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_key_456_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_value_457_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v___x_475_);
v___x_477_ = v_reuseFailAlloc_480_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_478_; 
v___x_478_ = lean_array_uset(v_x_454_, v___x_474_, v___x_477_);
v_x_454_ = v___x_478_;
v_x_455_ = v_tail_458_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__4_spec__5___redArg(lean_object* v_i_482_, lean_object* v_source_483_, lean_object* v_target_484_){
_start:
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = lean_array_get_size(v_source_483_);
v___x_486_ = lean_nat_dec_lt(v_i_482_, v___x_485_);
if (v___x_486_ == 0)
{
lean_dec_ref(v_source_483_);
lean_dec(v_i_482_);
return v_target_484_;
}
else
{
lean_object* v_es_487_; lean_object* v___x_488_; lean_object* v_source_489_; lean_object* v_target_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_es_487_ = lean_array_fget(v_source_483_, v_i_482_);
v___x_488_ = lean_box(0);
v_source_489_ = lean_array_fset(v_source_483_, v_i_482_, v___x_488_);
v_target_490_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_target_484_, v_es_487_);
v___x_491_ = lean_unsigned_to_nat(1u);
v___x_492_ = lean_nat_add(v_i_482_, v___x_491_);
lean_dec(v_i_482_);
v_i_482_ = v___x_492_;
v_source_483_ = v_source_489_;
v_target_484_ = v_target_490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__4___redArg(lean_object* v_data_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v_nbuckets_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_495_ = lean_array_get_size(v_data_494_);
v___x_496_ = lean_unsigned_to_nat(2u);
v_nbuckets_497_ = lean_nat_mul(v___x_495_, v___x_496_);
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = lean_box(0);
v___x_500_ = lean_mk_array(v_nbuckets_497_, v___x_499_);
v___x_501_ = lean_array_propagate_mark(v_data_494_, v___x_500_);
v___x_502_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__4_spec__5___redArg(v___x_498_, v_data_494_, v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__3___redArg(lean_object* v_a_503_, lean_object* v_x_504_){
_start:
{
if (lean_obj_tag(v_x_504_) == 0)
{
uint8_t v___x_505_; 
v___x_505_ = 0;
return v___x_505_;
}
else
{
lean_object* v_key_506_; lean_object* v_tail_507_; uint8_t v___x_508_; 
v_key_506_ = lean_ctor_get(v_x_504_, 0);
v_tail_507_ = lean_ctor_get(v_x_504_, 2);
v___x_508_ = lean_expr_eqv(v_key_506_, v_a_503_);
if (v___x_508_ == 0)
{
v_x_504_ = v_tail_507_;
goto _start;
}
else
{
return v___x_508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_510_, lean_object* v_x_511_){
_start:
{
uint8_t v_res_512_; lean_object* v_r_513_; 
v_res_512_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__3___redArg(v_a_510_, v_x_511_);
lean_dec(v_x_511_);
lean_dec_ref(v_a_510_);
v_r_513_ = lean_box(v_res_512_);
return v_r_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__5___redArg(lean_object* v_a_514_, lean_object* v_b_515_, lean_object* v_x_516_){
_start:
{
if (lean_obj_tag(v_x_516_) == 0)
{
lean_dec(v_b_515_);
lean_dec_ref(v_a_514_);
return v_x_516_;
}
else
{
lean_object* v_key_517_; lean_object* v_value_518_; lean_object* v_tail_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_531_; 
v_key_517_ = lean_ctor_get(v_x_516_, 0);
v_value_518_ = lean_ctor_get(v_x_516_, 1);
v_tail_519_ = lean_ctor_get(v_x_516_, 2);
v_isSharedCheck_531_ = !lean_is_exclusive(v_x_516_);
if (v_isSharedCheck_531_ == 0)
{
v___x_521_ = v_x_516_;
v_isShared_522_ = v_isSharedCheck_531_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_tail_519_);
lean_inc(v_value_518_);
lean_inc(v_key_517_);
lean_dec(v_x_516_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_531_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
uint8_t v___x_523_; 
v___x_523_ = lean_expr_eqv(v_key_517_, v_a_514_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_524_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__5___redArg(v_a_514_, v_b_515_, v_tail_519_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 2, v___x_524_);
v___x_526_ = v___x_521_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_key_517_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_value_518_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
else
{
lean_object* v___x_529_; 
lean_dec(v_value_518_);
lean_dec(v_key_517_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v_b_515_);
lean_ctor_set(v___x_521_, 0, v_a_514_);
v___x_529_ = v___x_521_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_514_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_b_515_);
lean_ctor_set(v_reuseFailAlloc_530_, 2, v_tail_519_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1___redArg(lean_object* v_m_532_, lean_object* v_a_533_, lean_object* v_b_534_){
_start:
{
lean_object* v_size_535_; lean_object* v_buckets_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_579_; 
v_size_535_ = lean_ctor_get(v_m_532_, 0);
v_buckets_536_ = lean_ctor_get(v_m_532_, 1);
v_isSharedCheck_579_ = !lean_is_exclusive(v_m_532_);
if (v_isSharedCheck_579_ == 0)
{
v___x_538_ = v_m_532_;
v_isShared_539_ = v_isSharedCheck_579_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_buckets_536_);
lean_inc(v_size_535_);
lean_dec(v_m_532_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_579_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; uint64_t v___x_541_; uint64_t v___x_542_; uint64_t v___x_543_; uint64_t v_fold_544_; uint64_t v___x_545_; uint64_t v___x_546_; uint64_t v___x_547_; size_t v___x_548_; size_t v___x_549_; size_t v___x_550_; size_t v___x_551_; size_t v___x_552_; lean_object* v_bkt_553_; uint8_t v___x_554_; 
v___x_540_ = lean_array_get_size(v_buckets_536_);
v___x_541_ = l_Lean_Expr_hash(v_a_533_);
v___x_542_ = 32ULL;
v___x_543_ = lean_uint64_shift_right(v___x_541_, v___x_542_);
v_fold_544_ = lean_uint64_xor(v___x_541_, v___x_543_);
v___x_545_ = 16ULL;
v___x_546_ = lean_uint64_shift_right(v_fold_544_, v___x_545_);
v___x_547_ = lean_uint64_xor(v_fold_544_, v___x_546_);
v___x_548_ = lean_uint64_to_usize(v___x_547_);
v___x_549_ = lean_usize_of_nat(v___x_540_);
v___x_550_ = ((size_t)1ULL);
v___x_551_ = lean_usize_sub(v___x_549_, v___x_550_);
v___x_552_ = lean_usize_land(v___x_548_, v___x_551_);
v_bkt_553_ = lean_array_uget_borrowed(v_buckets_536_, v___x_552_);
v___x_554_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__3___redArg(v_a_533_, v_bkt_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v_size_x27_556_; lean_object* v___x_557_; lean_object* v_buckets_x27_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_555_ = lean_unsigned_to_nat(1u);
v_size_x27_556_ = lean_nat_add(v_size_535_, v___x_555_);
lean_dec(v_size_535_);
lean_inc(v_bkt_553_);
v___x_557_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_557_, 0, v_a_533_);
lean_ctor_set(v___x_557_, 1, v_b_534_);
lean_ctor_set(v___x_557_, 2, v_bkt_553_);
v_buckets_x27_558_ = lean_array_uset(v_buckets_536_, v___x_552_, v___x_557_);
v___x_559_ = lean_unsigned_to_nat(4u);
v___x_560_ = lean_nat_mul(v_size_x27_556_, v___x_559_);
v___x_561_ = lean_unsigned_to_nat(3u);
v___x_562_ = lean_nat_div(v___x_560_, v___x_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_array_get_size(v_buckets_x27_558_);
v___x_564_ = lean_nat_dec_le(v___x_562_, v___x_563_);
lean_dec(v___x_562_);
if (v___x_564_ == 0)
{
lean_object* v_val_565_; lean_object* v___x_567_; 
v_val_565_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__4___redArg(v_buckets_x27_558_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v_val_565_);
lean_ctor_set(v___x_538_, 0, v_size_x27_556_);
v___x_567_ = v___x_538_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_size_x27_556_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_val_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
else
{
lean_object* v___x_570_; 
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v_buckets_x27_558_);
lean_ctor_set(v___x_538_, 0, v_size_x27_556_);
v___x_570_ = v___x_538_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_size_x27_556_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_buckets_x27_558_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
else
{
lean_object* v___x_572_; lean_object* v_buckets_x27_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
lean_inc(v_bkt_553_);
v___x_572_ = lean_box(0);
v_buckets_x27_573_ = lean_array_uset(v_buckets_536_, v___x_552_, v___x_572_);
v___x_574_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__5___redArg(v_a_533_, v_b_534_, v_bkt_553_);
v___x_575_ = lean_array_uset(v_buckets_x27_573_, v___x_552_, v___x_574_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v___x_575_);
v___x_577_ = v___x_538_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_size_535_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0(lean_object* v_g_580_, lean_object* v_e_581_, lean_object* v_a_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_a_590_; lean_object* v___y_596_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_st_ref_get(v_a_582_);
v___x_599_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0___redArg(v___x_598_, v_e_581_);
lean_dec(v___x_598_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v___x_600_; 
lean_inc_ref(v_g_580_);
lean_inc(v___y_587_);
lean_inc_ref(v___y_586_);
lean_inc(v___y_585_);
lean_inc_ref(v___y_584_);
lean_inc(v___y_583_);
lean_inc_ref(v_e_581_);
v___x_600_ = lean_apply_7(v_g_580_, v_e_581_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, lean_box(0));
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v_d_603_; lean_object* v_b_604_; lean_object* v___y_605_; uint8_t v___x_608_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
v___x_608_ = lean_unbox(v_a_601_);
lean_dec(v_a_601_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; 
lean_dec_ref(v_g_580_);
v___x_609_ = lean_box(0);
v_a_590_ = v___x_609_;
goto v___jp_589_;
}
else
{
switch(lean_obj_tag(v_e_581_))
{
case 7:
{
lean_object* v_binderType_610_; lean_object* v_body_611_; 
v_binderType_610_ = lean_ctor_get(v_e_581_, 1);
v_body_611_ = lean_ctor_get(v_e_581_, 2);
lean_inc_ref(v_body_611_);
lean_inc_ref(v_binderType_610_);
v_d_603_ = v_binderType_610_;
v_b_604_ = v_body_611_;
v___y_605_ = v_a_582_;
goto v___jp_602_;
}
case 6:
{
lean_object* v_binderType_612_; lean_object* v_body_613_; 
v_binderType_612_ = lean_ctor_get(v_e_581_, 1);
v_body_613_ = lean_ctor_get(v_e_581_, 2);
lean_inc_ref(v_body_613_);
lean_inc_ref(v_binderType_612_);
v_d_603_ = v_binderType_612_;
v_b_604_ = v_body_613_;
v___y_605_ = v_a_582_;
goto v___jp_602_;
}
case 8:
{
lean_object* v_type_614_; lean_object* v_value_615_; lean_object* v_body_616_; lean_object* v___x_617_; 
v_type_614_ = lean_ctor_get(v_e_581_, 1);
v_value_615_ = lean_ctor_get(v_e_581_, 2);
v_body_616_ = lean_ctor_get(v_e_581_, 3);
lean_inc_ref(v_type_614_);
lean_inc_ref(v_g_580_);
v___x_617_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0(v_g_580_, v_type_614_, v_a_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v___x_618_; 
lean_dec_ref_known(v___x_617_, 1);
lean_inc_ref(v_value_615_);
lean_inc_ref(v_g_580_);
v___x_618_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0(v_g_580_, v_value_615_, v_a_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v___x_619_; 
lean_dec_ref_known(v___x_618_, 1);
lean_inc_ref(v_body_616_);
v___x_619_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0(v_g_580_, v_body_616_, v_a_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
v___y_596_ = v___x_619_;
goto v___jp_595_;
}
else
{
lean_dec_ref_known(v_e_581_, 4);
lean_dec_ref(v_g_580_);
return v___x_618_;
}
}
else
{
lean_dec_ref_known(v_e_581_, 4);
lean_dec_ref(v_g_580_);
return v___x_617_;
}
}
case 5:
{
lean_object* v_fn_620_; lean_object* v_arg_621_; lean_object* v___x_622_; 
v_fn_620_ = lean_ctor_get(v_e_581_, 0);
v_arg_621_ = lean_ctor_get(v_e_581_, 1);
lean_inc_ref(v_fn_620_);
lean_inc_ref(v_g_580_);
v___x_622_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0(v_g_580_, v_fn_620_, v_a_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v___x_623_; 
lean_dec_ref_known(v___x_622_, 1);
lean_inc_ref(v_arg_621_);
v___x_623_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0(v_g_580_, v_arg_621_, v_a_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
v___y_596_ = v___x_623_;
goto v___jp_595_;
}
else
{
lean_dec_ref_known(v_e_581_, 2);
lean_dec_ref(v_g_580_);
return v___x_622_;
}
}
case 10:
{
lean_object* v_expr_624_; lean_object* v___x_625_; 
v_expr_624_ = lean_ctor_get(v_e_581_, 1);
lean_inc_ref(v_expr_624_);
v___x_625_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0(v_g_580_, v_expr_624_, v_a_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
v___y_596_ = v___x_625_;
goto v___jp_595_;
}
case 11:
{
lean_object* v_struct_626_; lean_object* v___x_627_; 
v_struct_626_ = lean_ctor_get(v_e_581_, 2);
lean_inc_ref(v_struct_626_);
v___x_627_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0(v_g_580_, v_struct_626_, v_a_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
v___y_596_ = v___x_627_;
goto v___jp_595_;
}
default: 
{
lean_object* v___x_628_; 
lean_dec_ref(v_g_580_);
v___x_628_ = lean_box(0);
v_a_590_ = v___x_628_;
goto v___jp_589_;
}
}
}
v___jp_602_:
{
lean_object* v___x_606_; 
lean_inc_ref(v_g_580_);
v___x_606_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0(v_g_580_, v_d_603_, v___y_605_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v___x_607_; 
lean_dec_ref_known(v___x_606_, 1);
v___x_607_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0(v_g_580_, v_b_604_, v___y_605_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
v___y_596_ = v___x_607_;
goto v___jp_595_;
}
else
{
lean_dec_ref(v_b_604_);
lean_dec_ref(v_e_581_);
lean_dec_ref(v_g_580_);
return v___x_606_;
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec_ref(v_e_581_);
lean_dec_ref(v_g_580_);
v_a_629_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_600_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_600_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
else
{
lean_object* v_val_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec_ref(v_e_581_);
lean_dec_ref(v_g_580_);
v_val_637_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_599_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_val_637_);
lean_dec(v___x_599_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set_tag(v___x_639_, 0);
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_val_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
v___jp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_591_ = lean_st_ref_take(v_a_582_);
v___x_592_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1___redArg(v___x_591_, v_e_581_, v_a_590_);
v___x_593_ = lean_st_ref_put(v_a_582_, v___x_592_);
v___x_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_594_, 0, v_a_590_);
return v___x_594_;
}
v___jp_595_:
{
if (lean_obj_tag(v___y_596_) == 0)
{
lean_object* v_a_597_; 
v_a_597_ = lean_ctor_get(v___y_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___y_596_, 1);
v_a_590_ = v_a_597_;
goto v___jp_589_;
}
else
{
lean_dec_ref(v_e_581_);
return v___y_596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0___boxed(lean_object* v_g_645_, lean_object* v_e_646_, lean_object* v_a_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0(v_g_645_, v_e_646_, v_a_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec(v_a_647_);
return v_res_654_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___closed__1(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = lean_box(0);
v___x_657_ = lean_unsigned_to_nat(16u);
v___x_658_ = lean_mk_array(v___x_657_, v___x_656_);
return v___x_658_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___closed__2(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = lean_obj_once(&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___closed__1, &l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___closed__1_once, _init_l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___closed__1);
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v___x_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars(lean_object* v_tree_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v___f_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___f_668_ = ((lean_object*)(l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___closed__0));
v___x_669_ = lean_obj_once(&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___closed__2, &l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___closed__2_once, _init_l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___closed__2);
v___x_670_ = lean_st_mk_ref(v___x_669_);
v___x_671_ = lean_st_mk_ref(v___x_669_);
v___x_672_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0(v___f_668_, v_tree_662_, v___x_671_, v___x_670_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_681_; 
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; 
v_unused_682_ = lean_ctor_get(v___x_672_, 0);
lean_dec(v_unused_682_);
v___x_674_ = v___x_672_;
v_isShared_675_ = v_isSharedCheck_681_;
goto v_resetjp_673_;
}
else
{
lean_dec(v___x_672_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_681_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_676_ = lean_st_ref_get(v___x_671_);
lean_dec(v___x_671_);
lean_dec(v___x_676_);
v___x_677_ = lean_st_ref_get(v___x_670_);
lean_dec(v___x_670_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_677_);
v___x_679_ = v___x_674_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec(v___x_671_);
lean_dec(v___x_670_);
v_a_683_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_672_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_672_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars___boxed(lean_object* v_tree_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars(v_tree_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0(lean_object* v_00_u03b2_698_, lean_object* v_m_699_, lean_object* v_a_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0___redArg(v_m_699_, v_a_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_702_, lean_object* v_m_703_, lean_object* v_a_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0(v_00_u03b2_702_, v_m_703_, v_a_704_);
lean_dec_ref(v_a_704_);
lean_dec_ref(v_m_703_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1(lean_object* v_00_u03b2_706_, lean_object* v_m_707_, lean_object* v_a_708_, lean_object* v_b_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1___redArg(v_m_707_, v_a_708_, v_b_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_711_, lean_object* v_a_712_, lean_object* v_x_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0_spec__1___redArg(v_a_712_, v_x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_715_, lean_object* v_a_716_, lean_object* v_x_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__0_spec__1(v_00_u03b2_715_, v_a_716_, v_x_717_);
lean_dec(v_x_717_);
lean_dec_ref(v_a_716_);
return v_res_718_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_719_, lean_object* v_a_720_, lean_object* v_x_721_){
_start:
{
uint8_t v___x_722_; 
v___x_722_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__3___redArg(v_a_720_, v_x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_723_, lean_object* v_a_724_, lean_object* v_x_725_){
_start:
{
uint8_t v_res_726_; lean_object* v_r_727_; 
v_res_726_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__3(v_00_u03b2_723_, v_a_724_, v_x_725_);
lean_dec(v_x_725_);
lean_dec_ref(v_a_724_);
v_r_727_ = lean_box(v_res_726_);
return v_r_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_728_, lean_object* v_data_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__4___redArg(v_data_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_731_, lean_object* v_a_732_, lean_object* v_b_733_, lean_object* v_x_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__5___redArg(v_a_732_, v_b_733_, v_x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_736_, lean_object* v_i_737_, lean_object* v_source_738_, lean_object* v_target_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__4_spec__5___redArg(v_i_737_, v_source_738_, v_target_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_741_, lean_object* v_x_742_, lean_object* v_x_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_x_742_, v_x_743_);
return v___x_744_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_visit___closed__0(void){
_start:
{
lean_object* v___x_745_; lean_object* v_dummy_746_; 
v___x_745_ = lean_box(0);
v_dummy_746_ = l_Lean_Expr_sort___override(v___x_745_);
return v_dummy_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_visit(lean_object* v_varPos_747_, lean_object* v_lhs_748_, lean_object* v_rhs_749_, lean_object* v_tests_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
if (lean_obj_tag(v_lhs_748_) == 1)
{
lean_object* v_fvarId_756_; uint8_t v___x_757_; 
v_fvarId_756_ = lean_ctor_get(v_lhs_748_, 0);
lean_inc(v_fvarId_756_);
lean_dec_ref_known(v_lhs_748_, 1);
v___x_757_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0___redArg(v_varPos_747_, v_fvarId_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; 
lean_dec(v_fvarId_756_);
lean_dec_ref(v_rhs_749_);
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v_tests_750_);
return v___x_758_;
}
else
{
uint8_t v___x_759_; 
v___x_759_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_isValue(v_rhs_749_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; 
lean_dec(v_fvarId_756_);
lean_dec_ref(v_rhs_749_);
v___x_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_760_, 0, v_tests_750_);
return v___x_760_;
}
else
{
lean_object* v___x_761_; 
v___x_761_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest(v_fvarId_756_, v_rhs_749_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_770_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_770_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_770_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_770_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_766_ = lean_array_push(v_tests_750_, v_a_762_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_766_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v_tests_750_);
v_a_771_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_761_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_761_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
}
else
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_Expr_getAppFn(v_lhs_748_);
if (lean_obj_tag(v___x_779_) == 4)
{
lean_object* v_declName_780_; lean_object* v___x_781_; 
v_declName_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_declName_780_);
lean_dec_ref_known(v___x_779_, 2);
v___x_781_ = l_Lean_Expr_getAppFn(v_rhs_749_);
if (lean_obj_tag(v___x_781_) == 4)
{
lean_object* v_declName_782_; uint8_t v___x_783_; 
v_declName_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_declName_782_);
lean_dec_ref_known(v___x_781_, 2);
v___x_783_ = lean_name_eq(v_declName_780_, v_declName_782_);
lean_dec(v_declName_782_);
lean_dec(v_declName_780_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; 
lean_dec_ref(v_rhs_749_);
lean_dec_ref(v_lhs_748_);
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v_tests_750_);
return v___x_784_;
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_785_ = l_Lean_Expr_getAppNumArgs(v_lhs_748_);
v___x_786_ = l_Lean_Expr_getAppNumArgs(v_rhs_749_);
v___x_787_ = lean_nat_dec_eq(v___x_785_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; 
lean_dec(v___x_786_);
lean_dec(v___x_785_);
lean_dec_ref(v_rhs_749_);
lean_dec_ref(v_lhs_748_);
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v_tests_750_);
return v___x_788_;
}
else
{
lean_object* v_dummy_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; size_t v_sz_801_; size_t v___x_802_; lean_object* v___x_803_; 
v_dummy_789_ = lean_obj_once(&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_visit___closed__0, &l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_visit___closed__0_once, _init_l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_visit___closed__0);
lean_inc(v___x_786_);
v___x_790_ = lean_mk_array(v___x_786_, v_dummy_789_);
v___x_791_ = lean_unsigned_to_nat(1u);
v___x_792_ = lean_nat_sub(v___x_786_, v___x_791_);
lean_dec(v___x_786_);
v___x_793_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_rhs_749_, v___x_790_, v___x_792_);
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = lean_array_get_size(v___x_793_);
v___x_796_ = l_Array_toSubarray___redArg(v___x_793_, v___x_794_, v___x_795_);
lean_inc(v___x_785_);
v___x_797_ = lean_mk_array(v___x_785_, v_dummy_789_);
v___x_798_ = lean_nat_sub(v___x_785_, v___x_791_);
lean_dec(v___x_785_);
v___x_799_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_lhs_748_, v___x_797_, v___x_798_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_tests_750_);
lean_ctor_set(v___x_800_, 1, v___x_796_);
v_sz_801_ = lean_array_size(v___x_799_);
v___x_802_ = ((size_t)0ULL);
v___x_803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_visit_spec__0(v_varPos_747_, v___x_799_, v_sz_801_, v___x_802_, v___x_800_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
lean_dec_ref(v___x_799_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_812_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_812_ == 0)
{
v___x_806_ = v___x_803_;
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_803_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v_fst_808_; lean_object* v___x_810_; 
v_fst_808_ = lean_ctor_get(v_a_804_, 0);
lean_inc(v_fst_808_);
lean_dec(v_a_804_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v_fst_808_);
v___x_810_ = v___x_806_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_fst_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
v_a_813_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_803_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_803_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
}
else
{
lean_object* v___x_821_; 
lean_dec_ref(v___x_781_);
lean_dec(v_declName_780_);
lean_dec_ref(v_rhs_749_);
lean_dec_ref(v_lhs_748_);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v_tests_750_);
return v___x_821_;
}
}
else
{
lean_object* v___x_822_; 
lean_dec_ref(v___x_779_);
lean_dec_ref(v_rhs_749_);
lean_dec_ref(v_lhs_748_);
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v_tests_750_);
return v___x_822_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_visit_spec__0(lean_object* v_varPos_823_, lean_object* v_as_824_, size_t v_sz_825_, size_t v_i_826_, lean_object* v_b_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
uint8_t v___x_833_; 
v___x_833_ = lean_usize_dec_lt(v_i_826_, v_sz_825_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v_b_827_);
return v___x_834_;
}
else
{
lean_object* v_snd_835_; lean_object* v_fst_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_878_; 
v_snd_835_ = lean_ctor_get(v_b_827_, 1);
v_fst_836_ = lean_ctor_get(v_b_827_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v_b_827_);
if (v_isSharedCheck_878_ == 0)
{
v___x_838_ = v_b_827_;
v_isShared_839_ = v_isSharedCheck_878_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_snd_835_);
lean_inc(v_fst_836_);
lean_dec(v_b_827_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_878_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v_array_840_; lean_object* v_start_841_; lean_object* v_stop_842_; uint8_t v___x_843_; 
v_array_840_ = lean_ctor_get(v_snd_835_, 0);
v_start_841_ = lean_ctor_get(v_snd_835_, 1);
v_stop_842_ = lean_ctor_get(v_snd_835_, 2);
v___x_843_ = lean_nat_dec_lt(v_start_841_, v_stop_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_845_; 
if (v_isShared_839_ == 0)
{
v___x_845_ = v___x_838_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_fst_836_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_snd_835_);
v___x_845_ = v_reuseFailAlloc_847_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_846_; 
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
return v___x_846_;
}
}
else
{
lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_874_; 
lean_inc(v_stop_842_);
lean_inc(v_start_841_);
lean_inc_ref(v_array_840_);
v_isSharedCheck_874_ = !lean_is_exclusive(v_snd_835_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; lean_object* v_unused_876_; lean_object* v_unused_877_; 
v_unused_875_ = lean_ctor_get(v_snd_835_, 2);
lean_dec(v_unused_875_);
v_unused_876_ = lean_ctor_get(v_snd_835_, 1);
lean_dec(v_unused_876_);
v_unused_877_ = lean_ctor_get(v_snd_835_, 0);
lean_dec(v_unused_877_);
v___x_849_ = v_snd_835_;
v_isShared_850_ = v_isSharedCheck_874_;
goto v_resetjp_848_;
}
else
{
lean_dec(v_snd_835_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_874_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v_a_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v_a_851_ = lean_array_uget_borrowed(v_as_824_, v_i_826_);
v___x_852_ = lean_array_fget(v_array_840_, v_start_841_);
v___x_853_ = lean_unsigned_to_nat(1u);
v___x_854_ = lean_nat_add(v_start_841_, v___x_853_);
lean_dec(v_start_841_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 1, v___x_854_);
v___x_856_ = v___x_849_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_array_840_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_873_, 2, v_stop_842_);
v___x_856_ = v_reuseFailAlloc_873_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; 
lean_inc(v_a_851_);
v___x_857_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_visit(v_varPos_823_, v_a_851_, v___x_852_, v_fst_836_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_860_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v___x_856_);
lean_ctor_set(v___x_838_, 0, v_a_858_);
v___x_860_ = v___x_838_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v___x_856_);
v___x_860_ = v_reuseFailAlloc_864_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
size_t v___x_861_; size_t v___x_862_; 
v___x_861_ = ((size_t)1ULL);
v___x_862_ = lean_usize_add(v_i_826_, v___x_861_);
v_i_826_ = v___x_862_;
v_b_827_ = v___x_860_;
goto _start;
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec_ref(v___x_856_);
lean_del_object(v___x_838_);
v_a_865_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_857_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_857_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_visit_spec__0___boxed(lean_object* v_varPos_879_, lean_object* v_as_880_, lean_object* v_sz_881_, lean_object* v_i_882_, lean_object* v_b_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
size_t v_sz_boxed_889_; size_t v_i_boxed_890_; lean_object* v_res_891_; 
v_sz_boxed_889_ = lean_unbox_usize(v_sz_881_);
lean_dec(v_sz_881_);
v_i_boxed_890_ = lean_unbox_usize(v_i_882_);
lean_dec(v_i_882_);
v_res_891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_visit_spec__0(v_varPos_879_, v_as_880_, v_sz_boxed_889_, v_i_boxed_890_, v_b_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec_ref(v_as_880_);
lean_dec_ref(v_varPos_879_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_visit___boxed(lean_object* v_varPos_892_, lean_object* v_lhs_893_, lean_object* v_rhs_894_, lean_object* v_tests_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_visit(v_varPos_892_, v_lhs_893_, v_rhs_894_, v_tests_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec_ref(v_varPos_892_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_go(lean_object* v_varPos_902_, lean_object* v_type_903_, lean_object* v_tests_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
if (lean_obj_tag(v_type_903_) == 7)
{
lean_object* v_binderType_910_; lean_object* v_body_911_; lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v_binderType_910_ = lean_ctor_get(v_type_903_, 1);
v_body_911_ = lean_ctor_get(v_type_903_, 2);
v___x_912_ = ((lean_object*)(l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__3));
v___x_913_ = lean_unsigned_to_nat(3u);
v___x_914_ = l_Lean_Expr_isAppOfArity(v_binderType_910_, v___x_912_, v___x_913_);
if (v___x_914_ == 0)
{
v_type_903_ = v_body_911_;
goto _start;
}
else
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = lean_unsigned_to_nat(0u);
v___x_917_ = lean_expr_has_loose_bvar(v_body_911_, v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_918_ = l_Lean_Expr_appFn_x21(v_binderType_910_);
v___x_919_ = l_Lean_Expr_appArg_x21(v___x_918_);
lean_dec_ref(v___x_918_);
v___x_920_ = l_Lean_Expr_appArg_x21(v_binderType_910_);
v___x_921_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_visit(v_varPos_902_, v___x_919_, v___x_920_, v_tests_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref_known(v___x_921_, 1);
v_type_903_ = v_body_911_;
v_tests_904_ = v_a_922_;
goto _start;
}
else
{
return v___x_921_;
}
}
else
{
v_type_903_ = v_body_911_;
goto _start;
}
}
}
else
{
lean_object* v___x_925_; 
v___x_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_925_, 0, v_tests_904_);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_go___boxed(lean_object* v_varPos_926_, lean_object* v_type_927_, lean_object* v_tests_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_go(v_varPos_926_, v_type_927_, v_tests_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec_ref(v_type_927_);
lean_dec_ref(v_varPos_926_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests(lean_object* v_varPos_937_, lean_object* v_type_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests___closed__0));
v___x_945_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests_go(v_varPos_937_, v_type_938_, v___x_944_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests___boxed(lean_object* v_varPos_946_, lean_object* v_type_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests(v_varPos_946_, v_type_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec_ref(v_type_947_);
lean_dec_ref(v_varPos_946_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0_spec__1(lean_object* v_msg_954_){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_unsigned_to_nat(0u);
v___x_956_ = lean_panic_fn_borrowed(v___x_955_, v_msg_954_);
return v___x_956_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_960_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0___closed__2));
v___x_961_ = lean_unsigned_to_nat(11u);
v___x_962_ = lean_unsigned_to_nat(163u);
v___x_963_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0___closed__1));
v___x_964_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0___closed__0));
v___x_965_ = l_mkPanicMessageWithDecl(v___x_964_, v___x_963_, v___x_962_, v___x_961_, v___x_960_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0(lean_object* v_a_966_, lean_object* v_x_967_){
_start:
{
if (lean_obj_tag(v_x_967_) == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0___closed__3);
v___x_969_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0_spec__1(v___x_968_);
return v___x_969_;
}
else
{
lean_object* v_key_970_; lean_object* v_value_971_; lean_object* v_tail_972_; uint8_t v___x_973_; 
v_key_970_ = lean_ctor_get(v_x_967_, 0);
v_value_971_ = lean_ctor_get(v_x_967_, 1);
v_tail_972_ = lean_ctor_get(v_x_967_, 2);
v___x_973_ = l_Lean_instBEqFVarId_beq(v_key_970_, v_a_966_);
if (v___x_973_ == 0)
{
v_x_967_ = v_tail_972_;
goto _start;
}
else
{
lean_inc(v_value_971_);
return v_value_971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0___boxed(lean_object* v_a_975_, lean_object* v_x_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0(v_a_975_, v_x_976_);
lean_dec(v_x_976_);
lean_dec(v_a_975_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0(lean_object* v_m_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_buckets_980_; lean_object* v___x_981_; uint64_t v___x_982_; uint64_t v___x_983_; uint64_t v___x_984_; uint64_t v_fold_985_; uint64_t v___x_986_; uint64_t v___x_987_; uint64_t v___x_988_; size_t v___x_989_; size_t v___x_990_; size_t v___x_991_; size_t v___x_992_; size_t v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_buckets_980_ = lean_ctor_get(v_m_978_, 1);
v___x_981_ = lean_array_get_size(v_buckets_980_);
v___x_982_ = l_Lean_instHashableFVarId_hash(v_a_979_);
v___x_983_ = 32ULL;
v___x_984_ = lean_uint64_shift_right(v___x_982_, v___x_983_);
v_fold_985_ = lean_uint64_xor(v___x_982_, v___x_984_);
v___x_986_ = 16ULL;
v___x_987_ = lean_uint64_shift_right(v_fold_985_, v___x_986_);
v___x_988_ = lean_uint64_xor(v_fold_985_, v___x_987_);
v___x_989_ = lean_uint64_to_usize(v___x_988_);
v___x_990_ = lean_usize_of_nat(v___x_981_);
v___x_991_ = ((size_t)1ULL);
v___x_992_ = lean_usize_sub(v___x_990_, v___x_991_);
v___x_993_ = lean_usize_land(v___x_989_, v___x_992_);
v___x_994_ = lean_array_uget_borrowed(v_buckets_980_, v___x_993_);
v___x_995_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0_spec__0(v_a_979_, v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0___boxed(lean_object* v_m_996_, lean_object* v_a_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0(v_m_996_, v_a_997_);
lean_dec(v_a_997_);
lean_dec_ref(v_m_996_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1_spec__2___redArg(lean_object* v_index_999_, lean_object* v_hi_1000_, lean_object* v_pivot_1001_, lean_object* v_as_1002_, lean_object* v_i_1003_, lean_object* v_k_1004_){
_start:
{
uint8_t v___x_1005_; 
v___x_1005_ = lean_nat_dec_lt(v_k_1004_, v_hi_1000_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_dec(v_k_1004_);
v___x_1006_ = lean_array_fswap(v_as_1002_, v_i_1003_, v_hi_1000_);
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v_i_1003_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
return v___x_1007_;
}
else
{
lean_object* v___x_1008_; lean_object* v_fst_1009_; lean_object* v_fst_1010_; lean_object* v_varPos_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1008_ = lean_array_fget_borrowed(v_as_1002_, v_k_1004_);
v_fst_1009_ = lean_ctor_get(v___x_1008_, 0);
v_fst_1010_ = lean_ctor_get(v_pivot_1001_, 0);
v_varPos_1011_ = lean_ctor_get(v_index_999_, 0);
v___x_1012_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0(v_varPos_1011_, v_fst_1009_);
v___x_1013_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0(v_varPos_1011_, v_fst_1010_);
v___x_1014_ = lean_nat_dec_lt(v___x_1012_, v___x_1013_);
lean_dec(v___x_1013_);
lean_dec(v___x_1012_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_unsigned_to_nat(1u);
v___x_1016_ = lean_nat_add(v_k_1004_, v___x_1015_);
lean_dec(v_k_1004_);
v_k_1004_ = v___x_1016_;
goto _start;
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1018_ = lean_array_fswap(v_as_1002_, v_i_1003_, v_k_1004_);
v___x_1019_ = lean_unsigned_to_nat(1u);
v___x_1020_ = lean_nat_add(v_i_1003_, v___x_1019_);
lean_dec(v_i_1003_);
v___x_1021_ = lean_nat_add(v_k_1004_, v___x_1019_);
lean_dec(v_k_1004_);
v_as_1002_ = v___x_1018_;
v_i_1003_ = v___x_1020_;
v_k_1004_ = v___x_1021_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1_spec__2___redArg___boxed(lean_object* v_index_1023_, lean_object* v_hi_1024_, lean_object* v_pivot_1025_, lean_object* v_as_1026_, lean_object* v_i_1027_, lean_object* v_k_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1_spec__2___redArg(v_index_1023_, v_hi_1024_, v_pivot_1025_, v_as_1026_, v_i_1027_, v_k_1028_);
lean_dec_ref(v_pivot_1025_);
lean_dec(v_hi_1024_);
lean_dec_ref(v_index_1023_);
return v_res_1029_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1___redArg___lam__0(lean_object* v_index_1030_, lean_object* v_x_1031_, lean_object* v_x_1032_){
_start:
{
lean_object* v_fst_1033_; lean_object* v_fst_1034_; lean_object* v_varPos_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; 
v_fst_1033_ = lean_ctor_get(v_x_1031_, 0);
v_fst_1034_ = lean_ctor_get(v_x_1032_, 0);
v_varPos_1035_ = lean_ctor_get(v_index_1030_, 0);
v___x_1036_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0(v_varPos_1035_, v_fst_1033_);
v___x_1037_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__0(v_varPos_1035_, v_fst_1034_);
v___x_1038_ = lean_nat_dec_lt(v___x_1036_, v___x_1037_);
lean_dec(v___x_1037_);
lean_dec(v___x_1036_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1___redArg___lam__0___boxed(lean_object* v_index_1039_, lean_object* v_x_1040_, lean_object* v_x_1041_){
_start:
{
uint8_t v_res_1042_; lean_object* v_r_1043_; 
v_res_1042_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1___redArg___lam__0(v_index_1039_, v_x_1040_, v_x_1041_);
lean_dec_ref(v_x_1041_);
lean_dec_ref(v_x_1040_);
lean_dec_ref(v_index_1039_);
v_r_1043_ = lean_box(v_res_1042_);
return v_r_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1___redArg(lean_object* v_index_1044_, lean_object* v_n_1045_, lean_object* v_as_1046_, lean_object* v_lo_1047_, lean_object* v_hi_1048_){
_start:
{
lean_object* v___y_1050_; uint8_t v___x_1060_; 
v___x_1060_ = lean_nat_dec_lt(v_lo_1047_, v_hi_1048_);
if (v___x_1060_ == 0)
{
lean_dec(v_lo_1047_);
return v_as_1046_;
}
else
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v_mid_1063_; lean_object* v___y_1065_; lean_object* v___y_1071_; lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1061_ = lean_nat_add(v_lo_1047_, v_hi_1048_);
v___x_1062_ = lean_unsigned_to_nat(1u);
v_mid_1063_ = lean_nat_shiftr(v___x_1061_, v___x_1062_);
lean_dec(v___x_1061_);
v___x_1076_ = lean_array_fget_borrowed(v_as_1046_, v_mid_1063_);
v___x_1077_ = lean_array_fget_borrowed(v_as_1046_, v_lo_1047_);
v___x_1078_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1___redArg___lam__0(v_index_1044_, v___x_1076_, v___x_1077_);
if (v___x_1078_ == 0)
{
v___y_1071_ = v_as_1046_;
goto v___jp_1070_;
}
else
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_array_fswap(v_as_1046_, v_lo_1047_, v_mid_1063_);
v___y_1071_ = v___x_1079_;
goto v___jp_1070_;
}
v___jp_1064_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1066_ = lean_array_fget_borrowed(v___y_1065_, v_mid_1063_);
v___x_1067_ = lean_array_fget_borrowed(v___y_1065_, v_hi_1048_);
v___x_1068_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1___redArg___lam__0(v_index_1044_, v___x_1066_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_dec(v_mid_1063_);
v___y_1050_ = v___y_1065_;
goto v___jp_1049_;
}
else
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_array_fswap(v___y_1065_, v_mid_1063_, v_hi_1048_);
lean_dec(v_mid_1063_);
v___y_1050_ = v___x_1069_;
goto v___jp_1049_;
}
}
v___jp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1072_ = lean_array_fget_borrowed(v___y_1071_, v_hi_1048_);
v___x_1073_ = lean_array_fget_borrowed(v___y_1071_, v_lo_1047_);
v___x_1074_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1___redArg___lam__0(v_index_1044_, v___x_1072_, v___x_1073_);
if (v___x_1074_ == 0)
{
v___y_1065_ = v___y_1071_;
goto v___jp_1064_;
}
else
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_array_fswap(v___y_1071_, v_lo_1047_, v_hi_1048_);
v___y_1065_ = v___x_1075_;
goto v___jp_1064_;
}
}
}
v___jp_1049_:
{
lean_object* v_pivot_1051_; lean_object* v___x_1052_; lean_object* v_fst_1053_; lean_object* v_snd_1054_; uint8_t v___x_1055_; 
v_pivot_1051_ = lean_array_fget(v___y_1050_, v_hi_1048_);
lean_inc_n(v_lo_1047_, 2);
v___x_1052_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1_spec__2___redArg(v_index_1044_, v_hi_1048_, v_pivot_1051_, v___y_1050_, v_lo_1047_, v_lo_1047_);
lean_dec(v_pivot_1051_);
v_fst_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_fst_1053_);
v_snd_1054_ = lean_ctor_get(v___x_1052_, 1);
lean_inc(v_snd_1054_);
lean_dec_ref(v___x_1052_);
v___x_1055_ = lean_nat_dec_le(v_hi_1048_, v_fst_1053_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1056_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1___redArg(v_index_1044_, v_n_1045_, v_snd_1054_, v_lo_1047_, v_fst_1053_);
v___x_1057_ = lean_unsigned_to_nat(1u);
v___x_1058_ = lean_nat_add(v_fst_1053_, v___x_1057_);
lean_dec(v_fst_1053_);
v_as_1046_ = v___x_1056_;
v_lo_1047_ = v___x_1058_;
goto _start;
}
else
{
lean_dec(v_fst_1053_);
lean_dec(v_lo_1047_);
return v_snd_1054_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1___redArg___boxed(lean_object* v_index_1080_, lean_object* v_n_1081_, lean_object* v_as_1082_, lean_object* v_lo_1083_, lean_object* v_hi_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1___redArg(v_index_1080_, v_n_1081_, v_as_1082_, v_lo_1083_, v_hi_1084_);
lean_dec(v_hi_1084_);
lean_dec(v_n_1081_);
lean_dec_ref(v_index_1080_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort(lean_object* v_index_1086_, lean_object* v_tests_1087_){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1088_ = lean_array_get_size(v_tests_1087_);
v___x_1089_ = lean_unsigned_to_nat(0u);
v___x_1090_ = lean_nat_dec_eq(v___x_1088_, v___x_1089_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___y_1094_; uint8_t v___x_1098_; 
v___x_1091_ = lean_unsigned_to_nat(1u);
v___x_1092_ = lean_nat_sub(v___x_1088_, v___x_1091_);
v___x_1098_ = lean_nat_dec_le(v___x_1089_, v___x_1092_);
if (v___x_1098_ == 0)
{
lean_inc(v___x_1092_);
v___y_1094_ = v___x_1092_;
goto v___jp_1093_;
}
else
{
v___y_1094_ = v___x_1089_;
goto v___jp_1093_;
}
v___jp_1093_:
{
uint8_t v___x_1095_; 
v___x_1095_ = lean_nat_dec_le(v___y_1094_, v___x_1092_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; 
lean_dec(v___x_1092_);
lean_inc(v___y_1094_);
v___x_1096_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1___redArg(v_index_1086_, v___x_1088_, v_tests_1087_, v___y_1094_, v___y_1094_);
lean_dec(v___y_1094_);
return v___x_1096_;
}
else
{
lean_object* v___x_1097_; 
v___x_1097_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1___redArg(v_index_1086_, v___x_1088_, v_tests_1087_, v___y_1094_, v___x_1092_);
lean_dec(v___x_1092_);
return v___x_1097_;
}
}
}
else
{
return v_tests_1087_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort___boxed(lean_object* v_index_1099_, lean_object* v_tests_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort(v_index_1099_, v_tests_1100_);
lean_dec_ref(v_index_1099_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1(lean_object* v_index_1102_, lean_object* v_n_1103_, lean_object* v_as_1104_, lean_object* v_lo_1105_, lean_object* v_hi_1106_, lean_object* v_w_1107_, lean_object* v_hlo_1108_, lean_object* v_hhi_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1___redArg(v_index_1102_, v_n_1103_, v_as_1104_, v_lo_1105_, v_hi_1106_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1___boxed(lean_object* v_index_1111_, lean_object* v_n_1112_, lean_object* v_as_1113_, lean_object* v_lo_1114_, lean_object* v_hi_1115_, lean_object* v_w_1116_, lean_object* v_hlo_1117_, lean_object* v_hhi_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1(v_index_1111_, v_n_1112_, v_as_1113_, v_lo_1114_, v_hi_1115_, v_w_1116_, v_hlo_1117_, v_hhi_1118_);
lean_dec(v_hi_1115_);
lean_dec(v_n_1112_);
lean_dec_ref(v_index_1111_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1_spec__2(lean_object* v_index_1120_, lean_object* v_n_1121_, lean_object* v_lo_1122_, lean_object* v_hi_1123_, lean_object* v_hhi_1124_, lean_object* v_pivot_1125_, lean_object* v_as_1126_, lean_object* v_i_1127_, lean_object* v_k_1128_, lean_object* v_ilo_1129_, lean_object* v_ik_1130_, lean_object* v_w_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1_spec__2___redArg(v_index_1120_, v_hi_1123_, v_pivot_1125_, v_as_1126_, v_i_1127_, v_k_1128_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1_spec__2___boxed(lean_object* v_index_1133_, lean_object* v_n_1134_, lean_object* v_lo_1135_, lean_object* v_hi_1136_, lean_object* v_hhi_1137_, lean_object* v_pivot_1138_, lean_object* v_as_1139_, lean_object* v_i_1140_, lean_object* v_k_1141_, lean_object* v_ilo_1142_, lean_object* v_ik_1143_, lean_object* v_w_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort_spec__1_spec__2(v_index_1133_, v_n_1134_, v_lo_1135_, v_hi_1136_, v_hhi_1137_, v_pivot_1138_, v_as_1139_, v_i_1140_, v_k_1141_, v_ilo_1142_, v_ik_1143_, v_w_1144_);
lean_dec_ref(v_pivot_1138_);
lean_dec(v_hi_1136_);
lean_dec(v_lo_1135_);
lean_dec(v_n_1134_);
lean_dec_ref(v_index_1133_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__4___redArg(lean_object* v_a_1146_, lean_object* v_b_1147_, lean_object* v_x_1148_){
_start:
{
if (lean_obj_tag(v_x_1148_) == 0)
{
lean_dec(v_b_1147_);
lean_dec_ref(v_a_1146_);
return v_x_1148_;
}
else
{
lean_object* v_key_1149_; lean_object* v_value_1150_; lean_object* v_tail_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1167_; 
v_key_1149_ = lean_ctor_get(v_x_1148_, 0);
v_value_1150_ = lean_ctor_get(v_x_1148_, 1);
v_tail_1151_ = lean_ctor_get(v_x_1148_, 2);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_x_1148_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1153_ = v_x_1148_;
v_isShared_1154_ = v_isSharedCheck_1167_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_tail_1151_);
lean_inc(v_value_1150_);
lean_inc(v_key_1149_);
lean_dec(v_x_1148_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1167_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v_fst_1160_; lean_object* v_snd_1161_; lean_object* v_fst_1162_; lean_object* v_snd_1163_; uint8_t v___x_1164_; 
v_fst_1160_ = lean_ctor_get(v_key_1149_, 0);
v_snd_1161_ = lean_ctor_get(v_key_1149_, 1);
v_fst_1162_ = lean_ctor_get(v_a_1146_, 0);
v_snd_1163_ = lean_ctor_get(v_a_1146_, 1);
v___x_1164_ = l_Lean_instBEqFVarId_beq(v_fst_1160_, v_fst_1162_);
if (v___x_1164_ == 0)
{
goto v___jp_1155_;
}
else
{
uint8_t v___x_1165_; 
v___x_1165_ = lean_expr_eqv(v_snd_1161_, v_snd_1163_);
if (v___x_1165_ == 0)
{
goto v___jp_1155_;
}
else
{
lean_object* v___x_1166_; 
lean_del_object(v___x_1153_);
lean_dec(v_value_1150_);
lean_dec(v_key_1149_);
v___x_1166_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1166_, 0, v_a_1146_);
lean_ctor_set(v___x_1166_, 1, v_b_1147_);
lean_ctor_set(v___x_1166_, 2, v_tail_1151_);
return v___x_1166_;
}
}
v___jp_1155_:
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1156_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__4___redArg(v_a_1146_, v_b_1147_, v_tail_1151_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 2, v___x_1156_);
v___x_1158_ = v___x_1153_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_key_1149_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_value_1150_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__3_spec__4_spec__6___redArg(lean_object* v_x_1168_, lean_object* v_x_1169_){
_start:
{
if (lean_obj_tag(v_x_1169_) == 0)
{
return v_x_1168_;
}
else
{
lean_object* v_key_1170_; lean_object* v_value_1171_; lean_object* v_tail_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1199_; 
v_key_1170_ = lean_ctor_get(v_x_1169_, 0);
v_value_1171_ = lean_ctor_get(v_x_1169_, 1);
v_tail_1172_ = lean_ctor_get(v_x_1169_, 2);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_x_1169_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1174_ = v_x_1169_;
v_isShared_1175_ = v_isSharedCheck_1199_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_tail_1172_);
lean_inc(v_value_1171_);
lean_inc(v_key_1170_);
lean_dec(v_x_1169_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1199_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v_fst_1176_; lean_object* v_snd_1177_; lean_object* v___x_1178_; uint64_t v___x_1179_; uint64_t v___x_1180_; uint64_t v___x_1181_; uint64_t v___x_1182_; uint64_t v___x_1183_; uint64_t v_fold_1184_; uint64_t v___x_1185_; uint64_t v___x_1186_; uint64_t v___x_1187_; size_t v___x_1188_; size_t v___x_1189_; size_t v___x_1190_; size_t v___x_1191_; size_t v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v_fst_1176_ = lean_ctor_get(v_key_1170_, 0);
v_snd_1177_ = lean_ctor_get(v_key_1170_, 1);
v___x_1178_ = lean_array_get_size(v_x_1168_);
v___x_1179_ = l_Lean_instHashableFVarId_hash(v_fst_1176_);
v___x_1180_ = l_Lean_Expr_hash(v_snd_1177_);
v___x_1181_ = lean_uint64_mix_hash(v___x_1179_, v___x_1180_);
v___x_1182_ = 32ULL;
v___x_1183_ = lean_uint64_shift_right(v___x_1181_, v___x_1182_);
v_fold_1184_ = lean_uint64_xor(v___x_1181_, v___x_1183_);
v___x_1185_ = 16ULL;
v___x_1186_ = lean_uint64_shift_right(v_fold_1184_, v___x_1185_);
v___x_1187_ = lean_uint64_xor(v_fold_1184_, v___x_1186_);
v___x_1188_ = lean_uint64_to_usize(v___x_1187_);
v___x_1189_ = lean_usize_of_nat(v___x_1178_);
v___x_1190_ = ((size_t)1ULL);
v___x_1191_ = lean_usize_sub(v___x_1189_, v___x_1190_);
v___x_1192_ = lean_usize_land(v___x_1188_, v___x_1191_);
v___x_1193_ = lean_array_uget_borrowed(v_x_1168_, v___x_1192_);
lean_inc(v___x_1193_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 2, v___x_1193_);
v___x_1195_ = v___x_1174_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_key_1170_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_value_1171_);
lean_ctor_set(v_reuseFailAlloc_1198_, 2, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_array_uset(v_x_1168_, v___x_1192_, v___x_1195_);
v_x_1168_ = v___x_1196_;
v_x_1169_ = v_tail_1172_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1200_, lean_object* v_source_1201_, lean_object* v_target_1202_){
_start:
{
lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = lean_array_get_size(v_source_1201_);
v___x_1204_ = lean_nat_dec_lt(v_i_1200_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_dec_ref(v_source_1201_);
lean_dec(v_i_1200_);
return v_target_1202_;
}
else
{
lean_object* v_es_1205_; lean_object* v___x_1206_; lean_object* v_source_1207_; lean_object* v_target_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v_es_1205_ = lean_array_fget(v_source_1201_, v_i_1200_);
v___x_1206_ = lean_box(0);
v_source_1207_ = lean_array_fset(v_source_1201_, v_i_1200_, v___x_1206_);
v_target_1208_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__3_spec__4_spec__6___redArg(v_target_1202_, v_es_1205_);
v___x_1209_ = lean_unsigned_to_nat(1u);
v___x_1210_ = lean_nat_add(v_i_1200_, v___x_1209_);
lean_dec(v_i_1200_);
v_i_1200_ = v___x_1210_;
v_source_1201_ = v_source_1207_;
v_target_1202_ = v_target_1208_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__3___redArg(lean_object* v_data_1212_){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v_nbuckets_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1213_ = lean_array_get_size(v_data_1212_);
v___x_1214_ = lean_unsigned_to_nat(2u);
v_nbuckets_1215_ = lean_nat_mul(v___x_1213_, v___x_1214_);
v___x_1216_ = lean_unsigned_to_nat(0u);
v___x_1217_ = lean_box(0);
v___x_1218_ = lean_mk_array(v_nbuckets_1215_, v___x_1217_);
v___x_1219_ = lean_array_propagate_mark(v_data_1212_, v___x_1218_);
v___x_1220_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__3_spec__4___redArg(v___x_1216_, v_data_1212_, v___x_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__2___redArg(lean_object* v_a_1221_, lean_object* v_x_1222_){
_start:
{
if (lean_obj_tag(v_x_1222_) == 0)
{
uint8_t v___x_1223_; 
v___x_1223_ = 0;
return v___x_1223_;
}
else
{
lean_object* v_key_1224_; lean_object* v_tail_1225_; lean_object* v_fst_1226_; lean_object* v_snd_1227_; lean_object* v_fst_1228_; lean_object* v_snd_1229_; uint8_t v___x_1230_; 
v_key_1224_ = lean_ctor_get(v_x_1222_, 0);
v_tail_1225_ = lean_ctor_get(v_x_1222_, 2);
v_fst_1226_ = lean_ctor_get(v_key_1224_, 0);
v_snd_1227_ = lean_ctor_get(v_key_1224_, 1);
v_fst_1228_ = lean_ctor_get(v_a_1221_, 0);
v_snd_1229_ = lean_ctor_get(v_a_1221_, 1);
v___x_1230_ = l_Lean_instBEqFVarId_beq(v_fst_1226_, v_fst_1228_);
if (v___x_1230_ == 0)
{
v_x_1222_ = v_tail_1225_;
goto _start;
}
else
{
uint8_t v___x_1232_; 
v___x_1232_ = lean_expr_eqv(v_snd_1227_, v_snd_1229_);
if (v___x_1232_ == 0)
{
v_x_1222_ = v_tail_1225_;
goto _start;
}
else
{
return v___x_1232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__2___redArg___boxed(lean_object* v_a_1234_, lean_object* v_x_1235_){
_start:
{
uint8_t v_res_1236_; lean_object* v_r_1237_; 
v_res_1236_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__2___redArg(v_a_1234_, v_x_1235_);
lean_dec(v_x_1235_);
lean_dec_ref(v_a_1234_);
v_r_1237_ = lean_box(v_res_1236_);
return v_r_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1___redArg(lean_object* v_m_1238_, lean_object* v_a_1239_, lean_object* v_b_1240_){
_start:
{
lean_object* v_size_1241_; lean_object* v_buckets_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1289_; 
v_size_1241_ = lean_ctor_get(v_m_1238_, 0);
v_buckets_1242_ = lean_ctor_get(v_m_1238_, 1);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_m_1238_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1244_ = v_m_1238_;
v_isShared_1245_ = v_isSharedCheck_1289_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_buckets_1242_);
lean_inc(v_size_1241_);
lean_dec(v_m_1238_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1289_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v_fst_1246_; lean_object* v_snd_1247_; lean_object* v___x_1248_; uint64_t v___x_1249_; uint64_t v___x_1250_; uint64_t v___x_1251_; uint64_t v___x_1252_; uint64_t v___x_1253_; uint64_t v_fold_1254_; uint64_t v___x_1255_; uint64_t v___x_1256_; uint64_t v___x_1257_; size_t v___x_1258_; size_t v___x_1259_; size_t v___x_1260_; size_t v___x_1261_; size_t v___x_1262_; lean_object* v_bkt_1263_; uint8_t v___x_1264_; 
v_fst_1246_ = lean_ctor_get(v_a_1239_, 0);
v_snd_1247_ = lean_ctor_get(v_a_1239_, 1);
v___x_1248_ = lean_array_get_size(v_buckets_1242_);
v___x_1249_ = l_Lean_instHashableFVarId_hash(v_fst_1246_);
v___x_1250_ = l_Lean_Expr_hash(v_snd_1247_);
v___x_1251_ = lean_uint64_mix_hash(v___x_1249_, v___x_1250_);
v___x_1252_ = 32ULL;
v___x_1253_ = lean_uint64_shift_right(v___x_1251_, v___x_1252_);
v_fold_1254_ = lean_uint64_xor(v___x_1251_, v___x_1253_);
v___x_1255_ = 16ULL;
v___x_1256_ = lean_uint64_shift_right(v_fold_1254_, v___x_1255_);
v___x_1257_ = lean_uint64_xor(v_fold_1254_, v___x_1256_);
v___x_1258_ = lean_uint64_to_usize(v___x_1257_);
v___x_1259_ = lean_usize_of_nat(v___x_1248_);
v___x_1260_ = ((size_t)1ULL);
v___x_1261_ = lean_usize_sub(v___x_1259_, v___x_1260_);
v___x_1262_ = lean_usize_land(v___x_1258_, v___x_1261_);
v_bkt_1263_ = lean_array_uget_borrowed(v_buckets_1242_, v___x_1262_);
v___x_1264_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__2___redArg(v_a_1239_, v_bkt_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; lean_object* v_size_x27_1266_; lean_object* v___x_1267_; lean_object* v_buckets_x27_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1265_ = lean_unsigned_to_nat(1u);
v_size_x27_1266_ = lean_nat_add(v_size_1241_, v___x_1265_);
lean_dec(v_size_1241_);
lean_inc(v_bkt_1263_);
v___x_1267_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1267_, 0, v_a_1239_);
lean_ctor_set(v___x_1267_, 1, v_b_1240_);
lean_ctor_set(v___x_1267_, 2, v_bkt_1263_);
v_buckets_x27_1268_ = lean_array_uset(v_buckets_1242_, v___x_1262_, v___x_1267_);
v___x_1269_ = lean_unsigned_to_nat(4u);
v___x_1270_ = lean_nat_mul(v_size_x27_1266_, v___x_1269_);
v___x_1271_ = lean_unsigned_to_nat(3u);
v___x_1272_ = lean_nat_div(v___x_1270_, v___x_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_array_get_size(v_buckets_x27_1268_);
v___x_1274_ = lean_nat_dec_le(v___x_1272_, v___x_1273_);
lean_dec(v___x_1272_);
if (v___x_1274_ == 0)
{
lean_object* v_val_1275_; lean_object* v___x_1277_; 
v_val_1275_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__3___redArg(v_buckets_x27_1268_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v_val_1275_);
lean_ctor_set(v___x_1244_, 0, v_size_x27_1266_);
v___x_1277_ = v___x_1244_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_size_x27_1266_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_val_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
else
{
lean_object* v___x_1280_; 
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v_buckets_x27_1268_);
lean_ctor_set(v___x_1244_, 0, v_size_x27_1266_);
v___x_1280_ = v___x_1244_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_size_x27_1266_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_buckets_x27_1268_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
else
{
lean_object* v___x_1282_; lean_object* v_buckets_x27_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1287_; 
lean_inc(v_bkt_1263_);
v___x_1282_ = lean_box(0);
v_buckets_x27_1283_ = lean_array_uset(v_buckets_1242_, v___x_1262_, v___x_1282_);
v___x_1284_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__4___redArg(v_a_1239_, v_b_1240_, v_bkt_1263_);
v___x_1285_ = lean_array_uset(v_buckets_x27_1283_, v___x_1262_, v___x_1284_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v___x_1285_);
v___x_1287_ = v___x_1244_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_size_1241_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0_spec__0___redArg(lean_object* v_a_1290_, lean_object* v_x_1291_){
_start:
{
if (lean_obj_tag(v_x_1291_) == 0)
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_box(0);
return v___x_1292_;
}
else
{
lean_object* v_key_1293_; lean_object* v_value_1294_; lean_object* v_tail_1295_; lean_object* v_fst_1296_; lean_object* v_snd_1297_; lean_object* v_fst_1298_; lean_object* v_snd_1299_; uint8_t v___x_1300_; 
v_key_1293_ = lean_ctor_get(v_x_1291_, 0);
v_value_1294_ = lean_ctor_get(v_x_1291_, 1);
v_tail_1295_ = lean_ctor_get(v_x_1291_, 2);
v_fst_1296_ = lean_ctor_get(v_key_1293_, 0);
v_snd_1297_ = lean_ctor_get(v_key_1293_, 1);
v_fst_1298_ = lean_ctor_get(v_a_1290_, 0);
v_snd_1299_ = lean_ctor_get(v_a_1290_, 1);
v___x_1300_ = l_Lean_instBEqFVarId_beq(v_fst_1296_, v_fst_1298_);
if (v___x_1300_ == 0)
{
v_x_1291_ = v_tail_1295_;
goto _start;
}
else
{
uint8_t v___x_1302_; 
v___x_1302_ = lean_expr_eqv(v_snd_1297_, v_snd_1299_);
if (v___x_1302_ == 0)
{
v_x_1291_ = v_tail_1295_;
goto _start;
}
else
{
lean_object* v___x_1304_; 
lean_inc(v_value_1294_);
v___x_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1304_, 0, v_value_1294_);
return v___x_1304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0_spec__0___redArg___boxed(lean_object* v_a_1305_, lean_object* v_x_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0_spec__0___redArg(v_a_1305_, v_x_1306_);
lean_dec(v_x_1306_);
lean_dec_ref(v_a_1305_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0___redArg(lean_object* v_m_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_buckets_1310_; lean_object* v_fst_1311_; lean_object* v_snd_1312_; lean_object* v___x_1313_; uint64_t v___x_1314_; uint64_t v___x_1315_; uint64_t v___x_1316_; uint64_t v___x_1317_; uint64_t v___x_1318_; uint64_t v_fold_1319_; uint64_t v___x_1320_; uint64_t v___x_1321_; uint64_t v___x_1322_; size_t v___x_1323_; size_t v___x_1324_; size_t v___x_1325_; size_t v___x_1326_; size_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v_buckets_1310_ = lean_ctor_get(v_m_1308_, 1);
v_fst_1311_ = lean_ctor_get(v_a_1309_, 0);
v_snd_1312_ = lean_ctor_get(v_a_1309_, 1);
v___x_1313_ = lean_array_get_size(v_buckets_1310_);
v___x_1314_ = l_Lean_instHashableFVarId_hash(v_fst_1311_);
v___x_1315_ = l_Lean_Expr_hash(v_snd_1312_);
v___x_1316_ = lean_uint64_mix_hash(v___x_1314_, v___x_1315_);
v___x_1317_ = 32ULL;
v___x_1318_ = lean_uint64_shift_right(v___x_1316_, v___x_1317_);
v_fold_1319_ = lean_uint64_xor(v___x_1316_, v___x_1318_);
v___x_1320_ = 16ULL;
v___x_1321_ = lean_uint64_shift_right(v_fold_1319_, v___x_1320_);
v___x_1322_ = lean_uint64_xor(v_fold_1319_, v___x_1321_);
v___x_1323_ = lean_uint64_to_usize(v___x_1322_);
v___x_1324_ = lean_usize_of_nat(v___x_1313_);
v___x_1325_ = ((size_t)1ULL);
v___x_1326_ = lean_usize_sub(v___x_1324_, v___x_1325_);
v___x_1327_ = lean_usize_land(v___x_1323_, v___x_1326_);
v___x_1328_ = lean_array_uget_borrowed(v_buckets_1310_, v___x_1327_);
v___x_1329_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0_spec__0___redArg(v_a_1309_, v___x_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0___redArg___boxed(lean_object* v_m_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0___redArg(v_m_1330_, v_a_1331_);
lean_dec_ref(v_a_1331_);
lean_dec_ref(v_m_1330_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__2(lean_object* v_as_1333_, size_t v_sz_1334_, size_t v_i_1335_, lean_object* v_b_1336_){
_start:
{
lean_object* v_a_1338_; uint8_t v___x_1342_; 
v___x_1342_ = lean_usize_dec_lt(v_i_1335_, v_sz_1334_);
if (v___x_1342_ == 0)
{
return v_b_1336_;
}
else
{
lean_object* v_fst_1343_; lean_object* v_snd_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1380_; 
v_fst_1343_ = lean_ctor_get(v_b_1336_, 0);
v_snd_1344_ = lean_ctor_get(v_b_1336_, 1);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_b_1336_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1346_ = v_b_1336_;
v_isShared_1347_ = v_isSharedCheck_1380_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_snd_1344_);
lean_inc(v_fst_1343_);
lean_dec(v_b_1336_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1380_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v_children_1350_; lean_object* v_a_1351_; lean_object* v___x_1352_; 
v___x_1348_ = l_Lean_Meta_Match_DiteTree_instInhabitedNode_default;
v___x_1349_ = lean_array_get_borrowed(v___x_1348_, v_fst_1343_, v_snd_1344_);
v_children_1350_ = lean_ctor_get(v___x_1349_, 1);
v_a_1351_ = lean_array_uget_borrowed(v_as_1333_, v_i_1335_);
v___x_1352_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0___redArg(v_children_1350_, v_a_1351_);
if (lean_obj_tag(v___x_1352_) == 1)
{
lean_object* v_val_1353_; lean_object* v___x_1355_; 
lean_dec(v_snd_1344_);
v_val_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_val_1353_);
lean_dec_ref_known(v___x_1352_, 1);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v_val_1353_);
v___x_1355_ = v___x_1346_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_fst_1343_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_val_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
v_a_1338_ = v___x_1355_;
goto v___jp_1337_;
}
}
else
{
lean_object* v___x_1357_; lean_object* v___y_1359_; uint8_t v___x_1365_; 
lean_dec(v___x_1352_);
v___x_1357_ = lean_array_get_size(v_fst_1343_);
v___x_1365_ = lean_nat_dec_lt(v_snd_1344_, v___x_1357_);
if (v___x_1365_ == 0)
{
lean_dec(v_snd_1344_);
v___y_1359_ = v_fst_1343_;
goto v___jp_1358_;
}
else
{
lean_object* v_v_1366_; lean_object* v_hyps_1367_; lean_object* v_children_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1379_; 
v_v_1366_ = lean_array_fget(v_fst_1343_, v_snd_1344_);
v_hyps_1367_ = lean_ctor_get(v_v_1366_, 0);
v_children_1368_ = lean_ctor_get(v_v_1366_, 1);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_v_1366_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1370_ = v_v_1366_;
v_isShared_1371_ = v_isSharedCheck_1379_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_children_1368_);
lean_inc(v_hyps_1367_);
lean_dec(v_v_1366_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1379_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v_xs_x27_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1372_ = lean_box(0);
v_xs_x27_1373_ = lean_array_fset(v_fst_1343_, v_snd_1344_, v___x_1372_);
lean_inc(v_a_1351_);
v___x_1374_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1___redArg(v_children_1368_, v_a_1351_, v___x_1357_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 1, v___x_1374_);
v___x_1376_ = v___x_1370_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_hyps_1367_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_array_fset(v_xs_x27_1373_, v_snd_1344_, v___x_1376_);
lean_dec(v_snd_1344_);
v___y_1359_ = v___x_1377_;
goto v___jp_1358_;
}
}
}
v___jp_1358_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1363_; 
v___x_1360_ = lean_obj_once(&l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__3, &l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__3_once, _init_l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__3);
v___x_1361_ = lean_array_push(v___y_1359_, v___x_1360_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v___x_1357_);
lean_ctor_set(v___x_1346_, 0, v___x_1361_);
v___x_1363_ = v___x_1346_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v___x_1357_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
v_a_1338_ = v___x_1363_;
goto v___jp_1337_;
}
}
}
}
}
v___jp_1337_:
{
size_t v___x_1339_; size_t v___x_1340_; 
v___x_1339_ = ((size_t)1ULL);
v___x_1340_ = lean_usize_add(v_i_1335_, v___x_1339_);
v_i_1335_ = v___x_1340_;
v_b_1336_ = v_a_1338_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__2___boxed(lean_object* v_as_1381_, lean_object* v_sz_1382_, lean_object* v_i_1383_, lean_object* v_b_1384_){
_start:
{
size_t v_sz_boxed_1385_; size_t v_i_boxed_1386_; lean_object* v_res_1387_; 
v_sz_boxed_1385_ = lean_unbox_usize(v_sz_1382_);
lean_dec(v_sz_1382_);
v_i_boxed_1386_ = lean_unbox_usize(v_i_1383_);
lean_dec(v_i_1383_);
v_res_1387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__2(v_as_1381_, v_sz_boxed_1385_, v_i_boxed_1386_, v_b_1384_);
lean_dec_ref(v_as_1381_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert(lean_object* v_index_1388_, lean_object* v_fvarId_1389_, lean_object* v_tests_1390_){
_start:
{
lean_object* v_varPos_1391_; lean_object* v_nodes_1392_; lean_object* v_tests_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1426_; 
v_varPos_1391_ = lean_ctor_get(v_index_1388_, 0);
lean_inc_ref(v_varPos_1391_);
v_nodes_1392_ = lean_ctor_get(v_index_1388_, 1);
lean_inc_ref(v_nodes_1392_);
v_tests_1393_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort(v_index_1388_, v_tests_1390_);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_index_1388_);
if (v_isSharedCheck_1426_ == 0)
{
lean_object* v_unused_1427_; lean_object* v_unused_1428_; 
v_unused_1427_ = lean_ctor_get(v_index_1388_, 1);
lean_dec(v_unused_1427_);
v_unused_1428_ = lean_ctor_get(v_index_1388_, 0);
lean_dec(v_unused_1428_);
v___x_1395_ = v_index_1388_;
v_isShared_1396_ = v_isSharedCheck_1426_;
goto v_resetjp_1394_;
}
else
{
lean_dec(v_index_1388_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1426_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v_i_1397_; lean_object* v___x_1398_; size_t v_sz_1399_; size_t v___x_1400_; lean_object* v___x_1401_; lean_object* v_fst_1402_; lean_object* v_snd_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v_i_1397_ = lean_unsigned_to_nat(0u);
v___x_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1398_, 0, v_nodes_1392_);
lean_ctor_set(v___x_1398_, 1, v_i_1397_);
v_sz_1399_ = lean_array_size(v_tests_1393_);
v___x_1400_ = ((size_t)0ULL);
v___x_1401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__2(v_tests_1393_, v_sz_1399_, v___x_1400_, v___x_1398_);
lean_dec_ref(v_tests_1393_);
v_fst_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_fst_1402_);
v_snd_1403_ = lean_ctor_get(v___x_1401_, 1);
lean_inc(v_snd_1403_);
lean_dec_ref(v___x_1401_);
v___x_1404_ = lean_array_get_size(v_fst_1402_);
v___x_1405_ = lean_nat_dec_lt(v_snd_1403_, v___x_1404_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1407_; 
lean_dec(v_snd_1403_);
lean_dec(v_fvarId_1389_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 1, v_fst_1402_);
v___x_1407_ = v___x_1395_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_varPos_1391_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_fst_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
else
{
lean_object* v_v_1409_; lean_object* v_hyps_1410_; lean_object* v_children_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1425_; 
v_v_1409_ = lean_array_fget(v_fst_1402_, v_snd_1403_);
v_hyps_1410_ = lean_ctor_get(v_v_1409_, 0);
v_children_1411_ = lean_ctor_get(v_v_1409_, 1);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_v_1409_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1413_ = v_v_1409_;
v_isShared_1414_ = v_isSharedCheck_1425_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_children_1411_);
lean_inc(v_hyps_1410_);
lean_dec(v_v_1409_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1425_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; lean_object* v_xs_x27_1416_; lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1415_ = lean_box(0);
v_xs_x27_1416_ = lean_array_fset(v_fst_1402_, v_snd_1403_, v___x_1415_);
v___x_1417_ = lean_array_push(v_hyps_1410_, v_fvarId_1389_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v___x_1417_);
v___x_1419_ = v___x_1413_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_children_1411_);
v___x_1419_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1420_ = lean_array_fset(v_xs_x27_1416_, v_snd_1403_, v___x_1419_);
lean_dec(v_snd_1403_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 1, v___x_1420_);
v___x_1422_ = v___x_1395_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_varPos_1391_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0(lean_object* v_00_u03b2_1429_, lean_object* v_m_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0___redArg(v_m_1430_, v_a_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0___boxed(lean_object* v_00_u03b2_1433_, lean_object* v_m_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0(v_00_u03b2_1433_, v_m_1434_, v_a_1435_);
lean_dec_ref(v_a_1435_);
lean_dec_ref(v_m_1434_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1(lean_object* v_00_u03b2_1437_, lean_object* v_m_1438_, lean_object* v_a_1439_, lean_object* v_b_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1___redArg(v_m_1438_, v_a_1439_, v_b_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0_spec__0(lean_object* v_00_u03b2_1442_, lean_object* v_a_1443_, lean_object* v_x_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0_spec__0___redArg(v_a_1443_, v_x_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1446_, lean_object* v_a_1447_, lean_object* v_x_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0_spec__0(v_00_u03b2_1446_, v_a_1447_, v_x_1448_);
lean_dec(v_x_1448_);
lean_dec_ref(v_a_1447_);
return v_res_1449_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__2(lean_object* v_00_u03b2_1450_, lean_object* v_a_1451_, lean_object* v_x_1452_){
_start:
{
uint8_t v___x_1453_; 
v___x_1453_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__2___redArg(v_a_1451_, v_x_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1454_, lean_object* v_a_1455_, lean_object* v_x_1456_){
_start:
{
uint8_t v_res_1457_; lean_object* v_r_1458_; 
v_res_1457_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__2(v_00_u03b2_1454_, v_a_1455_, v_x_1456_);
lean_dec(v_x_1456_);
lean_dec_ref(v_a_1455_);
v_r_1458_ = lean_box(v_res_1457_);
return v_r_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__3(lean_object* v_00_u03b2_1459_, lean_object* v_data_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__3___redArg(v_data_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__4(lean_object* v_00_u03b2_1462_, lean_object* v_a_1463_, lean_object* v_b_1464_, lean_object* v_x_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__4___redArg(v_a_1463_, v_b_1464_, v_x_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1467_, lean_object* v_i_1468_, lean_object* v_source_1469_, lean_object* v_target_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__3_spec__4___redArg(v_i_1468_, v_source_1469_, v_target_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1472_, lean_object* v_x_1473_, lean_object* v_x_1474_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__1_spec__3_spec__4_spec__6___redArg(v_x_1473_, v_x_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__0___redArg(lean_object* v_e_1476_, lean_object* v___y_1477_){
_start:
{
uint8_t v___x_1479_; 
v___x_1479_ = l_Lean_Expr_hasMVar(v_e_1476_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1480_, 0, v_e_1476_);
return v___x_1480_;
}
else
{
lean_object* v___x_1481_; lean_object* v_mctx_1482_; lean_object* v___x_1483_; lean_object* v_fst_1484_; lean_object* v_snd_1485_; lean_object* v___x_1486_; lean_object* v_cache_1487_; lean_object* v_zetaDeltaFVarIds_1488_; lean_object* v_postponed_1489_; lean_object* v_diag_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1499_; 
v___x_1481_ = lean_st_ref_get(v___y_1477_);
v_mctx_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc_ref(v_mctx_1482_);
lean_dec(v___x_1481_);
v___x_1483_ = l_Lean_instantiateMVarsCore(v_mctx_1482_, v_e_1476_);
v_fst_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_fst_1484_);
v_snd_1485_ = lean_ctor_get(v___x_1483_, 1);
lean_inc(v_snd_1485_);
lean_dec_ref(v___x_1483_);
v___x_1486_ = lean_st_ref_take(v___y_1477_);
v_cache_1487_ = lean_ctor_get(v___x_1486_, 1);
v_zetaDeltaFVarIds_1488_ = lean_ctor_get(v___x_1486_, 2);
v_postponed_1489_ = lean_ctor_get(v___x_1486_, 3);
v_diag_1490_ = lean_ctor_get(v___x_1486_, 4);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1499_ == 0)
{
lean_object* v_unused_1500_; 
v_unused_1500_ = lean_ctor_get(v___x_1486_, 0);
lean_dec(v_unused_1500_);
v___x_1492_ = v___x_1486_;
v_isShared_1493_ = v_isSharedCheck_1499_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_diag_1490_);
lean_inc(v_postponed_1489_);
lean_inc(v_zetaDeltaFVarIds_1488_);
lean_inc(v_cache_1487_);
lean_dec(v___x_1486_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1499_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v_snd_1485_);
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_snd_1485_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_cache_1487_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_zetaDeltaFVarIds_1488_);
lean_ctor_set(v_reuseFailAlloc_1498_, 3, v_postponed_1489_);
lean_ctor_set(v_reuseFailAlloc_1498_, 4, v_diag_1490_);
v___x_1495_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = lean_st_ref_put(v___y_1477_, v___x_1495_);
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v_fst_1484_);
return v___x_1497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__0___redArg___boxed(lean_object* v_e_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__0___redArg(v_e_1501_, v___y_1502_);
lean_dec(v___y_1502_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__0(lean_object* v_e_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__0___redArg(v_e_1505_, v___y_1507_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__0___boxed(lean_object* v_e_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__0(v_e_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_1519_, size_t v_sz_1520_, size_t v_i_1521_, lean_object* v_b_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
uint8_t v___x_1528_; 
v___x_1528_ = lean_usize_dec_lt(v_i_1521_, v_sz_1520_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1529_, 0, v_b_1522_);
return v___x_1529_;
}
else
{
lean_object* v_snd_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1574_; 
v_snd_1530_ = lean_ctor_get(v_b_1522_, 1);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_b_1522_);
if (v_isSharedCheck_1574_ == 0)
{
lean_object* v_unused_1575_; 
v_unused_1575_ = lean_ctor_get(v_b_1522_, 0);
lean_dec(v_unused_1575_);
v___x_1532_ = v_b_1522_;
v_isShared_1533_ = v_isSharedCheck_1574_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_snd_1530_);
lean_dec(v_b_1522_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1574_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v_a_1536_; lean_object* v_a_1543_; 
v___x_1534_ = lean_box(0);
v_a_1543_ = lean_array_uget_borrowed(v_as_1519_, v_i_1521_);
if (lean_obj_tag(v_a_1543_) == 0)
{
v_a_1536_ = v_snd_1530_;
goto v___jp_1535_;
}
else
{
lean_object* v_val_1544_; uint8_t v___x_1545_; 
v_val_1544_ = lean_ctor_get(v_a_1543_, 0);
v___x_1545_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = l_Lean_LocalDecl_type(v_val_1544_);
v___x_1547_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__0___redArg(v___x_1546_, v___y_1524_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; uint8_t v___x_1549_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1547_, 1);
v___x_1549_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_a_1548_);
if (v___x_1549_ == 0)
{
lean_dec(v_a_1548_);
v_a_1536_ = v_snd_1530_;
goto v___jp_1535_;
}
else
{
lean_object* v_varPos_1550_; lean_object* v___x_1551_; 
v_varPos_1550_ = lean_ctor_get(v_snd_1530_, 0);
v___x_1551_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests(v_varPos_1550_, v_a_1548_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v_a_1548_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1551_, 1);
v___x_1553_ = lean_array_get_size(v_a_1552_);
v___x_1554_ = lean_unsigned_to_nat(0u);
v___x_1555_ = lean_nat_dec_eq(v___x_1553_, v___x_1554_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = l_Lean_LocalDecl_fvarId(v_val_1544_);
v___x_1557_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert(v_snd_1530_, v___x_1556_, v_a_1552_);
v_a_1536_ = v___x_1557_;
goto v___jp_1535_;
}
else
{
lean_dec(v_a_1552_);
v_a_1536_ = v_snd_1530_;
goto v___jp_1535_;
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_del_object(v___x_1532_);
lean_dec(v_snd_1530_);
v_a_1558_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1551_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1551_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_del_object(v___x_1532_);
lean_dec(v_snd_1530_);
v_a_1566_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1547_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1547_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
else
{
v_a_1536_ = v_snd_1530_;
goto v___jp_1535_;
}
}
v___jp_1535_:
{
lean_object* v___x_1538_; 
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 1, v_a_1536_);
lean_ctor_set(v___x_1532_, 0, v___x_1534_);
v___x_1538_ = v___x_1532_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1534_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_a_1536_);
v___x_1538_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
size_t v___x_1539_; size_t v___x_1540_; 
v___x_1539_ = ((size_t)1ULL);
v___x_1540_ = lean_usize_add(v_i_1521_, v___x_1539_);
v_i_1521_ = v___x_1540_;
v_b_1522_ = v___x_1538_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_1576_, lean_object* v_sz_1577_, lean_object* v_i_1578_, lean_object* v_b_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
size_t v_sz_boxed_1585_; size_t v_i_boxed_1586_; lean_object* v_res_1587_; 
v_sz_boxed_1585_ = lean_unbox_usize(v_sz_1577_);
lean_dec(v_sz_1577_);
v_i_boxed_1586_ = lean_unbox_usize(v_i_1578_);
lean_dec(v_i_1578_);
v_res_1587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1_spec__3_spec__4(v_as_1576_, v_sz_boxed_1585_, v_i_boxed_1586_, v_b_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec_ref(v_as_1576_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1_spec__3(lean_object* v_as_1588_, size_t v_sz_1589_, size_t v_i_1590_, lean_object* v_b_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
uint8_t v___x_1597_; 
v___x_1597_ = lean_usize_dec_lt(v_i_1590_, v_sz_1589_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1598_, 0, v_b_1591_);
return v___x_1598_;
}
else
{
lean_object* v_snd_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1643_; 
v_snd_1599_ = lean_ctor_get(v_b_1591_, 1);
v_isSharedCheck_1643_ = !lean_is_exclusive(v_b_1591_);
if (v_isSharedCheck_1643_ == 0)
{
lean_object* v_unused_1644_; 
v_unused_1644_ = lean_ctor_get(v_b_1591_, 0);
lean_dec(v_unused_1644_);
v___x_1601_ = v_b_1591_;
v_isShared_1602_ = v_isSharedCheck_1643_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_snd_1599_);
lean_dec(v_b_1591_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1643_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; lean_object* v_a_1605_; lean_object* v_a_1612_; 
v___x_1603_ = lean_box(0);
v_a_1612_ = lean_array_uget_borrowed(v_as_1588_, v_i_1590_);
if (lean_obj_tag(v_a_1612_) == 0)
{
v_a_1605_ = v_snd_1599_;
goto v___jp_1604_;
}
else
{
lean_object* v_val_1613_; uint8_t v___x_1614_; 
v_val_1613_ = lean_ctor_get(v_a_1612_, 0);
v___x_1614_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = l_Lean_LocalDecl_type(v_val_1613_);
v___x_1616_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__0___redArg(v___x_1615_, v___y_1593_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; uint8_t v___x_1618_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1616_, 1);
v___x_1618_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_a_1617_);
if (v___x_1618_ == 0)
{
lean_dec(v_a_1617_);
v_a_1605_ = v_snd_1599_;
goto v___jp_1604_;
}
else
{
lean_object* v_varPos_1619_; lean_object* v___x_1620_; 
v_varPos_1619_ = lean_ctor_get(v_snd_1599_, 0);
v___x_1620_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests(v_varPos_1619_, v_a_1617_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
lean_dec(v_a_1617_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; uint8_t v___x_1624_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
v___x_1622_ = lean_array_get_size(v_a_1621_);
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = lean_nat_dec_eq(v___x_1622_, v___x_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = l_Lean_LocalDecl_fvarId(v_val_1613_);
v___x_1626_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert(v_snd_1599_, v___x_1625_, v_a_1621_);
v_a_1605_ = v___x_1626_;
goto v___jp_1604_;
}
else
{
lean_dec(v_a_1621_);
v_a_1605_ = v_snd_1599_;
goto v___jp_1604_;
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_del_object(v___x_1601_);
lean_dec(v_snd_1599_);
v_a_1627_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1620_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1620_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_del_object(v___x_1601_);
lean_dec(v_snd_1599_);
v_a_1635_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1616_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1616_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
else
{
v_a_1605_ = v_snd_1599_;
goto v___jp_1604_;
}
}
v___jp_1604_:
{
lean_object* v___x_1607_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 1, v_a_1605_);
lean_ctor_set(v___x_1601_, 0, v___x_1603_);
v___x_1607_ = v___x_1601_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_a_1605_);
v___x_1607_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
size_t v___x_1608_; size_t v___x_1609_; lean_object* v___x_1610_; 
v___x_1608_ = ((size_t)1ULL);
v___x_1609_ = lean_usize_add(v_i_1590_, v___x_1608_);
v___x_1610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1_spec__3_spec__4(v_as_1588_, v_sz_1589_, v___x_1609_, v___x_1607_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
return v___x_1610_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1645_, lean_object* v_sz_1646_, lean_object* v_i_1647_, lean_object* v_b_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
size_t v_sz_boxed_1654_; size_t v_i_boxed_1655_; lean_object* v_res_1656_; 
v_sz_boxed_1654_ = lean_unbox_usize(v_sz_1646_);
lean_dec(v_sz_1646_);
v_i_boxed_1655_ = lean_unbox_usize(v_i_1647_);
lean_dec(v_i_1647_);
v_res_1656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1_spec__3(v_as_1645_, v_sz_boxed_1654_, v_i_boxed_1655_, v_b_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec_ref(v_as_1645_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1(lean_object* v_init_1657_, lean_object* v_n_1658_, lean_object* v_b_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
if (lean_obj_tag(v_n_1658_) == 0)
{
lean_object* v_cs_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; size_t v_sz_1668_; size_t v___x_1669_; lean_object* v___x_1670_; 
v_cs_1665_ = lean_ctor_get(v_n_1658_, 0);
v___x_1666_ = lean_box(0);
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
lean_ctor_set(v___x_1667_, 1, v_b_1659_);
v_sz_1668_ = lean_array_size(v_cs_1665_);
v___x_1669_ = ((size_t)0ULL);
v___x_1670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1_spec__2(v_init_1657_, v_cs_1665_, v_sz_1668_, v___x_1669_, v___x_1667_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1685_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1685_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1685_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v_fst_1675_; 
v_fst_1675_ = lean_ctor_get(v_a_1671_, 0);
if (lean_obj_tag(v_fst_1675_) == 0)
{
lean_object* v_snd_1676_; lean_object* v___x_1677_; lean_object* v___x_1679_; 
v_snd_1676_ = lean_ctor_get(v_a_1671_, 1);
lean_inc(v_snd_1676_);
lean_dec(v_a_1671_);
v___x_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1677_, 0, v_snd_1676_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1677_);
v___x_1679_ = v___x_1673_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
else
{
lean_object* v_val_1681_; lean_object* v___x_1683_; 
lean_inc_ref(v_fst_1675_);
lean_dec(v_a_1671_);
v_val_1681_ = lean_ctor_get(v_fst_1675_, 0);
lean_inc(v_val_1681_);
lean_dec_ref_known(v_fst_1675_, 1);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v_val_1681_);
v___x_1683_ = v___x_1673_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_val_1681_);
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
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
v_a_1686_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1670_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1670_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
else
{
lean_object* v_vs_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; size_t v_sz_1697_; size_t v___x_1698_; lean_object* v___x_1699_; 
v_vs_1694_ = lean_ctor_get(v_n_1658_, 0);
v___x_1695_ = lean_box(0);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
lean_ctor_set(v___x_1696_, 1, v_b_1659_);
v_sz_1697_ = lean_array_size(v_vs_1694_);
v___x_1698_ = ((size_t)0ULL);
v___x_1699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1_spec__3(v_vs_1694_, v_sz_1697_, v___x_1698_, v___x_1696_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1714_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1702_ = v___x_1699_;
v_isShared_1703_ = v_isSharedCheck_1714_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1714_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v_fst_1704_; 
v_fst_1704_ = lean_ctor_get(v_a_1700_, 0);
if (lean_obj_tag(v_fst_1704_) == 0)
{
lean_object* v_snd_1705_; lean_object* v___x_1706_; lean_object* v___x_1708_; 
v_snd_1705_ = lean_ctor_get(v_a_1700_, 1);
lean_inc(v_snd_1705_);
lean_dec(v_a_1700_);
v___x_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_snd_1705_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v___x_1706_);
v___x_1708_ = v___x_1702_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
else
{
lean_object* v_val_1710_; lean_object* v___x_1712_; 
lean_inc_ref(v_fst_1704_);
lean_dec(v_a_1700_);
v_val_1710_ = lean_ctor_get(v_fst_1704_, 0);
lean_inc(v_val_1710_);
lean_dec_ref_known(v_fst_1704_, 1);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v_val_1710_);
v___x_1712_ = v___x_1702_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_val_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
v_a_1715_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1699_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1699_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1_spec__2(lean_object* v_init_1723_, lean_object* v_as_1724_, size_t v_sz_1725_, size_t v_i_1726_, lean_object* v_b_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
uint8_t v___x_1733_; 
v___x_1733_ = lean_usize_dec_lt(v_i_1726_, v_sz_1725_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; 
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v_b_1727_);
return v___x_1734_;
}
else
{
lean_object* v_snd_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1769_; 
v_snd_1735_ = lean_ctor_get(v_b_1727_, 1);
v_isSharedCheck_1769_ = !lean_is_exclusive(v_b_1727_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; 
v_unused_1770_ = lean_ctor_get(v_b_1727_, 0);
lean_dec(v_unused_1770_);
v___x_1737_ = v_b_1727_;
v_isShared_1738_ = v_isSharedCheck_1769_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_snd_1735_);
lean_dec(v_b_1727_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1769_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; lean_object* v_a_1740_; lean_object* v___x_1741_; 
v___x_1739_ = lean_box(0);
v_a_1740_ = lean_array_uget_borrowed(v_as_1724_, v_i_1726_);
lean_inc(v_snd_1735_);
v___x_1741_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1(v_init_1723_, v_a_1740_, v_snd_1735_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1760_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1744_ = v___x_1741_;
v_isShared_1745_ = v_isSharedCheck_1760_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1741_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1760_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
if (lean_obj_tag(v_a_1742_) == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1748_; 
v___x_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1746_, 0, v_a_1742_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v___x_1746_);
v___x_1748_ = v___x_1737_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1746_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_snd_1735_);
v___x_1748_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
lean_object* v___x_1750_; 
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1748_);
v___x_1750_ = v___x_1744_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; 
lean_del_object(v___x_1744_);
lean_dec(v_snd_1735_);
v_a_1753_ = lean_ctor_get(v_a_1742_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v_a_1742_, 1);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 1, v_a_1753_);
lean_ctor_set(v___x_1737_, 0, v___x_1739_);
v___x_1755_ = v___x_1737_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_a_1753_);
v___x_1755_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
size_t v___x_1756_; size_t v___x_1757_; 
v___x_1756_ = ((size_t)1ULL);
v___x_1757_ = lean_usize_add(v_i_1726_, v___x_1756_);
v_i_1726_ = v___x_1757_;
v_b_1727_ = v___x_1755_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_del_object(v___x_1737_);
lean_dec(v_snd_1735_);
v_a_1761_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1741_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1741_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1_spec__2___boxed(lean_object* v_init_1771_, lean_object* v_as_1772_, lean_object* v_sz_1773_, lean_object* v_i_1774_, lean_object* v_b_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
size_t v_sz_boxed_1781_; size_t v_i_boxed_1782_; lean_object* v_res_1783_; 
v_sz_boxed_1781_ = lean_unbox_usize(v_sz_1773_);
lean_dec(v_sz_1773_);
v_i_boxed_1782_ = lean_unbox_usize(v_i_1774_);
lean_dec(v_i_1774_);
v_res_1783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1_spec__2(v_init_1771_, v_as_1772_, v_sz_boxed_1781_, v_i_boxed_1782_, v_b_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v_as_1772_);
lean_dec_ref(v_init_1771_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1___boxed(lean_object* v_init_1784_, lean_object* v_n_1785_, lean_object* v_b_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1(v_init_1784_, v_n_1785_, v_b_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec_ref(v_n_1785_);
lean_dec_ref(v_init_1784_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__2_spec__5(lean_object* v_as_1793_, size_t v_sz_1794_, size_t v_i_1795_, lean_object* v_b_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
uint8_t v___x_1802_; 
v___x_1802_ = lean_usize_dec_lt(v_i_1795_, v_sz_1794_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; 
v___x_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1803_, 0, v_b_1796_);
return v___x_1803_;
}
else
{
lean_object* v_snd_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1848_; 
v_snd_1804_ = lean_ctor_get(v_b_1796_, 1);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_b_1796_);
if (v_isSharedCheck_1848_ == 0)
{
lean_object* v_unused_1849_; 
v_unused_1849_ = lean_ctor_get(v_b_1796_, 0);
lean_dec(v_unused_1849_);
v___x_1806_ = v_b_1796_;
v_isShared_1807_ = v_isSharedCheck_1848_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_snd_1804_);
lean_dec(v_b_1796_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1848_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1808_; lean_object* v_a_1810_; lean_object* v_a_1817_; 
v___x_1808_ = lean_box(0);
v_a_1817_ = lean_array_uget_borrowed(v_as_1793_, v_i_1795_);
if (lean_obj_tag(v_a_1817_) == 0)
{
v_a_1810_ = v_snd_1804_;
goto v___jp_1809_;
}
else
{
lean_object* v_val_1818_; uint8_t v___x_1819_; 
v_val_1818_ = lean_ctor_get(v_a_1817_, 0);
v___x_1819_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1818_);
if (v___x_1819_ == 0)
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = l_Lean_LocalDecl_type(v_val_1818_);
v___x_1821_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__0___redArg(v___x_1820_, v___y_1798_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; uint8_t v___x_1823_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1822_);
lean_dec_ref_known(v___x_1821_, 1);
v___x_1823_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_a_1822_);
if (v___x_1823_ == 0)
{
lean_dec(v_a_1822_);
v_a_1810_ = v_snd_1804_;
goto v___jp_1809_;
}
else
{
lean_object* v_varPos_1824_; lean_object* v___x_1825_; 
v_varPos_1824_ = lean_ctor_get(v_snd_1804_, 0);
v___x_1825_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests(v_varPos_1824_, v_a_1822_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
lean_dec(v_a_1822_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1826_);
lean_dec_ref_known(v___x_1825_, 1);
v___x_1827_ = lean_array_get_size(v_a_1826_);
v___x_1828_ = lean_unsigned_to_nat(0u);
v___x_1829_ = lean_nat_dec_eq(v___x_1827_, v___x_1828_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = l_Lean_LocalDecl_fvarId(v_val_1818_);
v___x_1831_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert(v_snd_1804_, v___x_1830_, v_a_1826_);
v_a_1810_ = v___x_1831_;
goto v___jp_1809_;
}
else
{
lean_dec(v_a_1826_);
v_a_1810_ = v_snd_1804_;
goto v___jp_1809_;
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_del_object(v___x_1806_);
lean_dec(v_snd_1804_);
v_a_1832_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1825_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1825_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_del_object(v___x_1806_);
lean_dec(v_snd_1804_);
v_a_1840_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1821_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1821_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
else
{
v_a_1810_ = v_snd_1804_;
goto v___jp_1809_;
}
}
v___jp_1809_:
{
lean_object* v___x_1812_; 
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 1, v_a_1810_);
lean_ctor_set(v___x_1806_, 0, v___x_1808_);
v___x_1812_ = v___x_1806_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1808_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_a_1810_);
v___x_1812_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
size_t v___x_1813_; size_t v___x_1814_; 
v___x_1813_ = ((size_t)1ULL);
v___x_1814_ = lean_usize_add(v_i_1795_, v___x_1813_);
v_i_1795_ = v___x_1814_;
v_b_1796_ = v___x_1812_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__2_spec__5___boxed(lean_object* v_as_1850_, lean_object* v_sz_1851_, lean_object* v_i_1852_, lean_object* v_b_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
size_t v_sz_boxed_1859_; size_t v_i_boxed_1860_; lean_object* v_res_1861_; 
v_sz_boxed_1859_ = lean_unbox_usize(v_sz_1851_);
lean_dec(v_sz_1851_);
v_i_boxed_1860_ = lean_unbox_usize(v_i_1852_);
lean_dec(v_i_1852_);
v_res_1861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__2_spec__5(v_as_1850_, v_sz_boxed_1859_, v_i_boxed_1860_, v_b_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec_ref(v_as_1850_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__2(lean_object* v_as_1862_, size_t v_sz_1863_, size_t v_i_1864_, lean_object* v_b_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
uint8_t v___x_1871_; 
v___x_1871_ = lean_usize_dec_lt(v_i_1864_, v_sz_1863_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v_b_1865_);
return v___x_1872_;
}
else
{
lean_object* v_snd_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1917_; 
v_snd_1873_ = lean_ctor_get(v_b_1865_, 1);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_b_1865_);
if (v_isSharedCheck_1917_ == 0)
{
lean_object* v_unused_1918_; 
v_unused_1918_ = lean_ctor_get(v_b_1865_, 0);
lean_dec(v_unused_1918_);
v___x_1875_ = v_b_1865_;
v_isShared_1876_ = v_isSharedCheck_1917_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_snd_1873_);
lean_dec(v_b_1865_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1917_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; lean_object* v_a_1879_; lean_object* v_a_1886_; 
v___x_1877_ = lean_box(0);
v_a_1886_ = lean_array_uget_borrowed(v_as_1862_, v_i_1864_);
if (lean_obj_tag(v_a_1886_) == 0)
{
v_a_1879_ = v_snd_1873_;
goto v___jp_1878_;
}
else
{
lean_object* v_val_1887_; uint8_t v___x_1888_; 
v_val_1887_ = lean_ctor_get(v_a_1886_, 0);
v___x_1888_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1887_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = l_Lean_LocalDecl_type(v_val_1887_);
v___x_1890_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__0___redArg(v___x_1889_, v___y_1867_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; uint8_t v___x_1892_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc(v_a_1891_);
lean_dec_ref_known(v___x_1890_, 1);
v___x_1892_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_a_1891_);
if (v___x_1892_ == 0)
{
lean_dec(v_a_1891_);
v_a_1879_ = v_snd_1873_;
goto v___jp_1878_;
}
else
{
lean_object* v_varPos_1893_; lean_object* v___x_1894_; 
v_varPos_1893_ = lean_ctor_get(v_snd_1873_, 0);
v___x_1894_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests(v_varPos_1893_, v_a_1891_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v_a_1891_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_a_1895_);
lean_dec_ref_known(v___x_1894_, 1);
v___x_1896_ = lean_array_get_size(v_a_1895_);
v___x_1897_ = lean_unsigned_to_nat(0u);
v___x_1898_ = lean_nat_dec_eq(v___x_1896_, v___x_1897_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = l_Lean_LocalDecl_fvarId(v_val_1887_);
v___x_1900_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert(v_snd_1873_, v___x_1899_, v_a_1895_);
v_a_1879_ = v___x_1900_;
goto v___jp_1878_;
}
else
{
lean_dec(v_a_1895_);
v_a_1879_ = v_snd_1873_;
goto v___jp_1878_;
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_del_object(v___x_1875_);
lean_dec(v_snd_1873_);
v_a_1901_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1894_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1894_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_del_object(v___x_1875_);
lean_dec(v_snd_1873_);
v_a_1909_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1890_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1890_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
else
{
v_a_1879_ = v_snd_1873_;
goto v___jp_1878_;
}
}
v___jp_1878_:
{
lean_object* v___x_1881_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 1, v_a_1879_);
lean_ctor_set(v___x_1875_, 0, v___x_1877_);
v___x_1881_ = v___x_1875_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_a_1879_);
v___x_1881_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
size_t v___x_1882_; size_t v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = ((size_t)1ULL);
v___x_1883_ = lean_usize_add(v_i_1864_, v___x_1882_);
v___x_1884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__2_spec__5(v_as_1862_, v_sz_1863_, v___x_1883_, v___x_1881_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
return v___x_1884_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__2___boxed(lean_object* v_as_1919_, lean_object* v_sz_1920_, lean_object* v_i_1921_, lean_object* v_b_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
size_t v_sz_boxed_1928_; size_t v_i_boxed_1929_; lean_object* v_res_1930_; 
v_sz_boxed_1928_ = lean_unbox_usize(v_sz_1920_);
lean_dec(v_sz_1920_);
v_i_boxed_1929_ = lean_unbox_usize(v_i_1921_);
lean_dec(v_i_1921_);
v_res_1930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__2(v_as_1919_, v_sz_boxed_1928_, v_i_boxed_1929_, v_b_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec_ref(v_as_1919_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1(lean_object* v_t_1931_, lean_object* v_init_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_root_1938_; lean_object* v_tail_1939_; lean_object* v___x_1940_; 
v_root_1938_ = lean_ctor_get(v_t_1931_, 0);
v_tail_1939_ = lean_ctor_get(v_t_1931_, 1);
lean_inc_ref(v_init_1932_);
v___x_1940_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__1(v_init_1932_, v_root_1938_, v_init_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec_ref(v_init_1932_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1977_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1943_ = v___x_1940_;
v_isShared_1944_ = v_isSharedCheck_1977_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1940_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1977_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
if (lean_obj_tag(v_a_1941_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1947_; 
v_a_1945_ = lean_ctor_get(v_a_1941_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v_a_1941_, 1);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v_a_1945_);
v___x_1947_ = v___x_1943_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; size_t v_sz_1952_; size_t v___x_1953_; lean_object* v___x_1954_; 
lean_del_object(v___x_1943_);
v_a_1949_ = lean_ctor_get(v_a_1941_, 0);
lean_inc(v_a_1949_);
lean_dec_ref_known(v_a_1941_, 1);
v___x_1950_ = lean_box(0);
v___x_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
lean_ctor_set(v___x_1951_, 1, v_a_1949_);
v_sz_1952_ = lean_array_size(v_tail_1939_);
v___x_1953_ = ((size_t)0ULL);
v___x_1954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1_spec__2(v_tail_1939_, v_sz_1952_, v___x_1953_, v___x_1951_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1968_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1968_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1968_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v_fst_1959_; 
v_fst_1959_ = lean_ctor_get(v_a_1955_, 0);
if (lean_obj_tag(v_fst_1959_) == 0)
{
lean_object* v_snd_1960_; lean_object* v___x_1962_; 
v_snd_1960_ = lean_ctor_get(v_a_1955_, 1);
lean_inc(v_snd_1960_);
lean_dec(v_a_1955_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v_snd_1960_);
v___x_1962_ = v___x_1957_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_snd_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
else
{
lean_object* v_val_1964_; lean_object* v___x_1966_; 
lean_inc_ref(v_fst_1959_);
lean_dec(v_a_1955_);
v_val_1964_ = lean_ctor_get(v_fst_1959_, 0);
lean_inc(v_val_1964_);
lean_dec_ref_known(v_fst_1959_, 1);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v_val_1964_);
v___x_1966_ = v___x_1957_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_val_1964_);
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
v_a_1969_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1954_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1954_);
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
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
v_a_1978_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1940_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1940_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1___boxed(lean_object* v_t_1986_, lean_object* v_init_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1(v_t_1986_, v_init_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec_ref(v_t_1986_);
return v_res_1993_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex___closed__0(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1994_ = lean_obj_once(&l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__3, &l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__3_once, _init_l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__3);
v___x_1995_ = lean_unsigned_to_nat(1u);
v___x_1996_ = lean_mk_empty_array_with_capacity(v___x_1995_);
v___x_1997_ = lean_array_push(v___x_1996_, v___x_1994_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex(lean_object* v_tree_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars(v_tree_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_lctx_2005_; lean_object* v_a_2006_; lean_object* v_decls_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v_lctx_2005_ = lean_ctor_get(v_a_1999_, 2);
v_a_2006_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2006_);
lean_dec_ref_known(v___x_2004_, 1);
v_decls_2007_ = lean_ctor_get(v_lctx_2005_, 1);
v___x_2008_ = lean_obj_once(&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex___closed__0, &l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex___closed__0_once, _init_l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex___closed__0);
v___x_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2009_, 0, v_a_2006_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__1(v_decls_2007_, v___x_2009_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
return v___x_2010_;
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
v_a_2011_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_2004_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2004_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex___boxed(lean_object* v_tree_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex(v_tree_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_);
lean_dec(v_a_2023_);
lean_dec_ref(v_a_2022_);
lean_dec(v_a_2021_);
lean_dec_ref(v_a_2020_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__3(lean_object* v_index_2026_, lean_object* v_as_2027_, size_t v_sz_2028_, size_t v_i_2029_, lean_object* v_b_2030_){
_start:
{
lean_object* v_a_2032_; uint8_t v___x_2036_; 
v___x_2036_ = lean_usize_dec_lt(v_i_2029_, v_sz_2028_);
if (v___x_2036_ == 0)
{
return v_b_2030_;
}
else
{
lean_object* v_a_2037_; lean_object* v_snd_2038_; uint8_t v___x_2039_; 
v_a_2037_ = lean_array_uget_borrowed(v_as_2027_, v_i_2029_);
v_snd_2038_ = lean_ctor_get(v_a_2037_, 1);
v___x_2039_ = lean_unbox(v_snd_2038_);
if (v___x_2039_ == 0)
{
v_a_2032_ = v_b_2030_;
goto v___jp_2031_;
}
else
{
lean_object* v_fst_2040_; lean_object* v_nodes_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v_hyps_2044_; lean_object* v___x_2045_; 
v_fst_2040_ = lean_ctor_get(v_a_2037_, 0);
v_nodes_2041_ = lean_ctor_get(v_index_2026_, 1);
v___x_2042_ = l_Lean_Meta_Match_DiteTree_instInhabitedNode_default;
v___x_2043_ = lean_array_get_borrowed(v___x_2042_, v_nodes_2041_, v_fst_2040_);
v_hyps_2044_ = lean_ctor_get(v___x_2043_, 0);
v___x_2045_ = l_Array_append___redArg(v_b_2030_, v_hyps_2044_);
v_a_2032_ = v___x_2045_;
goto v___jp_2031_;
}
}
v___jp_2031_:
{
size_t v___x_2033_; size_t v___x_2034_; 
v___x_2033_ = ((size_t)1ULL);
v___x_2034_ = lean_usize_add(v_i_2029_, v___x_2033_);
v_i_2029_ = v___x_2034_;
v_b_2030_ = v_a_2032_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__3___boxed(lean_object* v_index_2046_, lean_object* v_as_2047_, lean_object* v_sz_2048_, lean_object* v_i_2049_, lean_object* v_b_2050_){
_start:
{
size_t v_sz_boxed_2051_; size_t v_i_boxed_2052_; lean_object* v_res_2053_; 
v_sz_boxed_2051_ = lean_unbox_usize(v_sz_2048_);
lean_dec(v_sz_2048_);
v_i_boxed_2052_ = lean_unbox_usize(v_i_2049_);
lean_dec(v_i_2049_);
v_res_2053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__3(v_index_2046_, v_as_2047_, v_sz_boxed_2051_, v_i_boxed_2052_, v_b_2050_);
lean_dec_ref(v_as_2047_);
lean_dec_ref(v_index_2046_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__0(lean_object* v_index_2054_, lean_object* v_a_2055_, uint8_t v___y_2056_, lean_object* v_as_2057_, size_t v_sz_2058_, size_t v_i_2059_, lean_object* v_b_2060_){
_start:
{
lean_object* v_a_2062_; uint8_t v___x_2066_; 
v___x_2066_ = lean_usize_dec_lt(v_i_2059_, v_sz_2058_);
if (v___x_2066_ == 0)
{
return v_b_2060_;
}
else
{
lean_object* v_a_2067_; lean_object* v_fst_2068_; lean_object* v_snd_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2088_; 
v_a_2067_ = lean_array_uget(v_as_2057_, v_i_2059_);
v_fst_2068_ = lean_ctor_get(v_a_2067_, 0);
v_snd_2069_ = lean_ctor_get(v_a_2067_, 1);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_a_2067_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2071_ = v_a_2067_;
v_isShared_2072_ = v_isSharedCheck_2088_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_snd_2069_);
lean_inc(v_fst_2068_);
lean_dec(v_a_2067_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2088_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v_nodes_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v_children_2076_; lean_object* v___x_2077_; 
v_nodes_2073_ = lean_ctor_get(v_index_2054_, 1);
v___x_2074_ = l_Lean_Meta_Match_DiteTree_instInhabitedNode_default;
v___x_2075_ = lean_array_get_borrowed(v___x_2074_, v_nodes_2073_, v_fst_2068_);
lean_dec(v_fst_2068_);
v_children_2076_ = lean_ctor_get(v___x_2075_, 1);
v___x_2077_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_insert_spec__0___redArg(v_children_2076_, v_a_2055_);
if (lean_obj_tag(v___x_2077_) == 1)
{
lean_object* v_val_2078_; uint8_t v___y_2080_; uint8_t v___x_2086_; 
v_val_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_val_2078_);
lean_dec_ref_known(v___x_2077_, 1);
v___x_2086_ = lean_unbox(v_snd_2069_);
if (v___x_2086_ == 0)
{
lean_dec(v_snd_2069_);
v___y_2080_ = v___y_2056_;
goto v___jp_2079_;
}
else
{
uint8_t v___x_2087_; 
v___x_2087_ = lean_unbox(v_snd_2069_);
lean_dec(v_snd_2069_);
v___y_2080_ = v___x_2087_;
goto v___jp_2079_;
}
v___jp_2079_:
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2081_ = lean_box(v___y_2080_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 1, v___x_2081_);
lean_ctor_set(v___x_2071_, 0, v_val_2078_);
v___x_2083_ = v___x_2071_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_val_2078_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_array_push(v_b_2060_, v___x_2083_);
v_a_2062_ = v___x_2084_;
goto v___jp_2061_;
}
}
}
else
{
lean_dec(v___x_2077_);
lean_del_object(v___x_2071_);
lean_dec(v_snd_2069_);
v_a_2062_ = v_b_2060_;
goto v___jp_2061_;
}
}
}
v___jp_2061_:
{
size_t v___x_2063_; size_t v___x_2064_; 
v___x_2063_ = ((size_t)1ULL);
v___x_2064_ = lean_usize_add(v_i_2059_, v___x_2063_);
v_i_2059_ = v___x_2064_;
v_b_2060_ = v_a_2062_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__0___boxed(lean_object* v_index_2089_, lean_object* v_a_2090_, lean_object* v___y_2091_, lean_object* v_as_2092_, lean_object* v_sz_2093_, lean_object* v_i_2094_, lean_object* v_b_2095_){
_start:
{
uint8_t v___y_1822__boxed_2096_; size_t v_sz_boxed_2097_; size_t v_i_boxed_2098_; lean_object* v_res_2099_; 
v___y_1822__boxed_2096_ = lean_unbox(v___y_2091_);
v_sz_boxed_2097_ = lean_unbox_usize(v_sz_2093_);
lean_dec(v_sz_2093_);
v_i_boxed_2098_ = lean_unbox_usize(v_i_2094_);
lean_dec(v_i_2094_);
v_res_2099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__0(v_index_2089_, v_a_2090_, v___y_1822__boxed_2096_, v_as_2092_, v_sz_boxed_2097_, v_i_boxed_2098_, v_b_2095_);
lean_dec_ref(v_as_2092_);
lean_dec_ref(v_a_2090_);
lean_dec_ref(v_index_2089_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__2(lean_object* v_index_2100_, lean_object* v_test_2101_, lean_object* v_as_2102_, size_t v_sz_2103_, size_t v_i_2104_, lean_object* v_b_2105_){
_start:
{
uint8_t v___x_2106_; 
v___x_2106_ = lean_usize_dec_lt(v_i_2104_, v_sz_2103_);
if (v___x_2106_ == 0)
{
return v_b_2105_;
}
else
{
lean_object* v_a_2107_; uint8_t v___y_2109_; lean_object* v_fst_2116_; lean_object* v_snd_2117_; lean_object* v_fst_2118_; lean_object* v_snd_2119_; uint8_t v___x_2120_; 
v_a_2107_ = lean_array_uget_borrowed(v_as_2102_, v_i_2104_);
v_fst_2116_ = lean_ctor_get(v_a_2107_, 0);
v_snd_2117_ = lean_ctor_get(v_a_2107_, 1);
v_fst_2118_ = lean_ctor_get(v_test_2101_, 0);
v_snd_2119_ = lean_ctor_get(v_test_2101_, 1);
v___x_2120_ = l_Lean_instBEqFVarId_beq(v_fst_2116_, v_fst_2118_);
if (v___x_2120_ == 0)
{
v___y_2109_ = v___x_2120_;
goto v___jp_2108_;
}
else
{
uint8_t v___x_2121_; 
v___x_2121_ = lean_expr_eqv(v_snd_2117_, v_snd_2119_);
v___y_2109_ = v___x_2121_;
goto v___jp_2108_;
}
v___jp_2108_:
{
size_t v_sz_2110_; size_t v___x_2111_; lean_object* v___x_2112_; size_t v___x_2113_; size_t v___x_2114_; 
v_sz_2110_ = lean_array_size(v_b_2105_);
v___x_2111_ = ((size_t)0ULL);
lean_inc_ref(v_b_2105_);
v___x_2112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__0(v_index_2100_, v_a_2107_, v___y_2109_, v_b_2105_, v_sz_2110_, v___x_2111_, v_b_2105_);
lean_dec_ref(v_b_2105_);
v___x_2113_ = ((size_t)1ULL);
v___x_2114_ = lean_usize_add(v_i_2104_, v___x_2113_);
v_i_2104_ = v___x_2114_;
v_b_2105_ = v___x_2112_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__2___boxed(lean_object* v_index_2122_, lean_object* v_test_2123_, lean_object* v_as_2124_, lean_object* v_sz_2125_, lean_object* v_i_2126_, lean_object* v_b_2127_){
_start:
{
size_t v_sz_boxed_2128_; size_t v_i_boxed_2129_; lean_object* v_res_2130_; 
v_sz_boxed_2128_ = lean_unbox_usize(v_sz_2125_);
lean_dec(v_sz_2125_);
v_i_boxed_2129_ = lean_unbox_usize(v_i_2126_);
lean_dec(v_i_2126_);
v_res_2130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__2(v_index_2122_, v_test_2123_, v_as_2124_, v_sz_boxed_2128_, v_i_boxed_2129_, v_b_2127_);
lean_dec_ref(v_as_2124_);
lean_dec_ref(v_test_2123_);
lean_dec_ref(v_index_2122_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__1_spec__1(lean_object* v_index_2131_, lean_object* v_as_2132_, size_t v_i_2133_, size_t v_stop_2134_, lean_object* v_b_2135_){
_start:
{
lean_object* v___y_2137_; uint8_t v___x_2141_; 
v___x_2141_ = lean_usize_dec_eq(v_i_2133_, v_stop_2134_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; lean_object* v_test_2143_; lean_object* v_varPos_2144_; lean_object* v_fst_2145_; uint8_t v___x_2146_; 
v___x_2142_ = lean_array_uget_borrowed(v_as_2132_, v_i_2133_);
v_test_2143_ = lean_ctor_get(v___x_2142_, 0);
v_varPos_2144_ = lean_ctor_get(v_index_2131_, 0);
v_fst_2145_ = lean_ctor_get(v_test_2143_, 0);
v___x_2146_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit_spec__0___redArg(v_varPos_2144_, v_fst_2145_);
if (v___x_2146_ == 0)
{
v___y_2137_ = v_b_2135_;
goto v___jp_2136_;
}
else
{
lean_object* v___x_2147_; 
lean_inc_ref(v_test_2143_);
v___x_2147_ = lean_array_push(v_b_2135_, v_test_2143_);
v___y_2137_ = v___x_2147_;
goto v___jp_2136_;
}
}
else
{
return v_b_2135_;
}
v___jp_2136_:
{
size_t v___x_2138_; size_t v___x_2139_; 
v___x_2138_ = ((size_t)1ULL);
v___x_2139_ = lean_usize_add(v_i_2133_, v___x_2138_);
v_i_2133_ = v___x_2139_;
v_b_2135_ = v___y_2137_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__1_spec__1___boxed(lean_object* v_index_2148_, lean_object* v_as_2149_, lean_object* v_i_2150_, lean_object* v_stop_2151_, lean_object* v_b_2152_){
_start:
{
size_t v_i_boxed_2153_; size_t v_stop_boxed_2154_; lean_object* v_res_2155_; 
v_i_boxed_2153_ = lean_unbox_usize(v_i_2150_);
lean_dec(v_i_2150_);
v_stop_boxed_2154_ = lean_unbox_usize(v_stop_2151_);
lean_dec(v_stop_2151_);
v_res_2155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__1_spec__1(v_index_2148_, v_as_2149_, v_i_boxed_2153_, v_stop_boxed_2154_, v_b_2152_);
lean_dec_ref(v_as_2149_);
lean_dec_ref(v_index_2148_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__1(lean_object* v_index_2156_, lean_object* v_as_2157_, lean_object* v_start_2158_, lean_object* v_stop_2159_){
_start:
{
lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2160_ = ((lean_object*)(l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectTests___closed__0));
v___x_2161_ = lean_nat_dec_lt(v_start_2158_, v_stop_2159_);
if (v___x_2161_ == 0)
{
return v___x_2160_;
}
else
{
lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2162_ = lean_array_get_size(v_as_2157_);
v___x_2163_ = lean_nat_dec_le(v_stop_2159_, v___x_2162_);
if (v___x_2163_ == 0)
{
uint8_t v___x_2164_; 
v___x_2164_ = lean_nat_dec_lt(v_start_2158_, v___x_2162_);
if (v___x_2164_ == 0)
{
return v___x_2160_;
}
else
{
size_t v___x_2165_; size_t v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = lean_usize_of_nat(v_start_2158_);
v___x_2166_ = lean_usize_of_nat(v___x_2162_);
v___x_2167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__1_spec__1(v_index_2156_, v_as_2157_, v___x_2165_, v___x_2166_, v___x_2160_);
return v___x_2167_;
}
}
else
{
size_t v___x_2168_; size_t v___x_2169_; lean_object* v___x_2170_; 
v___x_2168_ = lean_usize_of_nat(v_start_2158_);
v___x_2169_ = lean_usize_of_nat(v_stop_2159_);
v___x_2170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__1_spec__1(v_index_2156_, v_as_2157_, v___x_2168_, v___x_2169_, v___x_2160_);
return v___x_2170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__1___boxed(lean_object* v_index_2171_, lean_object* v_as_2172_, lean_object* v_start_2173_, lean_object* v_stop_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_Array_filterMapM___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__1(v_index_2171_, v_as_2172_, v_start_2173_, v_stop_2174_);
lean_dec(v_stop_2174_);
lean_dec(v_start_2173_);
lean_dec_ref(v_as_2172_);
lean_dec_ref(v_index_2171_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve(lean_object* v_index_2184_, lean_object* v_kept_2185_, lean_object* v_test_2186_){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v_tests_2189_; lean_object* v_active_2190_; lean_object* v___x_2191_; size_t v_sz_2192_; size_t v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; size_t v_sz_2196_; lean_object* v___x_2197_; 
v___x_2187_ = lean_unsigned_to_nat(0u);
v___x_2188_ = lean_array_get_size(v_kept_2185_);
v_tests_2189_ = l_Array_filterMapM___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__1(v_index_2184_, v_kept_2185_, v___x_2187_, v___x_2188_);
v_active_2190_ = ((lean_object*)(l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve___closed__1));
v___x_2191_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_sort(v_index_2184_, v_tests_2189_);
v_sz_2192_ = lean_array_size(v___x_2191_);
v___x_2193_ = ((size_t)0ULL);
v___x_2194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__2(v_index_2184_, v_test_2186_, v___x_2191_, v_sz_2192_, v___x_2193_, v_active_2190_);
lean_dec_ref(v___x_2191_);
v___x_2195_ = ((lean_object*)(l_Lean_Meta_Match_DiteTree_instInhabitedNode_default___closed__0));
v_sz_2196_ = lean_array_size(v___x_2194_);
v___x_2197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve_spec__3(v_index_2184_, v___x_2194_, v_sz_2196_, v___x_2193_, v___x_2195_);
lean_dec_ref(v___x_2194_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve___boxed(lean_object* v_index_2198_, lean_object* v_kept_2199_, lean_object* v_test_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve(v_index_2198_, v_kept_2199_, v_test_2200_);
lean_dec_ref(v_test_2200_);
lean_dec_ref(v_kept_2199_);
lean_dec_ref(v_index_2198_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__2___redArg(lean_object* v_mvarId_2202_, lean_object* v_x_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2202_, v_x_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2209_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2209_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
v_a_2218_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2209_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2209_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__2___redArg___boxed(lean_object* v_mvarId_2226_, lean_object* v_x_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__2___redArg(v_mvarId_2226_, v_x_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__2(lean_object* v_00_u03b1_2234_, lean_object* v_mvarId_2235_, lean_object* v_x_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__2___redArg(v_mvarId_2235_, v_x_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__2___boxed(lean_object* v_00_u03b1_2243_, lean_object* v_mvarId_2244_, lean_object* v_x_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__2(v_00_u03b1_2243_, v_mvarId_2244_, v_x_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_2252_, lean_object* v_x_2253_, lean_object* v_x_2254_, lean_object* v_x_2255_){
_start:
{
lean_object* v_ks_2256_; lean_object* v_vs_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2281_; 
v_ks_2256_ = lean_ctor_get(v_x_2252_, 0);
v_vs_2257_ = lean_ctor_get(v_x_2252_, 1);
v_isSharedCheck_2281_ = !lean_is_exclusive(v_x_2252_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2259_ = v_x_2252_;
v_isShared_2260_ = v_isSharedCheck_2281_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_vs_2257_);
lean_inc(v_ks_2256_);
lean_dec(v_x_2252_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2281_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2261_; uint8_t v___x_2262_; 
v___x_2261_ = lean_array_get_size(v_ks_2256_);
v___x_2262_ = lean_nat_dec_lt(v_x_2253_, v___x_2261_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2266_; 
lean_dec(v_x_2253_);
v___x_2263_ = lean_array_push(v_ks_2256_, v_x_2254_);
v___x_2264_ = lean_array_push(v_vs_2257_, v_x_2255_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 1, v___x_2264_);
lean_ctor_set(v___x_2259_, 0, v___x_2263_);
v___x_2266_ = v___x_2259_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2263_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2264_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
else
{
lean_object* v_k_x27_2268_; uint8_t v___x_2269_; 
v_k_x27_2268_ = lean_array_fget_borrowed(v_ks_2256_, v_x_2253_);
v___x_2269_ = l_Lean_instBEqMVarId_beq(v_x_2254_, v_k_x27_2268_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2271_; 
if (v_isShared_2260_ == 0)
{
v___x_2271_ = v___x_2259_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_ks_2256_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v_vs_2257_);
v___x_2271_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = lean_unsigned_to_nat(1u);
v___x_2273_ = lean_nat_add(v_x_2253_, v___x_2272_);
lean_dec(v_x_2253_);
v_x_2252_ = v___x_2271_;
v_x_2253_ = v___x_2273_;
goto _start;
}
}
else
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2279_; 
v___x_2276_ = lean_array_fset(v_ks_2256_, v_x_2253_, v_x_2254_);
v___x_2277_ = lean_array_fset(v_vs_2257_, v_x_2253_, v_x_2255_);
lean_dec(v_x_2253_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 1, v___x_2277_);
lean_ctor_set(v___x_2259_, 0, v___x_2276_);
v___x_2279_ = v___x_2259_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v___x_2277_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__4___redArg(lean_object* v_n_2282_, lean_object* v_k_2283_, lean_object* v_v_2284_){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = lean_unsigned_to_nat(0u);
v___x_2286_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_n_2282_, v___x_2285_, v_k_2283_, v_v_2284_);
return v___x_2286_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2287_; 
v___x_2287_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3___redArg(lean_object* v_x_2288_, size_t v_x_2289_, size_t v_x_2290_, lean_object* v_x_2291_, lean_object* v_x_2292_){
_start:
{
if (lean_obj_tag(v_x_2288_) == 0)
{
lean_object* v_es_2293_; size_t v___x_2294_; size_t v___x_2295_; lean_object* v_j_2296_; lean_object* v___x_2297_; uint8_t v___x_2298_; 
v_es_2293_ = lean_ctor_get(v_x_2288_, 0);
v___x_2294_ = ((size_t)31ULL);
v___x_2295_ = lean_usize_land(v_x_2289_, v___x_2294_);
v_j_2296_ = lean_usize_to_nat(v___x_2295_);
v___x_2297_ = lean_array_get_size(v_es_2293_);
v___x_2298_ = lean_nat_dec_lt(v_j_2296_, v___x_2297_);
if (v___x_2298_ == 0)
{
lean_dec(v_j_2296_);
lean_dec(v_x_2292_);
lean_dec(v_x_2291_);
return v_x_2288_;
}
else
{
lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2337_; 
lean_inc_ref(v_es_2293_);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_x_2288_);
if (v_isSharedCheck_2337_ == 0)
{
lean_object* v_unused_2338_; 
v_unused_2338_ = lean_ctor_get(v_x_2288_, 0);
lean_dec(v_unused_2338_);
v___x_2300_ = v_x_2288_;
v_isShared_2301_ = v_isSharedCheck_2337_;
goto v_resetjp_2299_;
}
else
{
lean_dec(v_x_2288_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2337_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v_v_2302_; lean_object* v___x_2303_; lean_object* v_xs_x27_2304_; lean_object* v___y_2306_; 
v_v_2302_ = lean_array_fget(v_es_2293_, v_j_2296_);
v___x_2303_ = lean_box(0);
v_xs_x27_2304_ = lean_array_fset(v_es_2293_, v_j_2296_, v___x_2303_);
switch(lean_obj_tag(v_v_2302_))
{
case 0:
{
lean_object* v_key_2311_; lean_object* v_val_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2322_; 
v_key_2311_ = lean_ctor_get(v_v_2302_, 0);
v_val_2312_ = lean_ctor_get(v_v_2302_, 1);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_v_2302_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2314_ = v_v_2302_;
v_isShared_2315_ = v_isSharedCheck_2322_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_val_2312_);
lean_inc(v_key_2311_);
lean_dec(v_v_2302_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2322_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
uint8_t v___x_2316_; 
v___x_2316_ = l_Lean_instBEqMVarId_beq(v_x_2291_, v_key_2311_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
lean_del_object(v___x_2314_);
v___x_2317_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2311_, v_val_2312_, v_x_2291_, v_x_2292_);
v___x_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
v___y_2306_ = v___x_2318_;
goto v___jp_2305_;
}
else
{
lean_object* v___x_2320_; 
lean_dec(v_val_2312_);
lean_dec(v_key_2311_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 1, v_x_2292_);
lean_ctor_set(v___x_2314_, 0, v_x_2291_);
v___x_2320_ = v___x_2314_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_x_2291_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_x_2292_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
v___y_2306_ = v___x_2320_;
goto v___jp_2305_;
}
}
}
}
case 1:
{
lean_object* v_node_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2335_; 
v_node_2323_ = lean_ctor_get(v_v_2302_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_v_2302_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2325_ = v_v_2302_;
v_isShared_2326_ = v_isSharedCheck_2335_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_node_2323_);
lean_dec(v_v_2302_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2335_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
size_t v___x_2327_; size_t v___x_2328_; size_t v___x_2329_; size_t v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2327_ = ((size_t)5ULL);
v___x_2328_ = lean_usize_shift_right(v_x_2289_, v___x_2327_);
v___x_2329_ = ((size_t)1ULL);
v___x_2330_ = lean_usize_add(v_x_2290_, v___x_2329_);
v___x_2331_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3___redArg(v_node_2323_, v___x_2328_, v___x_2330_, v_x_2291_, v_x_2292_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2331_);
v___x_2333_ = v___x_2325_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
v___y_2306_ = v___x_2333_;
goto v___jp_2305_;
}
}
}
default: 
{
lean_object* v___x_2336_; 
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v_x_2291_);
lean_ctor_set(v___x_2336_, 1, v_x_2292_);
v___y_2306_ = v___x_2336_;
goto v___jp_2305_;
}
}
v___jp_2305_:
{
lean_object* v___x_2307_; lean_object* v___x_2309_; 
v___x_2307_ = lean_array_fset(v_xs_x27_2304_, v_j_2296_, v___y_2306_);
lean_dec(v_j_2296_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v___x_2307_);
v___x_2309_ = v___x_2300_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2307_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
else
{
lean_object* v_ks_2339_; lean_object* v_vs_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2358_; 
v_ks_2339_ = lean_ctor_get(v_x_2288_, 0);
v_vs_2340_ = lean_ctor_get(v_x_2288_, 1);
v_isSharedCheck_2358_ = !lean_is_exclusive(v_x_2288_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2342_ = v_x_2288_;
v_isShared_2343_ = v_isSharedCheck_2358_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_vs_2340_);
lean_inc(v_ks_2339_);
lean_dec(v_x_2288_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2358_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_ks_2339_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v_vs_2340_);
v___x_2345_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v_newNode_2346_; size_t v___x_2347_; uint8_t v___x_2348_; 
v_newNode_2346_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__4___redArg(v___x_2345_, v_x_2291_, v_x_2292_);
v___x_2347_ = ((size_t)7ULL);
v___x_2348_ = lean_usize_dec_le(v___x_2347_, v_x_2290_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; 
v___x_2349_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2346_);
v___x_2350_ = lean_unsigned_to_nat(4u);
v___x_2351_ = lean_nat_dec_lt(v___x_2349_, v___x_2350_);
lean_dec(v___x_2349_);
if (v___x_2351_ == 0)
{
lean_object* v_ks_2352_; lean_object* v_vs_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v_ks_2352_ = lean_ctor_get(v_newNode_2346_, 0);
lean_inc_ref(v_ks_2352_);
v_vs_2353_ = lean_ctor_get(v_newNode_2346_, 1);
lean_inc_ref(v_vs_2353_);
lean_dec_ref(v_newNode_2346_);
v___x_2354_ = lean_unsigned_to_nat(0u);
v___x_2355_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_2356_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__5___redArg(v_x_2290_, v_ks_2352_, v_vs_2353_, v___x_2354_, v___x_2355_);
lean_dec_ref(v_vs_2353_);
lean_dec_ref(v_ks_2352_);
return v___x_2356_;
}
else
{
return v_newNode_2346_;
}
}
else
{
return v_newNode_2346_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__5___redArg(size_t v_depth_2359_, lean_object* v_keys_2360_, lean_object* v_vals_2361_, lean_object* v_i_2362_, lean_object* v_entries_2363_){
_start:
{
lean_object* v___x_2364_; uint8_t v___x_2365_; 
v___x_2364_ = lean_array_get_size(v_keys_2360_);
v___x_2365_ = lean_nat_dec_lt(v_i_2362_, v___x_2364_);
if (v___x_2365_ == 0)
{
lean_dec(v_i_2362_);
return v_entries_2363_;
}
else
{
lean_object* v_k_2366_; lean_object* v_v_2367_; uint64_t v___x_2368_; size_t v_h_2369_; size_t v___x_2370_; lean_object* v___x_2371_; size_t v___x_2372_; size_t v___x_2373_; size_t v___x_2374_; size_t v_h_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v_k_2366_ = lean_array_fget_borrowed(v_keys_2360_, v_i_2362_);
v_v_2367_ = lean_array_fget_borrowed(v_vals_2361_, v_i_2362_);
v___x_2368_ = l_Lean_instHashableMVarId_hash(v_k_2366_);
v_h_2369_ = lean_uint64_to_usize(v___x_2368_);
v___x_2370_ = ((size_t)5ULL);
v___x_2371_ = lean_unsigned_to_nat(1u);
v___x_2372_ = ((size_t)1ULL);
v___x_2373_ = lean_usize_sub(v_depth_2359_, v___x_2372_);
v___x_2374_ = lean_usize_mul(v___x_2370_, v___x_2373_);
v_h_2375_ = lean_usize_shift_right(v_h_2369_, v___x_2374_);
v___x_2376_ = lean_nat_add(v_i_2362_, v___x_2371_);
lean_dec(v_i_2362_);
lean_inc(v_v_2367_);
lean_inc(v_k_2366_);
v___x_2377_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3___redArg(v_entries_2363_, v_h_2375_, v_depth_2359_, v_k_2366_, v_v_2367_);
v_i_2362_ = v___x_2376_;
v_entries_2363_ = v___x_2377_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_depth_2379_, lean_object* v_keys_2380_, lean_object* v_vals_2381_, lean_object* v_i_2382_, lean_object* v_entries_2383_){
_start:
{
size_t v_depth_boxed_2384_; lean_object* v_res_2385_; 
v_depth_boxed_2384_ = lean_unbox_usize(v_depth_2379_);
lean_dec(v_depth_2379_);
v_res_2385_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_boxed_2384_, v_keys_2380_, v_vals_2381_, v_i_2382_, v_entries_2383_);
lean_dec_ref(v_vals_2381_);
lean_dec_ref(v_keys_2380_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_2386_, lean_object* v_x_2387_, lean_object* v_x_2388_, lean_object* v_x_2389_, lean_object* v_x_2390_){
_start:
{
size_t v_x_2776__boxed_2391_; size_t v_x_2777__boxed_2392_; lean_object* v_res_2393_; 
v_x_2776__boxed_2391_ = lean_unbox_usize(v_x_2387_);
lean_dec(v_x_2387_);
v_x_2777__boxed_2392_ = lean_unbox_usize(v_x_2388_);
lean_dec(v_x_2388_);
v_res_2393_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3___redArg(v_x_2386_, v_x_2776__boxed_2391_, v_x_2777__boxed_2392_, v_x_2389_, v_x_2390_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1___redArg(lean_object* v_x_2394_, lean_object* v_x_2395_, lean_object* v_x_2396_){
_start:
{
uint64_t v___x_2397_; size_t v___x_2398_; size_t v___x_2399_; lean_object* v___x_2400_; 
v___x_2397_ = l_Lean_instHashableMVarId_hash(v_x_2395_);
v___x_2398_ = lean_uint64_to_usize(v___x_2397_);
v___x_2399_ = ((size_t)1ULL);
v___x_2400_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3___redArg(v_x_2394_, v___x_2398_, v___x_2399_, v_x_2395_, v_x_2396_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1___redArg(lean_object* v_mvarId_2401_, lean_object* v_val_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___x_2405_; lean_object* v_mctx_2406_; lean_object* v_cache_2407_; lean_object* v_zetaDeltaFVarIds_2408_; lean_object* v_postponed_2409_; lean_object* v_diag_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2439_; 
v___x_2405_ = lean_st_ref_take(v___y_2403_);
v_mctx_2406_ = lean_ctor_get(v___x_2405_, 0);
v_cache_2407_ = lean_ctor_get(v___x_2405_, 1);
v_zetaDeltaFVarIds_2408_ = lean_ctor_get(v___x_2405_, 2);
v_postponed_2409_ = lean_ctor_get(v___x_2405_, 3);
v_diag_2410_ = lean_ctor_get(v___x_2405_, 4);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2412_ = v___x_2405_;
v_isShared_2413_ = v_isSharedCheck_2439_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_diag_2410_);
lean_inc(v_postponed_2409_);
lean_inc(v_zetaDeltaFVarIds_2408_);
lean_inc(v_cache_2407_);
lean_inc(v_mctx_2406_);
lean_dec(v___x_2405_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2439_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v_depth_2414_; lean_object* v_levelAssignDepth_2415_; lean_object* v_lmvarCounter_2416_; lean_object* v_mvarCounter_2417_; lean_object* v_lDecls_2418_; lean_object* v_decls_2419_; lean_object* v_userNames_2420_; lean_object* v_lAssignment_2421_; lean_object* v_eAssignment_2422_; lean_object* v_dAssignment_2423_; lean_object* v_instanceTypedMVars_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2438_; 
v_depth_2414_ = lean_ctor_get(v_mctx_2406_, 0);
v_levelAssignDepth_2415_ = lean_ctor_get(v_mctx_2406_, 1);
v_lmvarCounter_2416_ = lean_ctor_get(v_mctx_2406_, 2);
v_mvarCounter_2417_ = lean_ctor_get(v_mctx_2406_, 3);
v_lDecls_2418_ = lean_ctor_get(v_mctx_2406_, 4);
v_decls_2419_ = lean_ctor_get(v_mctx_2406_, 5);
v_userNames_2420_ = lean_ctor_get(v_mctx_2406_, 6);
v_lAssignment_2421_ = lean_ctor_get(v_mctx_2406_, 7);
v_eAssignment_2422_ = lean_ctor_get(v_mctx_2406_, 8);
v_dAssignment_2423_ = lean_ctor_get(v_mctx_2406_, 9);
v_instanceTypedMVars_2424_ = lean_ctor_get(v_mctx_2406_, 10);
v_isSharedCheck_2438_ = !lean_is_exclusive(v_mctx_2406_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2426_ = v_mctx_2406_;
v_isShared_2427_ = v_isSharedCheck_2438_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_instanceTypedMVars_2424_);
lean_inc(v_dAssignment_2423_);
lean_inc(v_eAssignment_2422_);
lean_inc(v_lAssignment_2421_);
lean_inc(v_userNames_2420_);
lean_inc(v_decls_2419_);
lean_inc(v_lDecls_2418_);
lean_inc(v_mvarCounter_2417_);
lean_inc(v_lmvarCounter_2416_);
lean_inc(v_levelAssignDepth_2415_);
lean_inc(v_depth_2414_);
lean_dec(v_mctx_2406_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2438_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2431_; 
v___x_2428_ = lean_box(0);
v___x_2429_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1___redArg(v_eAssignment_2422_, v_mvarId_2401_, v_val_2402_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 8, v___x_2429_);
v___x_2431_ = v___x_2426_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_depth_2414_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_levelAssignDepth_2415_);
lean_ctor_set(v_reuseFailAlloc_2437_, 2, v_lmvarCounter_2416_);
lean_ctor_set(v_reuseFailAlloc_2437_, 3, v_mvarCounter_2417_);
lean_ctor_set(v_reuseFailAlloc_2437_, 4, v_lDecls_2418_);
lean_ctor_set(v_reuseFailAlloc_2437_, 5, v_decls_2419_);
lean_ctor_set(v_reuseFailAlloc_2437_, 6, v_userNames_2420_);
lean_ctor_set(v_reuseFailAlloc_2437_, 7, v_lAssignment_2421_);
lean_ctor_set(v_reuseFailAlloc_2437_, 8, v___x_2429_);
lean_ctor_set(v_reuseFailAlloc_2437_, 9, v_dAssignment_2423_);
lean_ctor_set(v_reuseFailAlloc_2437_, 10, v_instanceTypedMVars_2424_);
v___x_2431_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
lean_object* v___x_2433_; 
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2431_);
v___x_2433_ = v___x_2412_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v_cache_2407_);
lean_ctor_set(v_reuseFailAlloc_2436_, 2, v_zetaDeltaFVarIds_2408_);
lean_ctor_set(v_reuseFailAlloc_2436_, 3, v_postponed_2409_);
lean_ctor_set(v_reuseFailAlloc_2436_, 4, v_diag_2410_);
v___x_2433_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = lean_st_ref_put(v___y_2403_, v___x_2433_);
v___x_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2428_);
return v___x_2435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1___redArg___boxed(lean_object* v_mvarId_2440_, lean_object* v_val_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1___redArg(v_mvarId_2440_, v_val_2441_, v___y_2442_);
lean_dec(v___y_2442_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__0(lean_object* v_as_2448_, size_t v_sz_2449_, size_t v_i_2450_, lean_object* v_b_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v_a_2458_; uint8_t v___x_2462_; 
v___x_2462_ = lean_usize_dec_lt(v_i_2450_, v_sz_2449_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; 
v___x_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2463_, 0, v_b_2451_);
return v___x_2463_;
}
else
{
lean_object* v_a_2464_; lean_object* v_test_2465_; lean_object* v_v_2466_; lean_object* v_h_2467_; lean_object* v_fst_2468_; lean_object* v_fst_2469_; lean_object* v_snd_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2511_; 
v_a_2464_ = lean_array_uget_borrowed(v_as_2448_, v_i_2450_);
v_test_2465_ = lean_ctor_get(v_a_2464_, 0);
v_v_2466_ = lean_ctor_get(v_a_2464_, 1);
v_h_2467_ = lean_ctor_get(v_a_2464_, 2);
v_fst_2468_ = lean_ctor_get(v_test_2465_, 0);
v_fst_2469_ = lean_ctor_get(v_b_2451_, 0);
v_snd_2470_ = lean_ctor_get(v_b_2451_, 1);
v_isSharedCheck_2511_ = !lean_is_exclusive(v_b_2451_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2472_ = v_b_2451_;
v_isShared_2473_ = v_isSharedCheck_2511_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_snd_2470_);
lean_inc(v_fst_2469_);
lean_dec(v_b_2451_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2511_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
uint8_t v___x_2474_; 
v___x_2474_ = l_Lean_Expr_containsFVar(v_snd_2470_, v_fst_2468_);
if (v___x_2474_ == 0)
{
lean_object* v___x_2476_; 
if (v_isShared_2473_ == 0)
{
v___x_2476_ = v___x_2472_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_fst_2469_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_snd_2470_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
v_a_2458_ = v___x_2476_;
goto v___jp_2457_;
}
}
else
{
lean_object* v___x_2478_; 
lean_inc(v_fst_2468_);
v___x_2478_ = l_Lean_FVarId_getType___redArg(v_fst_2468_, v___y_2452_, v___y_2454_, v___y_2455_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2479_);
lean_dec_ref_known(v___x_2478_, 1);
v___x_2480_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__0___closed__1));
v___x_2481_ = 0;
lean_inc(v_fst_2468_);
v___x_2482_ = l_Lean_mkFVar(v_fst_2468_);
v___x_2483_ = lean_unsigned_to_nat(1u);
v___x_2484_ = lean_mk_empty_array_with_capacity(v___x_2483_);
lean_inc_ref(v___x_2482_);
v___x_2485_ = lean_array_push(v___x_2484_, v___x_2482_);
v___x_2486_ = lean_expr_abstract(v_snd_2470_, v___x_2485_);
lean_dec_ref(v___x_2485_);
v___x_2487_ = l_Lean_mkLambda(v___x_2480_, v___x_2481_, v_a_2479_, v___x_2486_);
lean_inc(v_h_2467_);
v___x_2488_ = l_Lean_mkFVar(v_h_2467_);
v___x_2489_ = l_Lean_Meta_mkEqNDRec(v___x_2487_, v_fst_2469_, v___x_2488_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2490_);
lean_dec_ref_known(v___x_2489_, 1);
v___x_2491_ = l_Lean_Expr_replaceFVar(v_snd_2470_, v___x_2482_, v_v_2466_);
lean_dec(v_snd_2470_);
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 1, v___x_2491_);
lean_ctor_set(v___x_2472_, 0, v_a_2490_);
v___x_2493_ = v___x_2472_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2490_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v___x_2491_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
v_a_2458_ = v___x_2493_;
goto v___jp_2457_;
}
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec_ref(v___x_2482_);
lean_del_object(v___x_2472_);
lean_dec(v_snd_2470_);
v_a_2495_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2489_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2489_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
lean_del_object(v___x_2472_);
lean_dec(v_snd_2470_);
lean_dec(v_fst_2469_);
v_a_2503_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2478_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2478_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
}
}
v___jp_2457_:
{
size_t v___x_2459_; size_t v___x_2460_; 
v___x_2459_ = ((size_t)1ULL);
v___x_2460_ = lean_usize_add(v_i_2450_, v___x_2459_);
v_i_2450_ = v___x_2460_;
v_b_2451_ = v_a_2458_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__0___boxed(lean_object* v_as_2512_, lean_object* v_sz_2513_, lean_object* v_i_2514_, lean_object* v_b_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
size_t v_sz_boxed_2521_; size_t v_i_boxed_2522_; lean_object* v_res_2523_; 
v_sz_boxed_2521_ = lean_unbox_usize(v_sz_2513_);
lean_dec(v_sz_2513_);
v_i_boxed_2522_ = lean_unbox_usize(v_i_2514_);
lean_dec(v_i_2514_);
v_res_2523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__0(v_as_2512_, v_sz_boxed_2521_, v_i_boxed_2522_, v_b_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec_ref(v_as_2512_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing___lam__0(lean_object* v_hyp_2524_, lean_object* v_proof_2525_, lean_object* v_kept_2526_, lean_object* v_mvarId_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = l_Lean_FVarId_getType___redArg(v_hyp_2524_, v___y_2528_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; lean_object* v___x_2535_; lean_object* v_a_2536_; lean_object* v___x_2537_; size_t v_sz_2538_; size_t v___x_2539_; lean_object* v___x_2540_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2534_);
lean_dec_ref_known(v___x_2533_, 1);
v___x_2535_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex_spec__0___redArg(v_a_2534_, v___y_2529_);
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2536_);
lean_dec_ref(v___x_2535_);
v___x_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2537_, 0, v_proof_2525_);
lean_ctor_set(v___x_2537_, 1, v_a_2536_);
v_sz_2538_ = lean_array_size(v_kept_2526_);
v___x_2539_ = ((size_t)0ULL);
v___x_2540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__0(v_kept_2526_, v_sz_2538_, v___x_2539_, v___x_2537_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v_a_2541_; lean_object* v_fst_2542_; lean_object* v_snd_2543_; lean_object* v___x_2544_; 
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_a_2541_);
lean_dec_ref_known(v___x_2540_, 1);
v_fst_2542_ = lean_ctor_get(v_a_2541_, 0);
lean_inc(v_fst_2542_);
v_snd_2543_ = lean_ctor_get(v_a_2541_, 1);
lean_inc(v_snd_2543_);
lean_dec(v_a_2541_);
v___x_2544_ = l_Lean_Meta_mkGenDiseqFalseProof_x3f(v_fst_2542_, v_snd_2543_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2586_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2547_ = v___x_2544_;
v_isShared_2548_ = v_isSharedCheck_2586_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2544_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2586_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
if (lean_obj_tag(v_a_2545_) == 1)
{
lean_object* v_val_2549_; lean_object* v___x_2550_; 
lean_del_object(v___x_2547_);
v_val_2549_ = lean_ctor_get(v_a_2545_, 0);
lean_inc(v_val_2549_);
lean_dec_ref_known(v_a_2545_, 1);
lean_inc(v_mvarId_2527_);
v___x_2550_ = l_Lean_MVarId_getType(v_mvarId_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; lean_object* v___x_2552_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
lean_dec_ref_known(v___x_2550_, 1);
v___x_2552_ = l_Lean_Meta_mkFalseElim(v_a_2551_, v_val_2549_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2563_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2552_, 1);
v___x_2554_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1___redArg(v_mvarId_2527_, v_a_2553_, v___y_2529_);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2563_ == 0)
{
lean_object* v_unused_2564_; 
v_unused_2564_ = lean_ctor_get(v___x_2554_, 0);
lean_dec(v_unused_2564_);
v___x_2556_ = v___x_2554_;
v_isShared_2557_ = v_isSharedCheck_2563_;
goto v_resetjp_2555_;
}
else
{
lean_dec(v___x_2554_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2563_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
uint8_t v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2561_; 
v___x_2558_ = 1;
v___x_2559_ = lean_box(v___x_2558_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v___x_2559_);
v___x_2561_ = v___x_2556_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2559_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec(v_mvarId_2527_);
v_a_2565_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2552_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2552_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
lean_dec(v_val_2549_);
lean_dec(v_mvarId_2527_);
v_a_2573_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2550_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2550_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
else
{
uint8_t v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2584_; 
lean_dec(v_a_2545_);
lean_dec(v_mvarId_2527_);
v___x_2581_ = 0;
v___x_2582_ = lean_box(v___x_2581_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v___x_2582_);
v___x_2584_ = v___x_2547_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
else
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2594_; 
lean_dec(v_mvarId_2527_);
v_a_2587_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2589_ = v___x_2544_;
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2544_);
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
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec(v_mvarId_2527_);
v_a_2595_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2540_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2540_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_dec(v_mvarId_2527_);
lean_dec_ref(v_proof_2525_);
v_a_2603_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2533_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2533_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing___lam__0___boxed(lean_object* v_hyp_2611_, lean_object* v_proof_2612_, lean_object* v_kept_2613_, lean_object* v_mvarId_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing___lam__0(v_hyp_2611_, v_proof_2612_, v_kept_2613_, v_mvarId_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec_ref(v_kept_2613_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing(lean_object* v_mvarId_2621_, lean_object* v_kept_2622_, lean_object* v_hyp_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_){
_start:
{
lean_object* v_proof_2629_; lean_object* v___f_2630_; lean_object* v___x_2631_; 
lean_inc(v_hyp_2623_);
v_proof_2629_ = l_Lean_mkFVar(v_hyp_2623_);
lean_inc(v_mvarId_2621_);
v___f_2630_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2630_, 0, v_hyp_2623_);
lean_closure_set(v___f_2630_, 1, v_proof_2629_);
lean_closure_set(v___f_2630_, 2, v_kept_2622_);
lean_closure_set(v___f_2630_, 3, v_mvarId_2621_);
v___x_2631_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__2___redArg(v_mvarId_2621_, v___f_2630_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing___boxed(lean_object* v_mvarId_2632_, lean_object* v_kept_2633_, lean_object* v_hyp_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing(v_mvarId_2632_, v_kept_2633_, v_hyp_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_);
lean_dec(v_a_2638_);
lean_dec_ref(v_a_2637_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1(lean_object* v_mvarId_2641_, lean_object* v_val_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1___redArg(v_mvarId_2641_, v_val_2642_, v___y_2644_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1___boxed(lean_object* v_mvarId_2649_, lean_object* v_val_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1(v_mvarId_2649_, v_val_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1(lean_object* v_00_u03b2_2657_, lean_object* v_x_2658_, lean_object* v_x_2659_, lean_object* v_x_2660_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1___redArg(v_x_2658_, v_x_2659_, v_x_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2662_, lean_object* v_x_2663_, size_t v_x_2664_, size_t v_x_2665_, lean_object* v_x_2666_, lean_object* v_x_2667_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3___redArg(v_x_2663_, v_x_2664_, v_x_2665_, v_x_2666_, v_x_2667_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2669_, lean_object* v_x_2670_, lean_object* v_x_2671_, lean_object* v_x_2672_, lean_object* v_x_2673_, lean_object* v_x_2674_){
_start:
{
size_t v_x_3314__boxed_2675_; size_t v_x_3315__boxed_2676_; lean_object* v_res_2677_; 
v_x_3314__boxed_2675_ = lean_unbox_usize(v_x_2671_);
lean_dec(v_x_2671_);
v_x_3315__boxed_2676_ = lean_unbox_usize(v_x_2672_);
lean_dec(v_x_2672_);
v_res_2677_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3(v_00_u03b2_2669_, v_x_2670_, v_x_3314__boxed_2675_, v_x_3315__boxed_2676_, v_x_2673_, v_x_2674_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2678_, lean_object* v_n_2679_, lean_object* v_k_2680_, lean_object* v_v_2681_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__4___redArg(v_n_2679_, v_k_2680_, v_v_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_2683_, size_t v_depth_2684_, lean_object* v_keys_2685_, lean_object* v_vals_2686_, lean_object* v_heq_2687_, lean_object* v_i_2688_, lean_object* v_entries_2689_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_2684_, v_keys_2685_, v_vals_2686_, v_i_2688_, v_entries_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_2691_, lean_object* v_depth_2692_, lean_object* v_keys_2693_, lean_object* v_vals_2694_, lean_object* v_heq_2695_, lean_object* v_i_2696_, lean_object* v_entries_2697_){
_start:
{
size_t v_depth_boxed_2698_; lean_object* v_res_2699_; 
v_depth_boxed_2698_ = lean_unbox_usize(v_depth_2692_);
lean_dec(v_depth_2692_);
v_res_2699_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_2691_, v_depth_boxed_2698_, v_keys_2693_, v_vals_2694_, v_heq_2695_, v_i_2696_, v_entries_2697_);
lean_dec_ref(v_vals_2694_);
lean_dec_ref(v_keys_2693_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_2700_, lean_object* v_x_2701_, lean_object* v_x_2702_, lean_object* v_x_2703_, lean_object* v_x_2704_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_x_2701_, v_x_2702_, v_x_2703_, v_x_2704_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__0(lean_object* v___x_2706_, lean_object* v___x_2707_, lean_object* v_lhs_2708_, lean_object* v_rhs_2709_, lean_object* v_type_2710_){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = l_Lean_mkConst(v___x_2706_, v___x_2707_);
v___x_2712_ = l_Lean_mkApp3(v___x_2711_, v_type_2710_, v_lhs_2708_, v_rhs_2709_);
return v___x_2712_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = lean_unsigned_to_nat(0u);
v___x_2718_ = l_Lean_mkBVar(v___x_2717_);
return v___x_2718_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2719_ = lean_obj_once(&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__2, &l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__2_once, _init_l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__2);
v___x_2720_ = lean_unsigned_to_nat(1u);
v___x_2721_ = lean_mk_empty_array_with_capacity(v___x_2720_);
v___x_2722_ = lean_array_push(v___x_2721_, v___x_2719_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1(lean_object* v_mvarId_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v___x_2744_; 
lean_inc(v_mvarId_2729_);
v___x_2744_ = l_Lean_MVarId_getType(v_mvarId_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2994_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2747_ = v___x_2744_;
v_isShared_2748_ = v_isSharedCheck_2994_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2744_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2994_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; uint8_t v___x_2756_; 
v___x_2754_ = ((lean_object*)(l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__3));
v___x_2755_ = lean_unsigned_to_nat(3u);
v___x_2756_ = l_Lean_Expr_isAppOfArity(v_a_2745_, v___x_2754_, v___x_2755_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
lean_del_object(v___x_2747_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
v___x_2757_ = lean_box(0);
v___x_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
return v___x_2758_;
}
else
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; uint8_t v___x_2762_; 
v___x_2759_ = l_Lean_Expr_appFn_x21(v_a_2745_);
v___x_2760_ = l_Lean_Expr_appArg_x21(v___x_2759_);
lean_dec_ref(v___x_2759_);
v___x_2761_ = l_Lean_Expr_cleanupAnnotations(v___x_2760_);
lean_dec_ref(v___x_2760_);
v___x_2762_ = l_Lean_Expr_isApp(v___x_2761_);
if (v___x_2762_ == 0)
{
lean_dec_ref(v___x_2761_);
lean_del_object(v___x_2747_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
goto v___jp_2741_;
}
else
{
lean_object* v___x_2763_; uint8_t v___x_2764_; 
v___x_2763_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2761_);
v___x_2764_ = l_Lean_Expr_isApp(v___x_2763_);
if (v___x_2764_ == 0)
{
lean_dec_ref(v___x_2763_);
lean_dec_ref(v___x_2761_);
lean_del_object(v___x_2747_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
goto v___jp_2741_;
}
else
{
lean_object* v___x_2765_; uint8_t v___x_2766_; 
v___x_2765_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2763_);
v___x_2766_ = l_Lean_Expr_isApp(v___x_2765_);
if (v___x_2766_ == 0)
{
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2763_);
lean_dec_ref(v___x_2761_);
lean_del_object(v___x_2747_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
goto v___jp_2741_;
}
else
{
lean_object* v___x_2767_; uint8_t v___x_2768_; 
v___x_2767_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2765_);
v___x_2768_ = l_Lean_Expr_isApp(v___x_2767_);
if (v___x_2768_ == 0)
{
lean_dec_ref(v___x_2767_);
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2763_);
lean_dec_ref(v___x_2761_);
lean_del_object(v___x_2747_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
goto v___jp_2741_;
}
else
{
lean_object* v___x_2769_; uint8_t v___x_2770_; 
v___x_2769_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2767_);
v___x_2770_ = l_Lean_Expr_isApp(v___x_2769_);
if (v___x_2770_ == 0)
{
lean_dec_ref(v___x_2769_);
lean_dec_ref(v___x_2767_);
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2763_);
lean_dec_ref(v___x_2761_);
lean_del_object(v___x_2747_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
goto v___jp_2741_;
}
else
{
lean_object* v___x_2771_; lean_object* v___x_2772_; uint8_t v___x_2773_; 
v___x_2771_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2769_);
v___x_2772_ = ((lean_object*)(l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__1));
v___x_2773_ = l_Lean_Expr_isConstOf(v___x_2771_, v___x_2772_);
if (v___x_2773_ == 0)
{
lean_dec_ref(v___x_2771_);
lean_dec_ref(v___x_2769_);
lean_dec_ref(v___x_2767_);
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2763_);
lean_dec_ref(v___x_2761_);
lean_del_object(v___x_2747_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
goto v___jp_2741_;
}
else
{
lean_object* v_arg_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; 
v_arg_2774_ = lean_ctor_get(v___x_2767_, 1);
lean_inc_ref(v_arg_2774_);
lean_dec_ref(v___x_2767_);
v___x_2775_ = l_Lean_Expr_cleanupAnnotations(v_arg_2774_);
v___x_2776_ = l_Lean_Expr_isApp(v___x_2775_);
if (v___x_2776_ == 0)
{
lean_dec_ref(v___x_2775_);
lean_dec_ref(v_arg_2774_);
lean_dec_ref(v___x_2771_);
lean_dec_ref(v___x_2769_);
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2763_);
lean_dec_ref(v___x_2761_);
lean_del_object(v___x_2747_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
goto v___jp_2738_;
}
else
{
lean_object* v___x_2777_; uint8_t v___x_2778_; 
v___x_2777_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2775_);
v___x_2778_ = l_Lean_Expr_isApp(v___x_2777_);
if (v___x_2778_ == 0)
{
lean_dec_ref(v___x_2777_);
lean_dec_ref(v___x_2775_);
lean_dec_ref(v_arg_2774_);
lean_dec_ref(v___x_2771_);
lean_dec_ref(v___x_2769_);
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2763_);
lean_dec_ref(v___x_2761_);
lean_del_object(v___x_2747_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
goto v___jp_2738_;
}
else
{
lean_object* v___x_2779_; uint8_t v___x_2780_; 
v___x_2779_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2777_);
v___x_2780_ = l_Lean_Expr_isApp(v___x_2779_);
if (v___x_2780_ == 0)
{
lean_dec_ref(v___x_2779_);
lean_dec_ref(v___x_2777_);
lean_dec_ref(v___x_2775_);
lean_dec_ref(v_arg_2774_);
lean_dec_ref(v___x_2771_);
lean_dec_ref(v___x_2769_);
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2763_);
lean_dec_ref(v___x_2761_);
lean_del_object(v___x_2747_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
goto v___jp_2738_;
}
else
{
lean_object* v___x_2781_; uint8_t v___x_2782_; 
v___x_2781_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2779_);
v___x_2782_ = l_Lean_Expr_isConstOf(v___x_2781_, v___x_2754_);
if (v___x_2782_ == 0)
{
lean_dec_ref(v___x_2781_);
lean_dec_ref(v___x_2779_);
lean_dec_ref(v___x_2777_);
lean_dec_ref(v___x_2775_);
lean_dec_ref(v_arg_2774_);
lean_dec_ref(v___x_2771_);
lean_dec_ref(v___x_2769_);
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2763_);
lean_dec_ref(v___x_2761_);
lean_del_object(v___x_2747_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
goto v___jp_2738_;
}
else
{
lean_object* v_arg_2783_; 
v_arg_2783_ = lean_ctor_get(v___x_2777_, 1);
lean_inc_ref(v_arg_2783_);
lean_dec_ref(v___x_2777_);
if (lean_obj_tag(v_arg_2783_) == 1)
{
lean_object* v_fvarId_2784_; lean_object* v_arg_2785_; uint8_t v___x_2786_; 
v_fvarId_2784_ = lean_ctor_get(v_arg_2783_, 0);
lean_inc(v_fvarId_2784_);
v_arg_2785_ = lean_ctor_get(v___x_2775_, 1);
lean_inc_ref(v_arg_2785_);
lean_dec_ref(v___x_2775_);
v___x_2786_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_isValue(v_arg_2785_);
if (v___x_2786_ == 0)
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
lean_dec_ref(v_arg_2785_);
lean_dec_ref_known(v_arg_2783_, 1);
lean_dec(v_fvarId_2784_);
lean_dec_ref(v___x_2781_);
lean_dec_ref(v___x_2779_);
lean_dec_ref(v_arg_2774_);
lean_dec_ref(v___x_2771_);
lean_dec_ref(v___x_2769_);
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2763_);
lean_dec_ref(v___x_2761_);
lean_del_object(v___x_2747_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
v___x_2787_ = lean_box(0);
v___x_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2787_);
return v___x_2788_;
}
else
{
lean_object* v_arg_2789_; lean_object* v___x_2790_; uint8_t v___x_2791_; 
v_arg_2789_ = lean_ctor_get(v___x_2763_, 1);
lean_inc_ref(v_arg_2789_);
lean_dec_ref(v___x_2763_);
v___x_2790_ = l_Lean_Expr_cleanupAnnotations(v_arg_2789_);
lean_dec_ref(v_arg_2789_);
v___x_2791_ = l_Lean_Expr_isApp(v___x_2790_);
if (v___x_2791_ == 0)
{
lean_dec_ref(v___x_2790_);
lean_dec_ref(v_arg_2785_);
lean_dec_ref_known(v_arg_2783_, 1);
lean_dec(v_fvarId_2784_);
lean_dec_ref(v___x_2781_);
lean_dec_ref(v___x_2779_);
lean_dec_ref(v_arg_2774_);
lean_dec_ref(v___x_2771_);
lean_dec_ref(v___x_2769_);
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2761_);
lean_del_object(v___x_2747_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
goto v___jp_2735_;
}
else
{
lean_object* v___x_2792_; uint8_t v___x_2793_; 
v___x_2792_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2790_);
v___x_2793_ = l_Lean_Expr_isApp(v___x_2792_);
if (v___x_2793_ == 0)
{
lean_dec_ref(v___x_2792_);
lean_dec_ref(v___x_2790_);
lean_dec_ref(v_arg_2785_);
lean_dec_ref_known(v_arg_2783_, 1);
lean_dec(v_fvarId_2784_);
lean_dec_ref(v___x_2781_);
lean_dec_ref(v___x_2779_);
lean_dec_ref(v_arg_2774_);
lean_dec_ref(v___x_2771_);
lean_dec_ref(v___x_2769_);
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2761_);
lean_del_object(v___x_2747_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
goto v___jp_2735_;
}
else
{
lean_object* v___x_2794_; uint8_t v___x_2795_; 
v___x_2794_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2792_);
v___x_2795_ = l_Lean_Expr_isApp(v___x_2794_);
if (v___x_2795_ == 0)
{
lean_dec_ref(v___x_2794_);
lean_dec_ref(v___x_2792_);
lean_dec_ref(v___x_2790_);
lean_dec_ref(v_arg_2785_);
lean_dec_ref_known(v_arg_2783_, 1);
lean_dec(v_fvarId_2784_);
lean_dec_ref(v___x_2781_);
lean_dec_ref(v___x_2779_);
lean_dec_ref(v_arg_2774_);
lean_dec_ref(v___x_2771_);
lean_dec_ref(v___x_2769_);
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2761_);
lean_del_object(v___x_2747_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
goto v___jp_2735_;
}
else
{
lean_object* v___x_2796_; uint8_t v___x_2797_; 
v___x_2796_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2794_);
v___x_2797_ = l_Lean_Expr_isApp(v___x_2796_);
if (v___x_2797_ == 0)
{
lean_dec_ref(v___x_2796_);
lean_dec_ref(v___x_2794_);
lean_dec_ref(v___x_2792_);
lean_dec_ref(v___x_2790_);
lean_dec_ref(v_arg_2785_);
lean_dec_ref_known(v_arg_2783_, 1);
lean_dec(v_fvarId_2784_);
lean_dec_ref(v___x_2781_);
lean_dec_ref(v___x_2779_);
lean_dec_ref(v_arg_2774_);
lean_dec_ref(v___x_2771_);
lean_dec_ref(v___x_2769_);
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2761_);
lean_del_object(v___x_2747_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
goto v___jp_2735_;
}
else
{
lean_object* v___x_2798_; uint8_t v___x_2799_; 
v___x_2798_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2796_);
v___x_2799_ = l_Lean_Expr_isApp(v___x_2798_);
if (v___x_2799_ == 0)
{
lean_dec_ref(v___x_2798_);
lean_dec_ref(v___x_2796_);
lean_dec_ref(v___x_2794_);
lean_dec_ref(v___x_2792_);
lean_dec_ref(v___x_2790_);
lean_dec_ref(v_arg_2785_);
lean_dec(v_fvarId_2784_);
lean_dec_ref_known(v_arg_2783_, 1);
lean_dec_ref(v___x_2781_);
lean_dec_ref(v___x_2779_);
lean_dec_ref(v_arg_2774_);
lean_dec_ref(v___x_2771_);
lean_dec_ref(v___x_2769_);
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2761_);
lean_del_object(v___x_2747_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
goto v___jp_2735_;
}
else
{
lean_object* v___x_2800_; lean_object* v___x_2801_; uint8_t v___x_2802_; 
v___x_2800_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2798_);
lean_dec_ref(v___x_2798_);
v___x_2801_ = ((lean_object*)(l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__1));
v___x_2802_ = l_Lean_Expr_isConstOf(v___x_2800_, v___x_2801_);
lean_dec_ref(v___x_2800_);
if (v___x_2802_ == 0)
{
lean_dec_ref(v___x_2796_);
lean_dec_ref(v___x_2794_);
lean_dec_ref(v___x_2792_);
lean_dec_ref(v___x_2790_);
lean_dec_ref(v_arg_2785_);
lean_dec_ref_known(v_arg_2783_, 1);
lean_dec(v_fvarId_2784_);
lean_dec_ref(v___x_2781_);
lean_dec_ref(v___x_2779_);
lean_dec_ref(v_arg_2774_);
lean_dec_ref(v___x_2771_);
lean_dec_ref(v___x_2769_);
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2761_);
lean_del_object(v___x_2747_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
goto v___jp_2735_;
}
else
{
lean_object* v_arg_2803_; uint8_t v___x_2804_; 
v_arg_2803_ = lean_ctor_get(v___x_2796_, 1);
lean_inc_ref(v_arg_2803_);
lean_dec_ref(v___x_2796_);
v___x_2804_ = lean_expr_eqv(v_arg_2803_, v_arg_2785_);
lean_dec_ref(v_arg_2803_);
if (v___x_2804_ == 0)
{
lean_dec_ref(v___x_2794_);
lean_dec_ref(v___x_2792_);
lean_dec_ref(v___x_2790_);
lean_dec_ref(v_arg_2785_);
lean_dec_ref_known(v_arg_2783_, 1);
lean_dec(v_fvarId_2784_);
lean_dec_ref(v___x_2781_);
lean_dec_ref(v___x_2779_);
lean_dec_ref(v_arg_2774_);
lean_dec_ref(v___x_2771_);
lean_dec_ref(v___x_2769_);
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2761_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
goto v___jp_2749_;
}
else
{
lean_object* v_arg_2805_; uint8_t v___x_2806_; 
v_arg_2805_ = lean_ctor_get(v___x_2790_, 1);
lean_inc_ref(v_arg_2805_);
lean_dec_ref(v___x_2790_);
v___x_2806_ = lean_expr_eqv(v_arg_2805_, v_arg_2783_);
lean_dec_ref(v_arg_2805_);
if (v___x_2806_ == 0)
{
lean_dec_ref(v___x_2794_);
lean_dec_ref(v___x_2792_);
lean_dec_ref(v_arg_2785_);
lean_dec_ref_known(v_arg_2783_, 1);
lean_dec(v_fvarId_2784_);
lean_dec_ref(v___x_2781_);
lean_dec_ref(v___x_2779_);
lean_dec_ref(v_arg_2774_);
lean_dec_ref(v___x_2771_);
lean_dec_ref(v___x_2769_);
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2761_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
goto v___jp_2749_;
}
else
{
lean_object* v_arg_2807_; lean_object* v_arg_2808_; lean_object* v_arg_2809_; lean_object* v_arg_2810_; lean_object* v_arg_2811_; lean_object* v_arg_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; uint8_t v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
lean_del_object(v___x_2747_);
v_arg_2807_ = lean_ctor_get(v___x_2761_, 1);
lean_inc_ref(v_arg_2807_);
lean_dec_ref(v___x_2761_);
v_arg_2808_ = lean_ctor_get(v___x_2765_, 1);
lean_inc_ref(v_arg_2808_);
lean_dec_ref(v___x_2765_);
v_arg_2809_ = lean_ctor_get(v___x_2769_, 1);
lean_inc_ref(v_arg_2809_);
lean_dec_ref(v___x_2769_);
v_arg_2810_ = lean_ctor_get(v___x_2779_, 1);
lean_inc_ref_n(v_arg_2810_, 2);
lean_dec_ref(v___x_2779_);
v_arg_2811_ = lean_ctor_get(v___x_2792_, 1);
lean_inc_ref(v_arg_2811_);
lean_dec_ref(v___x_2792_);
v_arg_2812_ = lean_ctor_get(v___x_2794_, 1);
lean_inc_ref(v_arg_2812_);
lean_dec_ref(v___x_2794_);
v___x_2813_ = l_Lean_Expr_appArg_x21(v_a_2745_);
lean_dec(v_a_2745_);
v___x_2814_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__0___closed__1));
v___x_2815_ = 0;
v___x_2816_ = lean_unsigned_to_nat(1u);
v___x_2817_ = lean_mk_empty_array_with_capacity(v___x_2816_);
lean_inc_ref(v_arg_2783_);
lean_inc_ref(v___x_2817_);
v___x_2818_ = lean_array_push(v___x_2817_, v_arg_2783_);
v___x_2819_ = lean_expr_abstract(v___x_2813_, v___x_2818_);
lean_dec_ref(v___x_2818_);
v___x_2820_ = l_Lean_mkLambda(v___x_2814_, v___x_2815_, v_arg_2810_, v___x_2819_);
lean_inc_ref(v___x_2820_);
v___x_2821_ = l_Lean_Meta_isTypeCorrect(v___x_2820_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2983_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2824_ = v___x_2821_;
v_isShared_2825_ = v_isSharedCheck_2983_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2821_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2983_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
uint8_t v___x_2826_; 
v___x_2826_ = lean_unbox(v_a_2822_);
lean_dec(v_a_2822_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; lean_object* v___x_2829_; 
lean_dec_ref(v___x_2820_);
lean_dec_ref(v___x_2817_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_arg_2812_);
lean_dec_ref(v_arg_2811_);
lean_dec_ref(v_arg_2810_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2808_);
lean_dec_ref(v_arg_2807_);
lean_dec_ref(v_arg_2785_);
lean_dec(v_fvarId_2784_);
lean_dec_ref_known(v_arg_2783_, 1);
lean_dec_ref(v___x_2781_);
lean_dec_ref(v_arg_2774_);
lean_dec_ref(v___x_2771_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
v___x_2827_ = lean_box(0);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 0, v___x_2827_);
v___x_2829_ = v___x_2824_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2827_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
else
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
lean_del_object(v___x_2824_);
v___x_2831_ = lean_obj_once(&l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__3, &l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__3);
lean_inc_ref(v_arg_2812_);
v___x_2832_ = l_Lean_Expr_beta(v_arg_2812_, v___x_2831_);
lean_inc_ref(v_arg_2810_);
v___x_2833_ = l_Lean_mkForall(v___x_2814_, v___x_2815_, v_arg_2810_, v___x_2832_);
lean_inc(v___y_2733_);
lean_inc_ref(v___y_2732_);
lean_inc(v___y_2731_);
lean_inc_ref(v___y_2730_);
lean_inc_ref(v___x_2820_);
v___x_2834_ = lean_infer_type(v___x_2820_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2836_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref_known(v___x_2834_, 1);
v___x_2836_ = l_Lean_Meta_isExprDefEq(v_a_2835_, v___x_2833_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2966_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2839_ = v___x_2836_;
v_isShared_2840_ = v_isSharedCheck_2966_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2836_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2966_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
uint8_t v___x_2841_; 
v___x_2841_ = lean_unbox(v_a_2837_);
lean_dec(v_a_2837_);
if (v___x_2841_ == 0)
{
lean_object* v___x_2842_; lean_object* v___x_2844_; 
lean_dec_ref(v___x_2820_);
lean_dec_ref(v___x_2817_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_arg_2812_);
lean_dec_ref(v_arg_2811_);
lean_dec_ref(v_arg_2810_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2808_);
lean_dec_ref(v_arg_2807_);
lean_dec_ref(v_arg_2785_);
lean_dec(v_fvarId_2784_);
lean_dec_ref_known(v_arg_2783_, 1);
lean_dec_ref(v___x_2781_);
lean_dec_ref(v_arg_2774_);
lean_dec_ref(v___x_2771_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
v___x_2842_ = lean_box(0);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v___x_2842_);
v___x_2844_ = v___x_2839_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2842_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
else
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
lean_del_object(v___x_2839_);
v___x_2846_ = l_Lean_Expr_constLevels_x21(v___x_2771_);
lean_dec_ref(v___x_2771_);
lean_inc(v_mvarId_2729_);
v___x_2847_ = l_Lean_MVarId_getTag(v_mvarId_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_a_2848_);
lean_dec_ref_known(v___x_2847_, 1);
lean_inc_ref(v_arg_2783_);
v___x_2849_ = l_Lean_Expr_replaceFVar(v___x_2813_, v_arg_2783_, v_arg_2785_);
lean_inc_ref(v_arg_2785_);
v___x_2850_ = lean_array_push(v___x_2817_, v_arg_2785_);
lean_inc_ref(v_arg_2812_);
v___x_2851_ = l_Lean_Expr_beta(v_arg_2812_, v___x_2850_);
lean_inc_ref(v_arg_2811_);
lean_inc(v___x_2846_);
v___x_2852_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__0(v___x_2754_, v___x_2846_, v_arg_2811_, v___x_2849_, v___x_2851_);
lean_inc_ref(v_arg_2774_);
v___x_2853_ = l_Lean_mkArrow(v_arg_2774_, v___x_2852_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2855_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2854_);
lean_dec_ref_known(v___x_2853_, 1);
lean_inc(v_a_2848_);
v___x_2855_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2854_, v_a_2848_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2855_, 1);
v___x_2857_ = ((lean_object*)(l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__5));
v___x_2858_ = l_Lean_mkNot(v_arg_2774_);
lean_inc_ref(v_arg_2807_);
v___x_2859_ = l_Lean_Expr_beta(v_arg_2807_, v___x_2831_);
lean_inc(v___x_2846_);
v___x_2860_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__0(v___x_2754_, v___x_2846_, v___x_2859_, v___x_2813_, v_arg_2809_);
v___x_2861_ = l_Lean_mkForall(v___x_2857_, v___x_2815_, v___x_2858_, v___x_2860_);
v___x_2862_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2861_, v_a_2848_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2932_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc_n(v_a_2863_, 2);
lean_dec_ref_known(v___x_2862_, 1);
v___x_2864_ = ((lean_object*)(l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___closed__7));
v___x_2865_ = l_Lean_Expr_constLevels_x21(v___x_2781_);
lean_dec_ref(v___x_2781_);
v___x_2866_ = l_List_appendTR___redArg(v___x_2865_, v___x_2846_);
v___x_2867_ = l_Lean_mkConst(v___x_2864_, v___x_2866_);
v___x_2868_ = lean_unsigned_to_nat(10u);
v___x_2869_ = lean_mk_empty_array_with_capacity(v___x_2868_);
v___x_2870_ = lean_array_push(v___x_2869_, v_arg_2810_);
lean_inc_ref(v_arg_2785_);
v___x_2871_ = lean_array_push(v___x_2870_, v_arg_2785_);
v___x_2872_ = lean_array_push(v___x_2871_, v_arg_2783_);
v___x_2873_ = lean_array_push(v___x_2872_, v_arg_2808_);
v___x_2874_ = lean_array_push(v___x_2873_, v_arg_2812_);
v___x_2875_ = lean_array_push(v___x_2874_, v_arg_2811_);
v___x_2876_ = lean_array_push(v___x_2875_, v_arg_2807_);
v___x_2877_ = lean_array_push(v___x_2876_, v___x_2820_);
lean_inc(v_a_2856_);
v___x_2878_ = lean_array_push(v___x_2877_, v_a_2856_);
v___x_2879_ = lean_array_push(v___x_2878_, v_a_2863_);
v___x_2880_ = l_Lean_mkAppN(v___x_2867_, v___x_2879_);
lean_dec_ref(v___x_2879_);
v___x_2881_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__1___redArg(v_mvarId_2729_, v___x_2880_, v___y_2731_);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2932_ == 0)
{
lean_object* v_unused_2933_; 
v_unused_2933_ = lean_ctor_get(v___x_2881_, 0);
lean_dec(v_unused_2933_);
v___x_2883_ = v___x_2881_;
v_isShared_2884_ = v_isSharedCheck_2932_;
goto v_resetjp_2882_;
}
else
{
lean_dec(v___x_2881_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2932_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2885_; uint8_t v___x_2886_; lean_object* v___x_2887_; 
v___x_2885_ = l_Lean_Expr_mvarId_x21(v_a_2856_);
lean_dec(v_a_2856_);
v___x_2886_ = 0;
v___x_2887_ = l_Lean_Meta_intro1Core(v___x_2885_, v___x_2886_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v_fst_2889_; lean_object* v_snd_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2887_, 1);
v_fst_2889_ = lean_ctor_get(v_a_2888_, 0);
lean_inc(v_fst_2889_);
v_snd_2890_ = lean_ctor_get(v_a_2888_, 1);
lean_inc(v_snd_2890_);
lean_dec(v_a_2888_);
v___x_2891_ = l_Lean_Expr_mvarId_x21(v_a_2863_);
lean_dec(v_a_2863_);
v___x_2892_ = l_Lean_Meta_intro1Core(v___x_2891_, v___x_2886_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v_snd_2894_; lean_object* v___x_2895_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___x_2892_, 1);
v_snd_2894_ = lean_ctor_get(v_a_2893_, 1);
lean_inc(v_snd_2894_);
lean_dec(v_a_2893_);
lean_inc_ref(v_arg_2785_);
v___x_2895_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkTest(v_fvarId_2784_, v_arg_2785_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2907_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2898_ = v___x_2895_;
v_isShared_2899_ = v_isSharedCheck_2907_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2895_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2907_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2900_; lean_object* v___x_2902_; 
v___x_2900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2900_, 0, v_a_2896_);
lean_ctor_set(v___x_2900_, 1, v_arg_2785_);
lean_ctor_set(v___x_2900_, 2, v_snd_2890_);
lean_ctor_set(v___x_2900_, 3, v_fst_2889_);
lean_ctor_set(v___x_2900_, 4, v_snd_2894_);
if (v_isShared_2884_ == 0)
{
lean_ctor_set_tag(v___x_2883_, 1);
lean_ctor_set(v___x_2883_, 0, v___x_2900_);
v___x_2902_ = v___x_2883_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2900_);
v___x_2902_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
lean_object* v___x_2904_; 
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2902_);
v___x_2904_ = v___x_2898_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2902_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec(v_snd_2894_);
lean_dec(v_snd_2890_);
lean_dec(v_fst_2889_);
lean_del_object(v___x_2883_);
lean_dec_ref(v_arg_2785_);
v_a_2908_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2895_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2895_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec(v_snd_2890_);
lean_dec(v_fst_2889_);
lean_del_object(v___x_2883_);
lean_dec_ref(v_arg_2785_);
lean_dec(v_fvarId_2784_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
v_a_2916_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2892_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2892_);
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
lean_del_object(v___x_2883_);
lean_dec(v_a_2863_);
lean_dec_ref(v_arg_2785_);
lean_dec(v_fvarId_2784_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
v_a_2924_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2887_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2887_);
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
lean_dec(v_a_2856_);
lean_dec(v___x_2846_);
lean_dec_ref(v___x_2820_);
lean_dec_ref(v_arg_2812_);
lean_dec_ref(v_arg_2811_);
lean_dec_ref(v_arg_2810_);
lean_dec_ref(v_arg_2808_);
lean_dec_ref(v_arg_2807_);
lean_dec_ref(v_arg_2785_);
lean_dec(v_fvarId_2784_);
lean_dec_ref_known(v_arg_2783_, 1);
lean_dec_ref(v___x_2781_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
v_a_2934_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2862_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2862_);
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
lean_dec(v_a_2848_);
lean_dec(v___x_2846_);
lean_dec_ref(v___x_2820_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_arg_2812_);
lean_dec_ref(v_arg_2811_);
lean_dec_ref(v_arg_2810_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2808_);
lean_dec_ref(v_arg_2807_);
lean_dec_ref(v_arg_2785_);
lean_dec(v_fvarId_2784_);
lean_dec_ref_known(v_arg_2783_, 1);
lean_dec_ref(v___x_2781_);
lean_dec_ref(v_arg_2774_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
v_a_2942_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2855_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2855_);
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
lean_dec(v_a_2848_);
lean_dec(v___x_2846_);
lean_dec_ref(v___x_2820_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_arg_2812_);
lean_dec_ref(v_arg_2811_);
lean_dec_ref(v_arg_2810_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2808_);
lean_dec_ref(v_arg_2807_);
lean_dec_ref(v_arg_2785_);
lean_dec(v_fvarId_2784_);
lean_dec_ref_known(v_arg_2783_, 1);
lean_dec_ref(v___x_2781_);
lean_dec_ref(v_arg_2774_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
v_a_2950_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2853_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2853_);
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
lean_dec(v___x_2846_);
lean_dec_ref(v___x_2820_);
lean_dec_ref(v___x_2817_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_arg_2812_);
lean_dec_ref(v_arg_2811_);
lean_dec_ref(v_arg_2810_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2808_);
lean_dec_ref(v_arg_2807_);
lean_dec_ref(v_arg_2785_);
lean_dec(v_fvarId_2784_);
lean_dec_ref_known(v_arg_2783_, 1);
lean_dec_ref(v___x_2781_);
lean_dec_ref(v_arg_2774_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
v_a_2958_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2847_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2847_);
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
}
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_dec_ref(v___x_2820_);
lean_dec_ref(v___x_2817_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_arg_2812_);
lean_dec_ref(v_arg_2811_);
lean_dec_ref(v_arg_2810_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2808_);
lean_dec_ref(v_arg_2807_);
lean_dec_ref(v_arg_2785_);
lean_dec(v_fvarId_2784_);
lean_dec_ref_known(v_arg_2783_, 1);
lean_dec_ref(v___x_2781_);
lean_dec_ref(v_arg_2774_);
lean_dec_ref(v___x_2771_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
v_a_2967_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2836_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2836_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
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
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_dec_ref(v___x_2833_);
lean_dec_ref(v___x_2820_);
lean_dec_ref(v___x_2817_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_arg_2812_);
lean_dec_ref(v_arg_2811_);
lean_dec_ref(v_arg_2810_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2808_);
lean_dec_ref(v_arg_2807_);
lean_dec_ref(v_arg_2785_);
lean_dec(v_fvarId_2784_);
lean_dec_ref_known(v_arg_2783_, 1);
lean_dec_ref(v___x_2781_);
lean_dec_ref(v_arg_2774_);
lean_dec_ref(v___x_2771_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
v_a_2975_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2834_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2834_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
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
}
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec_ref(v___x_2820_);
lean_dec_ref(v___x_2817_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_arg_2812_);
lean_dec_ref(v_arg_2811_);
lean_dec_ref(v_arg_2810_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2808_);
lean_dec_ref(v_arg_2807_);
lean_dec_ref(v_arg_2785_);
lean_dec(v_fvarId_2784_);
lean_dec_ref_known(v_arg_2783_, 1);
lean_dec_ref(v___x_2781_);
lean_dec_ref(v_arg_2774_);
lean_dec_ref(v___x_2771_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
v_a_2984_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2821_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2821_);
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
lean_object* v___x_2992_; lean_object* v___x_2993_; 
lean_dec_ref(v_arg_2783_);
lean_dec_ref(v___x_2781_);
lean_dec_ref(v___x_2779_);
lean_dec_ref(v___x_2775_);
lean_dec_ref(v_arg_2774_);
lean_dec_ref(v___x_2771_);
lean_dec_ref(v___x_2769_);
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2763_);
lean_dec_ref(v___x_2761_);
lean_del_object(v___x_2747_);
lean_dec(v_a_2745_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
v___x_2992_ = lean_box(0);
v___x_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
return v___x_2993_;
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
v___jp_2749_:
{
lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2750_ = lean_box(0);
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 0, v___x_2750_);
v___x_2752_ = v___x_2747_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2750_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_mvarId_2729_);
v_a_2995_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2744_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2744_);
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
v___jp_2735_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = lean_box(0);
v___x_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
return v___x_2737_;
}
v___jp_2738_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = lean_box(0);
v___x_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
return v___x_2740_;
}
v___jp_2741_:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2742_ = lean_box(0);
v___x_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2742_);
return v___x_2743_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___boxed(lean_object* v_mvarId_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1(v_mvarId_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f(lean_object* v_mvarId_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_){
_start:
{
lean_object* v___f_3016_; lean_object* v___x_3017_; 
lean_inc(v_mvarId_3010_);
v___f_3016_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3016_, 0, v_mvarId_3010_);
v___x_3017_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__2___redArg(v_mvarId_3010_, v___f_3016_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f___boxed(lean_object* v_mvarId_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f(v_mvarId_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_);
lean_dec(v_a_3022_);
lean_dec_ref(v_a_3021_);
lean_dec(v_a_3020_);
lean_dec_ref(v_a_3019_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_substKept_spec__0(lean_object* v_as_3025_, size_t v_sz_3026_, size_t v_i_3027_, lean_object* v_b_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
uint8_t v___x_3034_; 
v___x_3034_ = lean_usize_dec_lt(v_i_3027_, v_sz_3026_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; 
v___x_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3035_, 0, v_b_3028_);
return v___x_3035_;
}
else
{
lean_object* v_a_3036_; lean_object* v_h_3037_; lean_object* v_fst_3038_; lean_object* v_snd_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; lean_object* v___x_3043_; 
v_a_3036_ = lean_array_uget_borrowed(v_as_3025_, v_i_3027_);
v_h_3037_ = lean_ctor_get(v_a_3036_, 2);
v_fst_3038_ = lean_ctor_get(v_b_3028_, 0);
lean_inc(v_fst_3038_);
v_snd_3039_ = lean_ctor_get(v_b_3028_, 1);
lean_inc(v_snd_3039_);
lean_dec_ref(v_b_3028_);
lean_inc(v_h_3037_);
v___x_3040_ = l_Lean_Meta_FVarSubst_get(v_snd_3039_, v_h_3037_);
v___x_3041_ = l_Lean_Expr_fvarId_x21(v___x_3040_);
lean_dec_ref(v___x_3040_);
v___x_3042_ = 0;
v___x_3043_ = l_Lean_Meta_substCore(v_fst_3038_, v___x_3041_, v___x_3042_, v_snd_3039_, v___x_3034_, v___x_3042_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v_fst_3045_; lean_object* v_snd_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3056_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_a_3044_);
lean_dec_ref_known(v___x_3043_, 1);
v_fst_3045_ = lean_ctor_get(v_a_3044_, 0);
v_snd_3046_ = lean_ctor_get(v_a_3044_, 1);
v_isSharedCheck_3056_ = !lean_is_exclusive(v_a_3044_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3048_ = v_a_3044_;
v_isShared_3049_ = v_isSharedCheck_3056_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_snd_3046_);
lean_inc(v_fst_3045_);
lean_dec(v_a_3044_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3056_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 1, v_fst_3045_);
lean_ctor_set(v___x_3048_, 0, v_snd_3046_);
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_snd_3046_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_fst_3045_);
v___x_3051_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
size_t v___x_3052_; size_t v___x_3053_; 
v___x_3052_ = ((size_t)1ULL);
v___x_3053_ = lean_usize_add(v_i_3027_, v___x_3052_);
v_i_3027_ = v___x_3053_;
v_b_3028_ = v___x_3051_;
goto _start;
}
}
}
else
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
v_a_3057_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___x_3043_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3043_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_substKept_spec__0___boxed(lean_object* v_as_3065_, lean_object* v_sz_3066_, lean_object* v_i_3067_, lean_object* v_b_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
size_t v_sz_boxed_3074_; size_t v_i_boxed_3075_; lean_object* v_res_3076_; 
v_sz_boxed_3074_ = lean_unbox_usize(v_sz_3066_);
lean_dec(v_sz_3066_);
v_i_boxed_3075_ = lean_unbox_usize(v_i_3067_);
lean_dec(v_i_3067_);
v_res_3076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_substKept_spec__0(v_as_3065_, v_sz_boxed_3074_, v_i_boxed_3075_, v_b_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec_ref(v_as_3065_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_substKept(lean_object* v_mvarId_3077_, lean_object* v_kept_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_){
_start:
{
lean_object* v_fvarSubst_3084_; lean_object* v___x_3085_; size_t v_sz_3086_; size_t v___x_3087_; lean_object* v___x_3088_; 
v_fvarSubst_3084_ = lean_box(0);
v___x_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3085_, 0, v_mvarId_3077_);
lean_ctor_set(v___x_3085_, 1, v_fvarSubst_3084_);
v_sz_3086_ = lean_array_size(v_kept_3078_);
v___x_3087_ = ((size_t)0ULL);
v___x_3088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_substKept_spec__0(v_kept_3078_, v_sz_3086_, v___x_3087_, v___x_3085_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3097_; 
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3091_ = v___x_3088_;
v_isShared_3092_ = v_isSharedCheck_3097_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3088_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3097_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v_fst_3093_; lean_object* v___x_3095_; 
v_fst_3093_ = lean_ctor_get(v_a_3089_, 0);
lean_inc(v_fst_3093_);
lean_dec(v_a_3089_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 0, v_fst_3093_);
v___x_3095_ = v___x_3091_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_fst_3093_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
v_a_3098_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3088_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3088_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_substKept___boxed(lean_object* v_mvarId_3106_, lean_object* v_kept_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_substKept(v_mvarId_3106_, v_kept_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_);
lean_dec(v_a_3111_);
lean_dec_ref(v_a_3110_);
lean_dec(v_a_3109_);
lean_dec_ref(v_a_3108_);
lean_dec_ref(v_kept_3107_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visitSplit_spec__1___redArg(lean_object* v_s_3114_, lean_object* v_keptTrue_3115_, lean_object* v_as_3116_, size_t v_i_3117_, size_t v_stop_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
uint8_t v___x_3124_; 
v___x_3124_ = lean_usize_dec_eq(v_i_3117_, v_stop_3118_);
if (v___x_3124_ == 0)
{
lean_object* v_mvarIdTrue_3125_; uint8_t v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v_mvarIdTrue_3125_ = lean_ctor_get(v_s_3114_, 2);
v___x_3126_ = 1;
v___x_3127_ = lean_array_uget_borrowed(v_as_3116_, v_i_3117_);
lean_inc(v___x_3127_);
lean_inc_ref(v_keptTrue_3115_);
lean_inc(v_mvarIdTrue_3125_);
v___x_3128_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing(v_mvarIdTrue_3125_, v_keptTrue_3115_, v___x_3127_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3141_; 
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3131_ = v___x_3128_;
v_isShared_3132_ = v_isSharedCheck_3141_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3128_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3141_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
uint8_t v___x_3133_; 
v___x_3133_ = lean_unbox(v_a_3129_);
lean_dec(v_a_3129_);
if (v___x_3133_ == 0)
{
size_t v___x_3134_; size_t v___x_3135_; 
lean_del_object(v___x_3131_);
v___x_3134_ = ((size_t)1ULL);
v___x_3135_ = lean_usize_add(v_i_3117_, v___x_3134_);
v_i_3117_ = v___x_3135_;
goto _start;
}
else
{
lean_object* v___x_3137_; lean_object* v___x_3139_; 
lean_dec_ref(v_keptTrue_3115_);
lean_dec_ref(v_s_3114_);
v___x_3137_ = lean_box(v___x_3126_);
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 0, v___x_3137_);
v___x_3139_ = v___x_3131_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3137_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
else
{
lean_dec_ref(v_keptTrue_3115_);
lean_dec_ref(v_s_3114_);
return v___x_3128_;
}
}
else
{
uint8_t v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
lean_dec_ref(v_keptTrue_3115_);
lean_dec_ref(v_s_3114_);
v___x_3142_ = 0;
v___x_3143_ = lean_box(v___x_3142_);
v___x_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
return v___x_3144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visitSplit_spec__1___redArg___boxed(lean_object* v_s_3145_, lean_object* v_keptTrue_3146_, lean_object* v_as_3147_, lean_object* v_i_3148_, lean_object* v_stop_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
size_t v_i_boxed_3155_; size_t v_stop_boxed_3156_; lean_object* v_res_3157_; 
v_i_boxed_3155_ = lean_unbox_usize(v_i_3148_);
lean_dec(v_i_3148_);
v_stop_boxed_3156_ = lean_unbox_usize(v_stop_3149_);
lean_dec(v_stop_3149_);
v_res_3157_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visitSplit_spec__1___redArg(v_s_3145_, v_keptTrue_3146_, v_as_3147_, v_i_boxed_3155_, v_stop_boxed_3156_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec_ref(v_as_3147_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visit(lean_object* v_index_3159_, lean_object* v_mvarId_3160_, lean_object* v_kept_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3168_ = ((lean_object*)(l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visit___closed__0));
v___x_3169_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_3160_, v___x_3168_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v___x_3171_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
lean_inc_n(v_a_3170_, 2);
lean_dec_ref_known(v___x_3169_, 1);
v___x_3171_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f(v_a_3170_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_a_3172_);
lean_dec_ref_known(v___x_3171_, 1);
if (lean_obj_tag(v_a_3172_) == 1)
{
lean_object* v_val_3173_; lean_object* v___x_3174_; 
lean_dec(v_a_3170_);
v_val_3173_ = lean_ctor_get(v_a_3172_, 0);
lean_inc(v_val_3173_);
lean_dec_ref_known(v_a_3172_, 1);
v___x_3174_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visitSplit(v_index_3159_, v_val_3173_, v_kept_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_);
return v___x_3174_;
}
else
{
uint8_t v___x_3175_; lean_object* v___x_3176_; 
lean_dec(v_a_3172_);
v___x_3175_ = 1;
v___x_3176_ = l_Lean_Meta_saveState___redArg(v_a_3164_, v_a_3166_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3178_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc(v_a_3177_);
lean_dec_ref_known(v___x_3176_, 1);
lean_inc(v_a_3170_);
v___x_3178_ = l_Lean_MVarId_refl(v_a_3170_, v___x_3175_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3186_; 
lean_dec(v_a_3177_);
lean_dec(v_a_3170_);
lean_dec_ref(v_kept_3161_);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3186_ == 0)
{
lean_object* v_unused_3187_; 
v_unused_3187_ = lean_ctor_get(v___x_3178_, 0);
lean_dec(v_unused_3187_);
v___x_3180_ = v___x_3178_;
v_isShared_3181_ = v_isSharedCheck_3186_;
goto v_resetjp_3179_;
}
else
{
lean_dec(v___x_3178_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3186_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3182_; lean_object* v___x_3184_; 
v___x_3182_ = lean_box(0);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 0, v___x_3182_);
v___x_3184_ = v___x_3180_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3182_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
else
{
lean_object* v_a_3188_; uint8_t v___x_3189_; 
v_a_3188_ = lean_ctor_get(v___x_3178_, 0);
v___x_3189_ = l_Lean_Exception_isInterrupt(v_a_3188_);
if (v___x_3189_ == 0)
{
uint8_t v___x_3190_; 
lean_inc(v_a_3188_);
v___x_3190_ = l_Lean_Exception_isRuntime(v_a_3188_);
if (v___x_3190_ == 0)
{
lean_object* v___x_3191_; 
lean_dec_ref_known(v___x_3178_, 1);
v___x_3191_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3177_, v_a_3164_, v_a_3166_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v___x_3192_; 
lean_dec_ref_known(v___x_3191_, 1);
v___x_3192_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_substKept(v_a_3170_, v_kept_3161_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_);
lean_dec_ref(v_kept_3161_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3204_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3195_ = v___x_3192_;
v_isShared_3196_ = v_isSharedCheck_3204_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3192_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3204_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3202_; 
v___x_3197_ = lean_st_ref_take(v_a_3162_);
v___x_3198_ = lean_box(0);
v___x_3199_ = lean_array_push(v___x_3197_, v_a_3193_);
v___x_3200_ = lean_st_ref_put(v_a_3162_, v___x_3199_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v___x_3198_);
v___x_3202_ = v___x_3195_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3198_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
v_a_3205_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3192_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3192_);
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
else
{
lean_dec(v_a_3170_);
lean_dec_ref(v_kept_3161_);
return v___x_3191_;
}
}
else
{
lean_dec(v_a_3177_);
lean_dec(v_a_3170_);
lean_dec_ref(v_kept_3161_);
return v___x_3178_;
}
}
else
{
lean_dec(v_a_3177_);
lean_dec(v_a_3170_);
lean_dec_ref(v_kept_3161_);
return v___x_3178_;
}
}
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec(v_a_3170_);
lean_dec_ref(v_kept_3161_);
v_a_3213_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3176_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3176_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_dec(v_a_3170_);
lean_dec_ref(v_kept_3161_);
v_a_3221_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3171_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3171_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
else
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
lean_dec_ref(v_kept_3161_);
v_a_3229_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___x_3169_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3169_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3234_; 
if (v_isShared_3232_ == 0)
{
v___x_3234_ = v___x_3231_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3229_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visitSplit(lean_object* v_index_3237_, lean_object* v_s_3238_, lean_object* v_kept_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_){
_start:
{
lean_object* v_test_3246_; lean_object* v_v_3247_; lean_object* v_mvarIdTrue_3248_; lean_object* v_h_3249_; lean_object* v_mvarIdFalse_3250_; lean_object* v___x_3251_; lean_object* v_keptTrue_3252_; lean_object* v_hyps_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; 
v_test_3246_ = lean_ctor_get(v_s_3238_, 0);
v_v_3247_ = lean_ctor_get(v_s_3238_, 1);
v_mvarIdTrue_3248_ = lean_ctor_get(v_s_3238_, 2);
lean_inc(v_mvarIdTrue_3248_);
v_h_3249_ = lean_ctor_get(v_s_3238_, 3);
v_mvarIdFalse_3250_ = lean_ctor_get(v_s_3238_, 4);
lean_inc(v_mvarIdFalse_3250_);
lean_inc(v_h_3249_);
lean_inc_ref(v_v_3247_);
lean_inc_ref(v_test_3246_);
v___x_3251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3251_, 0, v_test_3246_);
lean_ctor_set(v___x_3251_, 1, v_v_3247_);
lean_ctor_set(v___x_3251_, 2, v_h_3249_);
lean_inc_ref(v_kept_3239_);
v_keptTrue_3252_ = lean_array_push(v_kept_3239_, v___x_3251_);
v_hyps_3256_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_Index_retrieve(v_index_3237_, v_keptTrue_3252_, v_test_3246_);
v___x_3257_ = lean_unsigned_to_nat(0u);
v___x_3258_ = lean_array_get_size(v_hyps_3256_);
v___x_3259_ = lean_nat_dec_lt(v___x_3257_, v___x_3258_);
if (v___x_3259_ == 0)
{
lean_dec_ref(v_hyps_3256_);
lean_dec_ref(v_s_3238_);
goto v___jp_3253_;
}
else
{
if (v___x_3259_ == 0)
{
lean_dec_ref(v_hyps_3256_);
lean_dec_ref(v_s_3238_);
goto v___jp_3253_;
}
else
{
size_t v___x_3260_; size_t v___x_3261_; lean_object* v___x_3262_; 
v___x_3260_ = ((size_t)0ULL);
v___x_3261_ = lean_usize_of_nat(v___x_3258_);
lean_inc_ref(v_keptTrue_3252_);
v___x_3262_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visitSplit_spec__1___redArg(v_s_3238_, v_keptTrue_3252_, v_hyps_3256_, v___x_3260_, v___x_3261_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_);
lean_dec_ref(v_hyps_3256_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_a_3263_; uint8_t v___x_3264_; 
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_a_3263_);
lean_dec_ref_known(v___x_3262_, 1);
v___x_3264_ = lean_unbox(v_a_3263_);
lean_dec(v_a_3263_);
if (v___x_3264_ == 0)
{
goto v___jp_3253_;
}
else
{
lean_object* v___x_3265_; 
lean_dec_ref(v_keptTrue_3252_);
lean_dec(v_mvarIdTrue_3248_);
v___x_3265_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visit(v_index_3237_, v_mvarIdFalse_3250_, v_kept_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_);
return v___x_3265_;
}
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
lean_dec_ref(v_keptTrue_3252_);
lean_dec(v_mvarIdFalse_3250_);
lean_dec(v_mvarIdTrue_3248_);
lean_dec_ref(v_kept_3239_);
v_a_3266_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_3262_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3262_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
}
v___jp_3253_:
{
lean_object* v___x_3254_; 
v___x_3254_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visit(v_index_3237_, v_mvarIdTrue_3248_, v_keptTrue_3252_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v___x_3255_; 
lean_dec_ref_known(v___x_3254_, 1);
v___x_3255_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visit(v_index_3237_, v_mvarIdFalse_3250_, v_kept_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_);
return v___x_3255_;
}
else
{
lean_dec(v_mvarIdFalse_3250_);
lean_dec_ref(v_kept_3239_);
return v___x_3254_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visitSplit___boxed(lean_object* v_index_3274_, lean_object* v_s_3275_, lean_object* v_kept_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visitSplit(v_index_3274_, v_s_3275_, v_kept_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_);
lean_dec(v_a_3281_);
lean_dec_ref(v_a_3280_);
lean_dec(v_a_3279_);
lean_dec_ref(v_a_3278_);
lean_dec(v_a_3277_);
lean_dec_ref(v_index_3274_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visit___boxed(lean_object* v_index_3284_, lean_object* v_mvarId_3285_, lean_object* v_kept_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visit(v_index_3284_, v_mvarId_3285_, v_kept_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_);
lean_dec(v_a_3291_);
lean_dec_ref(v_a_3290_);
lean_dec(v_a_3289_);
lean_dec_ref(v_a_3288_);
lean_dec(v_a_3287_);
lean_dec_ref(v_index_3284_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visitSplit_spec__1(lean_object* v_s_3294_, lean_object* v_keptTrue_3295_, lean_object* v_as_3296_, size_t v_i_3297_, size_t v_stop_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visitSplit_spec__1___redArg(v_s_3294_, v_keptTrue_3295_, v_as_3296_, v_i_3297_, v_stop_3298_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visitSplit_spec__1___boxed(lean_object* v_s_3306_, lean_object* v_keptTrue_3307_, lean_object* v_as_3308_, lean_object* v_i_3309_, lean_object* v_stop_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
size_t v_i_boxed_3317_; size_t v_stop_boxed_3318_; lean_object* v_res_3319_; 
v_i_boxed_3317_ = lean_unbox_usize(v_i_3309_);
lean_dec(v_i_3309_);
v_stop_boxed_3318_ = lean_unbox_usize(v_stop_3310_);
lean_dec(v_stop_3310_);
v_res_3319_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visitSplit_spec__1(v_s_3306_, v_keptTrue_3307_, v_as_3308_, v_i_boxed_3317_, v_stop_boxed_3318_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec(v___y_3311_);
lean_dec_ref(v_as_3308_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Match_splitDiteTree_spec__0_spec__0(lean_object* v_msgData_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v___x_3326_; lean_object* v_env_3327_; uint8_t v___x_3328_; lean_object* v_env_3329_; lean_object* v___x_3330_; lean_object* v_toCold_3331_; lean_object* v_mctx_3332_; lean_object* v_lctx_3333_; lean_object* v_options_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3326_ = lean_st_ref_get(v___y_3324_);
v_env_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc_ref(v_env_3327_);
lean_dec(v___x_3326_);
v___x_3328_ = 0;
v_env_3329_ = l_Lean_Environment_setRecordingDeps(v_env_3327_, v___x_3328_);
v___x_3330_ = lean_st_ref_get(v___y_3322_);
v_toCold_3331_ = lean_ctor_get(v___y_3323_, 0);
v_mctx_3332_ = lean_ctor_get(v___x_3330_, 0);
lean_inc_ref(v_mctx_3332_);
lean_dec(v___x_3330_);
v_lctx_3333_ = lean_ctor_get(v___y_3321_, 2);
v_options_3334_ = lean_ctor_get(v_toCold_3331_, 2);
lean_inc_ref(v_options_3334_);
lean_inc_ref(v_lctx_3333_);
v___x_3335_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3335_, 0, v_env_3329_);
lean_ctor_set(v___x_3335_, 1, v_mctx_3332_);
lean_ctor_set(v___x_3335_, 2, v_lctx_3333_);
lean_ctor_set(v___x_3335_, 3, v_options_3334_);
v___x_3336_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
lean_ctor_set(v___x_3336_, 1, v_msgData_3320_);
v___x_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3336_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Match_splitDiteTree_spec__0_spec__0___boxed(lean_object* v_msgData_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Match_splitDiteTree_spec__0_spec__0(v_msgData_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_splitDiteTree_spec__0___redArg(lean_object* v_msg_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v_ref_3351_; lean_object* v___x_3352_; lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3361_; 
v_ref_3351_ = lean_ctor_get(v___y_3348_, 2);
v___x_3352_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Match_splitDiteTree_spec__0_spec__0(v_msg_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3355_ = v___x_3352_;
v_isShared_3356_ = v_isSharedCheck_3361_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3352_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3361_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3357_; lean_object* v___x_3359_; 
lean_inc(v_ref_3351_);
v___x_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3357_, 0, v_ref_3351_);
lean_ctor_set(v___x_3357_, 1, v_a_3353_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set_tag(v___x_3355_, 1);
lean_ctor_set(v___x_3355_, 0, v___x_3357_);
v___x_3359_ = v___x_3355_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3357_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_splitDiteTree_spec__0___redArg___boxed(lean_object* v_msg_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_Lean_throwError___at___00Lean_Meta_Match_splitDiteTree_spec__0___redArg(v_msg_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
return v_res_3368_;
}
}
static lean_object* _init_l_Lean_Meta_Match_splitDiteTree___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3370_ = ((lean_object*)(l_Lean_Meta_Match_splitDiteTree___lam__0___closed__0));
v___x_3371_ = l_Lean_stringToMessageData(v___x_3370_);
return v___x_3371_;
}
}
static lean_object* _init_l_Lean_Meta_Match_splitDiteTree___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = ((lean_object*)(l_Lean_Meta_Match_splitDiteTree___lam__0___closed__3));
v___x_3376_ = l_Lean_stringToMessageData(v___x_3375_);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_splitDiteTree___lam__0(lean_object* v_mvarId_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v___x_3383_; 
lean_inc(v_mvarId_3377_);
v___x_3383_ = l_Lean_MVarId_getType(v_mvarId_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v_a_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; uint8_t v___x_3387_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_a_3384_);
lean_dec_ref_known(v___x_3383_, 1);
v___x_3385_ = ((lean_object*)(l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_collectVars_visit___redArg___closed__3));
v___x_3386_ = lean_unsigned_to_nat(3u);
v___x_3387_ = l_Lean_Expr_isAppOfArity(v_a_3384_, v___x_3385_, v___x_3386_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3388_; lean_object* v___x_3389_; 
lean_dec(v_a_3384_);
lean_dec(v_mvarId_3377_);
v___x_3388_ = lean_obj_once(&l_Lean_Meta_Match_splitDiteTree___lam__0___closed__1, &l_Lean_Meta_Match_splitDiteTree___lam__0___closed__1_once, _init_l_Lean_Meta_Match_splitDiteTree___lam__0___closed__1);
v___x_3389_ = l_Lean_throwError___at___00Lean_Meta_Match_splitDiteTree_spec__0___redArg(v___x_3388_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
return v___x_3389_;
}
else
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3390_ = l_Lean_Expr_appFn_x21(v_a_3384_);
lean_dec(v_a_3384_);
v___x_3391_ = l_Lean_Expr_appArg_x21(v___x_3390_);
lean_dec_ref(v___x_3390_);
v___x_3392_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_split_x3f(v_mvarId_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v___x_3392_, 1);
if (lean_obj_tag(v_a_3393_) == 1)
{
lean_object* v_val_3394_; lean_object* v___x_3395_; 
v_val_3394_ = lean_ctor_get(v_a_3393_, 0);
lean_inc(v_val_3394_);
lean_dec_ref_known(v_a_3393_, 1);
v___x_3395_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_mkIndex(v___x_3391_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_a_3396_);
lean_dec_ref_known(v___x_3395_, 1);
v___x_3397_ = ((lean_object*)(l_Lean_Meta_Match_splitDiteTree___lam__0___closed__2));
v___x_3398_ = lean_st_mk_ref(v___x_3397_);
v___x_3399_ = l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_visitSplit(v_a_3396_, v_val_3394_, v___x_3397_, v___x_3398_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
lean_dec(v_a_3396_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3407_; 
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3407_ == 0)
{
lean_object* v_unused_3408_; 
v_unused_3408_ = lean_ctor_get(v___x_3399_, 0);
lean_dec(v_unused_3408_);
v___x_3401_ = v___x_3399_;
v_isShared_3402_ = v_isSharedCheck_3407_;
goto v_resetjp_3400_;
}
else
{
lean_dec(v___x_3399_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3407_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3403_; lean_object* v___x_3405_; 
v___x_3403_ = lean_st_ref_get(v___x_3398_);
lean_dec(v___x_3398_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 0, v___x_3403_);
v___x_3405_ = v___x_3401_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
lean_dec(v___x_3398_);
v_a_3409_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3399_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3399_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
else
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
lean_dec(v_val_3394_);
v_a_3417_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3395_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3395_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
else
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
lean_dec(v_a_3393_);
lean_dec_ref(v___x_3391_);
v___x_3425_ = lean_obj_once(&l_Lean_Meta_Match_splitDiteTree___lam__0___closed__4, &l_Lean_Meta_Match_splitDiteTree___lam__0___closed__4_once, _init_l_Lean_Meta_Match_splitDiteTree___lam__0___closed__4);
v___x_3426_ = l_Lean_throwError___at___00Lean_Meta_Match_splitDiteTree_spec__0___redArg(v___x_3425_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
return v___x_3426_;
}
}
else
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_dec_ref(v___x_3391_);
v_a_3427_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3392_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3392_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
}
else
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
lean_dec(v_mvarId_3377_);
v_a_3435_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3383_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3383_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_splitDiteTree___lam__0___boxed(lean_object* v_mvarId_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Lean_Meta_Match_splitDiteTree___lam__0(v_mvarId_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_splitDiteTree(lean_object* v_mvarId_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_){
_start:
{
lean_object* v___f_3456_; lean_object* v___x_3457_; 
lean_inc(v_mvarId_3450_);
v___f_3456_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_splitDiteTree___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3456_, 0, v_mvarId_3450_);
v___x_3457_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_closeUsing_spec__2___redArg(v_mvarId_3450_, v___f_3456_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_);
return v___x_3457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_splitDiteTree___boxed(lean_object* v_mvarId_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Lean_Meta_Match_splitDiteTree(v_mvarId_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
lean_dec(v_a_3462_);
lean_dec_ref(v_a_3461_);
lean_dec(v_a_3460_);
lean_dec_ref(v_a_3459_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_splitDiteTree_spec__0(lean_object* v_00_u03b1_3465_, lean_object* v_msg_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v___x_3472_; 
v___x_3472_ = l_Lean_throwError___at___00Lean_Meta_Match_splitDiteTree_spec__0___redArg(v_msg_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
return v___x_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_splitDiteTree_spec__0___boxed(lean_object* v_00_u03b1_3473_, lean_object* v_msg_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Lean_throwError___at___00Lean_Meta_Match_splitDiteTree_spec__0(v_00_u03b1_3473_, v_msg_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
return v_res_3480_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_Value(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ForEachExpr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_DiteTree(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Contradiction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Match_DiteTree_instInhabitedNode_default = _init_l_Lean_Meta_Match_DiteTree_instInhabitedNode_default();
lean_mark_persistent(l_Lean_Meta_Match_DiteTree_instInhabitedNode_default);
l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_instInhabitedNode = _init_l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_instInhabitedNode();
lean_mark_persistent(l___private_Lean_Meta_Match_DiteTree_0__Lean_Meta_Match_DiteTree_instInhabitedNode);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Match_DiteTree(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_Value(uint8_t builtin);
lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_DiteTree(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Contradiction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_DiteTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Match_DiteTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Match_DiteTree(builtin);
}
#ifdef __cplusplus
}
#endif
