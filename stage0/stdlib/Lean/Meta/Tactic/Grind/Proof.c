// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Proof
// Imports: public import Lean.Meta.Tactic.Grind.Types import Init.Grind.Lemmas import Init.Grind.Util
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_congrPlaceholderProof;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_eqCongrSymmPlaceholderProof;
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Goal_hasSameRoot(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_useFunCC___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FunInfo_getArity(lean_object*);
lean_object* l_Lean_Meta_Grind_mkHCongrWithArity___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Meta.Tactic.Grind.Proof"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "_private.Lean.Meta.Tactic.Grind.Proof.0.Lean.Meta.Grind.findCommon"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "`grind` currently cannot build congruence proofs for over-applied terms such as"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\nand"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "assertion violation: thm.argKinds.size == numArgs\n    "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Meta.Tactic.Grind.Proof.0.Lean.Meta.Grind.mkHCongrProof'"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 52, .m_data = "assertion violation: isSameExpr n₁.root n₂.root\n    "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "_private.Lean.Meta.Tactic.Grind.Proof.0.Lean.Meta.Grind.mkEqProofCore"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2;
static const lean_string_object l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.Grind.mkEqCongrSymmProof"};
static const lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2;
static const lean_string_object l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 225, .m_capacity = 225, .m_length = 216, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Proof.1529172837._hygCtx._hyg.980.0 ).hasSameRoot a₁ b₂ && ( __do_lift._@.Lean.Meta.Tactic.Grind.Proof.1529172837._hygCtx._hyg.980.1 ).hasSameRoot b₁ a₂\n    "};
static const lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4;
static const lean_string_object l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "heq_congr'"};
static const lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__5_value),LEAN_SCALAR_PTR_LITERAL(12, 59, 80, 84, 143, 62, 233, 44)}};
static const lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eq_congr'"};
static const lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__7_value),LEAN_SCALAR_PTR_LITERAL(203, 224, 251, 50, 71, 48, 5, 203)}};
static const lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "implies_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 71, 54, 187, 9, 73, 178, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Meta.Tactic.Grind.Proof.0.Lean.Meta.Grind.mkCongrProof"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "assertion violation: rhs.getAppNumArgs == numArgs\n      "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "assertion violation: rhs.getAppNumArgs == numArgs\n    "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "_private.Lean.Meta.Tactic.Grind.Proof.0.Lean.Meta.Grind.mkHCongrProof"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_mkEqCongrProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Meta.Grind.mkEqCongrProof"};
static const lean_object* l_Lean_Meta_Grind_mkEqCongrProof___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkEqCongrProof___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkEqCongrProof___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkEqCongrProof___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_mkEqCongrProof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkEqCongrProof___closed__2;
static const lean_string_object l_Lean_Meta_Grind_mkEqCongrProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 225, .m_capacity = 225, .m_length = 216, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Proof.1529172837._hygCtx._hyg.502.0 ).hasSameRoot a₁ a₂ && ( __do_lift._@.Lean.Meta.Tactic.Grind.Proof.1529172837._hygCtx._hyg.502.1 ).hasSameRoot b₁ b₂\n    "};
static const lean_object* l_Lean_Meta_Grind_mkEqCongrProof___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_mkEqCongrProof___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkEqCongrProof___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkEqCongrProof___closed__4;
static const lean_string_object l_Lean_Meta_Grind_mkEqCongrProof___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "heq_congr"};
static const lean_object* l_Lean_Meta_Grind_mkEqCongrProof___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_mkEqCongrProof___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkEqCongrProof___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkEqCongrProof___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkEqCongrProof___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkEqCongrProof___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkEqCongrProof___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_mkEqCongrProof___closed__5_value),LEAN_SCALAR_PTR_LITERAL(42, 237, 37, 65, 223, 91, 106, 181)}};
static const lean_object* l_Lean_Meta_Grind_mkEqCongrProof___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_mkEqCongrProof___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_mkEqCongrProof___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "eq_congr"};
static const lean_object* l_Lean_Meta_Grind_mkEqCongrProof___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_mkEqCongrProof___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkEqCongrProof___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkEqCongrProof___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkEqCongrProof___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkEqCongrProof___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkEqCongrProof___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_mkEqCongrProof___closed__7_value),LEAN_SCALAR_PTR_LITERAL(239, 157, 43, 237, 198, 146, 143, 97)}};
static const lean_object* l_Lean_Meta_Grind_mkEqCongrProof___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_mkEqCongrProof___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "nestedDecidable"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6_value),LEAN_SCALAR_PTR_LITERAL(65, 76, 105, 85, 179, 183, 200, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "nestedDecidable_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(215, 141, 232, 33, 101, 236, 126, 130)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "nestedProof"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8_value),LEAN_SCALAR_PTR_LITERAL(182, 140, 29, 19, 223, 104, 218, 25)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "nestedProof_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 120, 160, 223, 90, 155, 239, 231)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "_private.Lean.Meta.Tactic.Grind.Proof.0.Lean.Meta.Grind.mkProofTo"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Meta.Tactic.Grind.Proof.0.Lean.Meta.Grind.mkProofFrom"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__3_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 77, .m_capacity = 77, .m_length = 76, .m_data = "_private.Lean.Meta.Tactic.Grind.Proof.0.Lean.Meta.Grind.mkCongrProofFunCC.go"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_mkEqProofImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "internal `grind` error, `mkEqProof` invoked with terms of different types"};
static const lean_object* l_Lean_Meta_Grind_mkEqProofImpl___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkEqProofImpl___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkEqProofImpl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkEqProofImpl___closed__1;
static const lean_string_object l_Lean_Meta_Grind_mkEqProofImpl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nhas type"};
static const lean_object* l_Lean_Meta_Grind_mkEqProofImpl___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkEqProofImpl___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkEqProofImpl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkEqProofImpl___closed__3;
static const lean_string_object l_Lean_Meta_Grind_mkEqProofImpl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\nbut"};
static const lean_object* l_Lean_Meta_Grind_mkEqProofImpl___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_mkEqProofImpl___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkEqProofImpl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkEqProofImpl___closed__5;
LEAN_EXPORT lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqProofImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_grind_mk_heq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHEqProofImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof(lean_object* v_h_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_10_; 
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
v___x_10_ = lean_infer_type(v_h_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_);
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v_a_11_; lean_object* v___x_12_; 
v_a_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc(v_a_11_);
lean_dec_ref_known(v___x_10_, 1);
v___x_12_ = l_Lean_Meta_whnfD(v_a_11_, v_a_5_, v_a_6_, v_a_7_, v_a_8_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v_a_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_a_13_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_23_ == 0)
{
v___x_15_ = v___x_12_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_a_13_);
lean_dec(v___x_12_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_17_; uint8_t v___x_18_; lean_object* v___x_19_; lean_object* v___x_21_; 
v___x_17_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_18_ = l_Lean_Expr_isAppOf(v_a_13_, v___x_17_);
lean_dec(v_a_13_);
v___x_19_ = lean_box(v___x_18_);
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_19_);
v___x_21_ = v___x_15_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v___x_19_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
}
else
{
lean_object* v_a_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_31_; 
v_a_24_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_31_ == 0)
{
v___x_26_ = v___x_12_;
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_a_24_);
lean_dec(v___x_12_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_29_; 
if (v_isShared_27_ == 0)
{
v___x_29_ = v___x_26_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_a_24_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
}
else
{
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_39_; 
v_a_32_ = lean_ctor_get(v___x_10_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_39_ == 0)
{
v___x_34_ = v___x_10_;
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_10_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_37_; 
if (v_isShared_35_ == 0)
{
v___x_37_ = v___x_34_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_a_32_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___boxed(lean_object* v_h_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof(v_h_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_);
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(lean_object* v_a_47_, lean_object* v_b_48_){
_start:
{
size_t v___x_49_; size_t v___x_50_; uint8_t v___x_51_; 
v___x_49_ = lean_ptr_addr(v_a_47_);
v___x_50_ = lean_ptr_addr(v_b_48_);
v___x_51_ = lean_usize_dec_eq(v___x_49_, v___x_50_);
if (v___x_51_ == 0)
{
uint8_t v___x_52_; 
v___x_52_ = l_Lean_Expr_isApp(v_a_47_);
if (v___x_52_ == 0)
{
lean_object* v___x_53_; 
lean_dec_ref(v_a_47_);
v___x_53_ = lean_box(0);
return v___x_53_;
}
else
{
uint8_t v___x_54_; 
v___x_54_ = l_Lean_Expr_isApp(v_b_48_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; 
lean_dec_ref(v_a_47_);
v___x_55_ = lean_box(0);
return v___x_55_;
}
else
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = l_Lean_Expr_appFn_x21(v_a_47_);
lean_dec_ref(v_a_47_);
v___x_57_ = l_Lean_Expr_appFn_x21(v_b_48_);
v___x_58_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(v___x_56_, v___x_57_);
lean_dec_ref(v___x_57_);
if (lean_obj_tag(v___x_58_) == 1)
{
lean_object* v_val_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_77_; 
v_val_59_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_77_ == 0)
{
v___x_61_ = v___x_58_;
v_isShared_62_ = v_isSharedCheck_77_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_val_59_);
lean_dec(v___x_58_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_77_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v_fst_63_; lean_object* v_snd_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_76_; 
v_fst_63_ = lean_ctor_get(v_val_59_, 0);
v_snd_64_ = lean_ctor_get(v_val_59_, 1);
v_isSharedCheck_76_ = !lean_is_exclusive(v_val_59_);
if (v_isSharedCheck_76_ == 0)
{
v___x_66_ = v_val_59_;
v_isShared_67_ = v_isSharedCheck_76_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_snd_64_);
lean_inc(v_fst_63_);
lean_dec(v_val_59_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_76_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = lean_nat_add(v_snd_64_, v___x_68_);
lean_dec(v_snd_64_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 1, v___x_69_);
v___x_71_ = v___x_66_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_fst_63_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v___x_69_);
v___x_71_ = v_reuseFailAlloc_75_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
lean_object* v___x_73_; 
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 0, v___x_71_);
v___x_73_ = v___x_61_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
}
else
{
lean_object* v___x_78_; 
lean_dec(v___x_58_);
v___x_78_ = lean_box(0);
return v___x_78_;
}
}
}
}
else
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_80_, 0, v_a_47_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix___boxed(lean_object* v_a_82_, lean_object* v_b_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(v_a_82_, v_b_83_);
lean_dec_ref(v_b_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(lean_object* v_h_85_, uint8_t v_flipped_86_, uint8_t v_heq_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_h_x27_94_; lean_object* v___y_95_; lean_object* v___y_96_; lean_object* v___y_97_; lean_object* v___y_98_; 
if (v_heq_87_ == 0)
{
v_h_x27_94_ = v_h_85_;
v___y_95_ = v_a_88_;
v___y_96_ = v_a_89_;
v___y_97_ = v_a_90_;
v___y_98_ = v_a_91_;
goto v___jp_93_;
}
else
{
lean_object* v___x_102_; 
lean_inc_ref(v_h_85_);
v___x_102_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof(v_h_85_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; uint8_t v___x_104_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_a_103_);
lean_dec_ref_known(v___x_102_, 1);
v___x_104_ = lean_unbox(v_a_103_);
lean_dec(v_a_103_);
if (v___x_104_ == 0)
{
v_h_x27_94_ = v_h_85_;
v___y_95_ = v_a_88_;
v___y_96_ = v_a_89_;
v___y_97_ = v_a_90_;
v___y_98_ = v_a_91_;
goto v___jp_93_;
}
else
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_Meta_mkHEqOfEq(v_h_85_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_a_106_);
lean_dec_ref_known(v___x_105_, 1);
v_h_x27_94_ = v_a_106_;
v___y_95_ = v_a_88_;
v___y_96_ = v_a_89_;
v___y_97_ = v_a_90_;
v___y_98_ = v_a_91_;
goto v___jp_93_;
}
else
{
return v___x_105_;
}
}
}
else
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
lean_dec_ref(v_h_85_);
v_a_107_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v___x_102_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_102_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_107_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
v___jp_93_:
{
if (v_flipped_86_ == 0)
{
lean_object* v___x_99_; 
v___x_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_99_, 0, v_h_x27_94_);
return v___x_99_;
}
else
{
if (v_heq_87_ == 0)
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_Meta_mkEqSymm(v_h_x27_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
return v___x_100_;
}
else
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_Meta_mkHEqSymm(v_h_x27_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
return v___x_101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof___boxed(lean_object* v_h_115_, lean_object* v_flipped_116_, lean_object* v_heq_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
uint8_t v_flipped_boxed_123_; uint8_t v_heq_boxed_124_; lean_object* v_res_125_; 
v_flipped_boxed_123_ = lean_unbox(v_flipped_116_);
v_heq_boxed_124_ = lean_unbox(v_heq_117_);
v_res_125_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(v_h_115_, v_flipped_boxed_123_, v_heq_boxed_124_, v_a_118_, v_a_119_, v_a_120_, v_a_121_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(lean_object* v_a_126_, uint8_t v_heq_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
if (v_heq_127_ == 0)
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Meta_mkEqRefl(v_a_126_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
return v___x_133_;
}
else
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Meta_mkHEqRefl(v_a_126_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl___boxed(lean_object* v_a_135_, lean_object* v_heq_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
uint8_t v_heq_boxed_142_; lean_object* v_res_143_; 
v_heq_boxed_142_ = lean_unbox(v_heq_136_);
v_res_143_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(v_a_135_, v_heq_boxed_142_, v_a_137_, v_a_138_, v_a_139_, v_a_140_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
lean_dec(v_a_138_);
lean_dec_ref(v_a_137_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans(lean_object* v_h_u2081_144_, lean_object* v_h_u2082_145_, uint8_t v_heq_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
if (v_heq_146_ == 0)
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_Meta_mkEqTrans(v_h_u2081_144_, v_h_u2082_145_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
return v___x_152_;
}
else
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_Meta_mkHEqTrans(v_h_u2081_144_, v_h_u2082_145_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans___boxed(lean_object* v_h_u2081_154_, lean_object* v_h_u2082_155_, lean_object* v_heq_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
uint8_t v_heq_boxed_162_; lean_object* v_res_163_; 
v_heq_boxed_162_ = lean_unbox(v_heq_156_);
v_res_163_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans(v_h_u2081_154_, v_h_u2082_155_, v_heq_boxed_162_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(lean_object* v_h_u2081_164_, lean_object* v_h_u2082_165_, uint8_t v_heq_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
if (lean_obj_tag(v_h_u2081_164_) == 1)
{
lean_object* v_val_172_; lean_object* v___x_173_; 
v_val_172_ = lean_ctor_get(v_h_u2081_164_, 0);
lean_inc(v_val_172_);
lean_dec_ref_known(v_h_u2081_164_, 1);
v___x_173_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans(v_val_172_, v_h_u2082_165_, v_heq_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_);
return v___x_173_;
}
else
{
lean_object* v___x_174_; 
lean_dec(v_h_u2081_164_);
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v_h_u2082_165_);
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27___boxed(lean_object* v_h_u2081_175_, lean_object* v_h_u2082_176_, lean_object* v_heq_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
uint8_t v_heq_boxed_183_; lean_object* v_res_184_; 
v_heq_boxed_183_ = lean_unbox(v_heq_177_);
v_res_184_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_h_u2081_175_, v_h_u2082_176_, v_heq_boxed_183_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(lean_object* v_h_185_, uint8_t v_heq_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
if (v_heq_186_ == 0)
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_Meta_mkEqOfHEq(v_h_185_, v_heq_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_);
return v___x_192_;
}
else
{
lean_object* v___x_193_; 
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v_h_185_);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded___boxed(lean_object* v_h_194_, lean_object* v_heq_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
uint8_t v_heq_boxed_201_; lean_object* v_res_202_; 
v_heq_boxed_201_ = lean_unbox(v_heq_195_);
v_res_202_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_h_194_, v_heq_boxed_201_, v_a_196_, v_a_197_, v_a_198_, v_a_199_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
return v_res_202_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0(void){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3(lean_object* v_msg_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_12252__overap_217_; lean_object* v___x_218_; 
v___x_216_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0);
v___x_12252__overap_217_ = lean_panic_fn_borrowed(v___x_216_, v_msg_204_);
lean_inc(v___y_214_);
lean_inc_ref(v___y_213_);
lean_inc(v___y_212_);
lean_inc_ref(v___y_211_);
lean_inc(v___y_210_);
lean_inc_ref(v___y_209_);
lean_inc(v___y_208_);
lean_inc_ref(v___y_207_);
lean_inc(v___y_206_);
lean_inc(v___y_205_);
v___x_218_ = lean_apply_11(v___x_12252__overap_217_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, lean_box(0));
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___boxed(lean_object* v_msg_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3(v_msg_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec(v___y_220_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(lean_object* v_msg_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_13049__overap_245_; lean_object* v___x_246_; 
v___x_244_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0);
v___x_13049__overap_245_ = lean_panic_fn_borrowed(v___x_244_, v_msg_232_);
lean_inc(v___y_242_);
lean_inc_ref(v___y_241_);
lean_inc(v___y_240_);
lean_inc_ref(v___y_239_);
lean_inc(v___y_238_);
lean_inc_ref(v___y_237_);
lean_inc(v___y_236_);
lean_inc_ref(v___y_235_);
lean_inc(v___y_234_);
lean_inc(v___y_233_);
v___x_246_ = lean_apply_11(v___x_13049__overap_245_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, lean_box(0));
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___boxed(lean_object* v_msg_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v_msg_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v___y_249_);
lean_dec(v___y_248_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(lean_object* v_t_260_, lean_object* v_k_261_){
_start:
{
if (lean_obj_tag(v_t_260_) == 0)
{
lean_object* v_k_262_; lean_object* v_v_263_; lean_object* v_l_264_; lean_object* v_r_265_; uint8_t v___x_266_; 
v_k_262_ = lean_ctor_get(v_t_260_, 1);
v_v_263_ = lean_ctor_get(v_t_260_, 2);
v_l_264_ = lean_ctor_get(v_t_260_, 3);
v_r_265_ = lean_ctor_get(v_t_260_, 4);
v___x_266_ = lean_nat_dec_lt(v_k_261_, v_k_262_);
if (v___x_266_ == 0)
{
uint8_t v___x_267_; 
v___x_267_ = lean_nat_dec_eq(v_k_261_, v_k_262_);
if (v___x_267_ == 0)
{
v_t_260_ = v_r_265_;
goto _start;
}
else
{
lean_object* v___x_269_; 
lean_inc(v_v_263_);
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v_v_263_);
return v___x_269_;
}
}
else
{
v_t_260_ = v_l_264_;
goto _start;
}
}
else
{
lean_object* v___x_271_; 
v___x_271_ = lean_box(0);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg___boxed(lean_object* v_t_272_, lean_object* v_k_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(v_t_272_, v_k_273_);
lean_dec(v_k_273_);
lean_dec(v_t_272_);
return v_res_274_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_278_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_279_ = lean_unsigned_to_nat(35u);
v___x_280_ = lean_unsigned_to_nat(87u);
v___x_281_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__1));
v___x_282_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_283_ = l_mkPanicMessageWithDecl(v___x_282_, v___x_281_, v___x_280_, v___x_279_, v___x_278_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(lean_object* v___x_284_, lean_object* v_a_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_snd_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_345_; 
v_snd_297_ = lean_ctor_get(v_a_285_, 1);
v_isSharedCheck_345_ = !lean_is_exclusive(v_a_285_);
if (v_isSharedCheck_345_ == 0)
{
lean_object* v_unused_346_; 
v_unused_346_ = lean_ctor_get(v_a_285_, 0);
lean_dec(v_unused_346_);
v___x_299_ = v_a_285_;
v_isShared_300_ = v_isSharedCheck_345_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_snd_297_);
lean_dec(v_a_285_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_345_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = lean_box(0);
v___x_302_ = lean_st_ref_get(v___y_286_);
lean_inc(v_snd_297_);
v___x_303_ = l_Lean_Meta_Grind_Goal_getENode(v___x_302_, v_snd_297_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___x_302_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_336_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_336_ == 0)
{
v___x_306_ = v___x_303_;
v_isShared_307_ = v_isSharedCheck_336_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_303_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_336_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v_target_x3f_308_; lean_object* v_idx_309_; lean_object* v___x_310_; 
v_target_x3f_308_ = lean_ctor_get(v_a_304_, 4);
lean_inc(v_target_x3f_308_);
v_idx_309_ = lean_ctor_get(v_a_304_, 7);
lean_inc(v_idx_309_);
lean_dec(v_a_304_);
v___x_310_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(v___x_284_, v_idx_309_);
lean_dec(v_idx_309_);
if (lean_obj_tag(v___x_310_) == 1)
{
lean_object* v___x_312_; 
lean_dec(v_target_x3f_308_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_310_);
v___x_312_ = v___x_299_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_snd_297_);
v___x_312_ = v_reuseFailAlloc_316_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_314_; 
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_312_);
v___x_314_ = v___x_306_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
else
{
lean_dec(v___x_310_);
lean_del_object(v___x_306_);
if (lean_obj_tag(v_target_x3f_308_) == 1)
{
lean_object* v_val_317_; lean_object* v___x_319_; 
lean_dec(v_snd_297_);
v_val_317_ = lean_ctor_get(v_target_x3f_308_, 0);
lean_inc(v_val_317_);
lean_dec_ref_known(v_target_x3f_308_, 1);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v_val_317_);
lean_ctor_set(v___x_299_, 0, v___x_301_);
v___x_319_ = v___x_299_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_val_317_);
v___x_319_ = v_reuseFailAlloc_321_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
v_a_285_ = v___x_319_;
goto _start;
}
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec(v_target_x3f_308_);
v___x_322_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3);
v___x_323_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3(v___x_322_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v___x_325_; 
lean_dec_ref_known(v___x_323_, 1);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_301_);
v___x_325_ = v___x_299_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_snd_297_);
v___x_325_ = v_reuseFailAlloc_327_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
v_a_285_ = v___x_325_;
goto _start;
}
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_del_object(v___x_299_);
lean_dec(v_snd_297_);
v_a_328_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_323_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_323_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_del_object(v___x_299_);
lean_dec(v_snd_297_);
v_a_337_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_303_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_303_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___boxed(lean_object* v___x_347_, lean_object* v_a_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(v___x_347_, v_a_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec(v___y_349_);
lean_dec(v___x_347_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(lean_object* v_k_361_, lean_object* v_v_362_, lean_object* v_t_363_){
_start:
{
if (lean_obj_tag(v_t_363_) == 0)
{
lean_object* v_size_364_; lean_object* v_k_365_; lean_object* v_v_366_; lean_object* v_l_367_; lean_object* v_r_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_649_; 
v_size_364_ = lean_ctor_get(v_t_363_, 0);
v_k_365_ = lean_ctor_get(v_t_363_, 1);
v_v_366_ = lean_ctor_get(v_t_363_, 2);
v_l_367_ = lean_ctor_get(v_t_363_, 3);
v_r_368_ = lean_ctor_get(v_t_363_, 4);
v_isSharedCheck_649_ = !lean_is_exclusive(v_t_363_);
if (v_isSharedCheck_649_ == 0)
{
v___x_370_ = v_t_363_;
v_isShared_371_ = v_isSharedCheck_649_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_r_368_);
lean_inc(v_l_367_);
lean_inc(v_v_366_);
lean_inc(v_k_365_);
lean_inc(v_size_364_);
lean_dec(v_t_363_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_649_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
uint8_t v___x_372_; 
v___x_372_ = lean_nat_dec_lt(v_k_361_, v_k_365_);
if (v___x_372_ == 0)
{
uint8_t v___x_373_; 
v___x_373_ = lean_nat_dec_eq(v_k_361_, v_k_365_);
if (v___x_373_ == 0)
{
lean_object* v_impl_374_; lean_object* v___x_375_; 
lean_dec(v_size_364_);
v_impl_374_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_k_361_, v_v_362_, v_r_368_);
v___x_375_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_367_) == 0)
{
lean_object* v_size_376_; lean_object* v_size_377_; lean_object* v_k_378_; lean_object* v_v_379_; lean_object* v_l_380_; lean_object* v_r_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v_size_376_ = lean_ctor_get(v_l_367_, 0);
v_size_377_ = lean_ctor_get(v_impl_374_, 0);
lean_inc(v_size_377_);
v_k_378_ = lean_ctor_get(v_impl_374_, 1);
lean_inc(v_k_378_);
v_v_379_ = lean_ctor_get(v_impl_374_, 2);
lean_inc(v_v_379_);
v_l_380_ = lean_ctor_get(v_impl_374_, 3);
lean_inc(v_l_380_);
v_r_381_ = lean_ctor_get(v_impl_374_, 4);
lean_inc(v_r_381_);
v___x_382_ = lean_unsigned_to_nat(3u);
v___x_383_ = lean_nat_mul(v___x_382_, v_size_376_);
v___x_384_ = lean_nat_dec_lt(v___x_383_, v_size_377_);
lean_dec(v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
lean_dec(v_r_381_);
lean_dec(v_l_380_);
lean_dec(v_v_379_);
lean_dec(v_k_378_);
v___x_385_ = lean_nat_add(v___x_375_, v_size_376_);
v___x_386_ = lean_nat_add(v___x_385_, v_size_377_);
lean_dec(v_size_377_);
lean_dec(v___x_385_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 4, v_impl_374_);
lean_ctor_set(v___x_370_, 0, v___x_386_);
v___x_388_ = v___x_370_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_k_365_);
lean_ctor_set(v_reuseFailAlloc_389_, 2, v_v_366_);
lean_ctor_set(v_reuseFailAlloc_389_, 3, v_l_367_);
lean_ctor_set(v_reuseFailAlloc_389_, 4, v_impl_374_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
else
{
lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_453_; 
v_isSharedCheck_453_ = !lean_is_exclusive(v_impl_374_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; lean_object* v_unused_455_; lean_object* v_unused_456_; lean_object* v_unused_457_; lean_object* v_unused_458_; 
v_unused_454_ = lean_ctor_get(v_impl_374_, 4);
lean_dec(v_unused_454_);
v_unused_455_ = lean_ctor_get(v_impl_374_, 3);
lean_dec(v_unused_455_);
v_unused_456_ = lean_ctor_get(v_impl_374_, 2);
lean_dec(v_unused_456_);
v_unused_457_ = lean_ctor_get(v_impl_374_, 1);
lean_dec(v_unused_457_);
v_unused_458_ = lean_ctor_get(v_impl_374_, 0);
lean_dec(v_unused_458_);
v___x_391_ = v_impl_374_;
v_isShared_392_ = v_isSharedCheck_453_;
goto v_resetjp_390_;
}
else
{
lean_dec(v_impl_374_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_453_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v_size_393_; lean_object* v_k_394_; lean_object* v_v_395_; lean_object* v_l_396_; lean_object* v_r_397_; lean_object* v_size_398_; lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_size_393_ = lean_ctor_get(v_l_380_, 0);
v_k_394_ = lean_ctor_get(v_l_380_, 1);
v_v_395_ = lean_ctor_get(v_l_380_, 2);
v_l_396_ = lean_ctor_get(v_l_380_, 3);
v_r_397_ = lean_ctor_get(v_l_380_, 4);
v_size_398_ = lean_ctor_get(v_r_381_, 0);
v___x_399_ = lean_unsigned_to_nat(2u);
v___x_400_ = lean_nat_mul(v___x_399_, v_size_398_);
v___x_401_ = lean_nat_dec_lt(v_size_393_, v___x_400_);
lean_dec(v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_429_; 
lean_inc(v_r_397_);
lean_inc(v_l_396_);
lean_inc(v_v_395_);
lean_inc(v_k_394_);
v_isSharedCheck_429_ = !lean_is_exclusive(v_l_380_);
if (v_isSharedCheck_429_ == 0)
{
lean_object* v_unused_430_; lean_object* v_unused_431_; lean_object* v_unused_432_; lean_object* v_unused_433_; lean_object* v_unused_434_; 
v_unused_430_ = lean_ctor_get(v_l_380_, 4);
lean_dec(v_unused_430_);
v_unused_431_ = lean_ctor_get(v_l_380_, 3);
lean_dec(v_unused_431_);
v_unused_432_ = lean_ctor_get(v_l_380_, 2);
lean_dec(v_unused_432_);
v_unused_433_ = lean_ctor_get(v_l_380_, 1);
lean_dec(v_unused_433_);
v_unused_434_ = lean_ctor_get(v_l_380_, 0);
lean_dec(v_unused_434_);
v___x_403_ = v_l_380_;
v_isShared_404_ = v_isSharedCheck_429_;
goto v_resetjp_402_;
}
else
{
lean_dec(v_l_380_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_429_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_419_; 
v___x_405_ = lean_nat_add(v___x_375_, v_size_376_);
v___x_406_ = lean_nat_add(v___x_405_, v_size_377_);
lean_dec(v_size_377_);
if (lean_obj_tag(v_l_396_) == 0)
{
lean_object* v_size_427_; 
v_size_427_ = lean_ctor_get(v_l_396_, 0);
lean_inc(v_size_427_);
v___y_419_ = v_size_427_;
goto v___jp_418_;
}
else
{
lean_object* v___x_428_; 
v___x_428_ = lean_unsigned_to_nat(0u);
v___y_419_ = v___x_428_;
goto v___jp_418_;
}
v___jp_407_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_411_ = lean_nat_add(v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec(v___y_409_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 4, v_r_381_);
lean_ctor_set(v___x_403_, 3, v_r_397_);
lean_ctor_set(v___x_403_, 2, v_v_379_);
lean_ctor_set(v___x_403_, 1, v_k_378_);
lean_ctor_set(v___x_403_, 0, v___x_411_);
v___x_413_ = v___x_403_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_411_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_k_378_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_v_379_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v_r_397_);
lean_ctor_set(v_reuseFailAlloc_417_, 4, v_r_381_);
v___x_413_ = v_reuseFailAlloc_417_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_415_; 
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 4, v___x_413_);
lean_ctor_set(v___x_391_, 3, v___y_408_);
lean_ctor_set(v___x_391_, 2, v_v_395_);
lean_ctor_set(v___x_391_, 1, v_k_394_);
lean_ctor_set(v___x_391_, 0, v___x_406_);
v___x_415_ = v___x_391_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_k_394_);
lean_ctor_set(v_reuseFailAlloc_416_, 2, v_v_395_);
lean_ctor_set(v_reuseFailAlloc_416_, 3, v___y_408_);
lean_ctor_set(v_reuseFailAlloc_416_, 4, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
v___jp_418_:
{
lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_420_ = lean_nat_add(v___x_405_, v___y_419_);
lean_dec(v___y_419_);
lean_dec(v___x_405_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 4, v_l_396_);
lean_ctor_set(v___x_370_, 0, v___x_420_);
v___x_422_ = v___x_370_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_k_365_);
lean_ctor_set(v_reuseFailAlloc_426_, 2, v_v_366_);
lean_ctor_set(v_reuseFailAlloc_426_, 3, v_l_367_);
lean_ctor_set(v_reuseFailAlloc_426_, 4, v_l_396_);
v___x_422_ = v_reuseFailAlloc_426_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_423_; 
v___x_423_ = lean_nat_add(v___x_375_, v_size_398_);
if (lean_obj_tag(v_r_397_) == 0)
{
lean_object* v_size_424_; 
v_size_424_ = lean_ctor_get(v_r_397_, 0);
lean_inc(v_size_424_);
v___y_408_ = v___x_422_;
v___y_409_ = v___x_423_;
v___y_410_ = v_size_424_;
goto v___jp_407_;
}
else
{
lean_object* v___x_425_; 
v___x_425_ = lean_unsigned_to_nat(0u);
v___y_408_ = v___x_422_;
v___y_409_ = v___x_423_;
v___y_410_ = v___x_425_;
goto v___jp_407_;
}
}
}
}
}
else
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
lean_del_object(v___x_370_);
v___x_435_ = lean_nat_add(v___x_375_, v_size_376_);
v___x_436_ = lean_nat_add(v___x_435_, v_size_377_);
lean_dec(v_size_377_);
v___x_437_ = lean_nat_add(v___x_435_, v_size_393_);
lean_dec(v___x_435_);
lean_inc_ref(v_l_367_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 4, v_l_380_);
lean_ctor_set(v___x_391_, 3, v_l_367_);
lean_ctor_set(v___x_391_, 2, v_v_366_);
lean_ctor_set(v___x_391_, 1, v_k_365_);
lean_ctor_set(v___x_391_, 0, v___x_437_);
v___x_439_ = v___x_391_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_k_365_);
lean_ctor_set(v_reuseFailAlloc_452_, 2, v_v_366_);
lean_ctor_set(v_reuseFailAlloc_452_, 3, v_l_367_);
lean_ctor_set(v_reuseFailAlloc_452_, 4, v_l_380_);
v___x_439_ = v_reuseFailAlloc_452_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
v_isSharedCheck_446_ = !lean_is_exclusive(v_l_367_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; lean_object* v_unused_448_; lean_object* v_unused_449_; lean_object* v_unused_450_; lean_object* v_unused_451_; 
v_unused_447_ = lean_ctor_get(v_l_367_, 4);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v_l_367_, 3);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_l_367_, 2);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_l_367_, 1);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v_l_367_, 0);
lean_dec(v_unused_451_);
v___x_441_ = v_l_367_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_dec(v_l_367_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 4, v_r_381_);
lean_ctor_set(v___x_441_, 3, v___x_439_);
lean_ctor_set(v___x_441_, 2, v_v_379_);
lean_ctor_set(v___x_441_, 1, v_k_378_);
lean_ctor_set(v___x_441_, 0, v___x_436_);
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_k_378_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v_v_379_);
lean_ctor_set(v_reuseFailAlloc_445_, 3, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_445_, 4, v_r_381_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_459_; 
v_l_459_ = lean_ctor_get(v_impl_374_, 3);
lean_inc(v_l_459_);
if (lean_obj_tag(v_l_459_) == 0)
{
lean_object* v_r_460_; lean_object* v_k_461_; lean_object* v_v_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_485_; 
v_r_460_ = lean_ctor_get(v_impl_374_, 4);
v_k_461_ = lean_ctor_get(v_impl_374_, 1);
v_v_462_ = lean_ctor_get(v_impl_374_, 2);
v_isSharedCheck_485_ = !lean_is_exclusive(v_impl_374_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; lean_object* v_unused_487_; 
v_unused_486_ = lean_ctor_get(v_impl_374_, 3);
lean_dec(v_unused_486_);
v_unused_487_ = lean_ctor_get(v_impl_374_, 0);
lean_dec(v_unused_487_);
v___x_464_ = v_impl_374_;
v_isShared_465_ = v_isSharedCheck_485_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_r_460_);
lean_inc(v_v_462_);
lean_inc(v_k_461_);
lean_dec(v_impl_374_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_485_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v_k_466_; lean_object* v_v_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_481_; 
v_k_466_ = lean_ctor_get(v_l_459_, 1);
v_v_467_ = lean_ctor_get(v_l_459_, 2);
v_isSharedCheck_481_ = !lean_is_exclusive(v_l_459_);
if (v_isSharedCheck_481_ == 0)
{
lean_object* v_unused_482_; lean_object* v_unused_483_; lean_object* v_unused_484_; 
v_unused_482_ = lean_ctor_get(v_l_459_, 4);
lean_dec(v_unused_482_);
v_unused_483_ = lean_ctor_get(v_l_459_, 3);
lean_dec(v_unused_483_);
v_unused_484_ = lean_ctor_get(v_l_459_, 0);
lean_dec(v_unused_484_);
v___x_469_ = v_l_459_;
v_isShared_470_ = v_isSharedCheck_481_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_v_467_);
lean_inc(v_k_466_);
lean_dec(v_l_459_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_481_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_471_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_460_, 2);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v_r_460_);
lean_ctor_set(v___x_469_, 3, v_r_460_);
lean_ctor_set(v___x_469_, 2, v_v_366_);
lean_ctor_set(v___x_469_, 1, v_k_365_);
lean_ctor_set(v___x_469_, 0, v___x_375_);
v___x_473_ = v___x_469_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_k_365_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_v_366_);
lean_ctor_set(v_reuseFailAlloc_480_, 3, v_r_460_);
lean_ctor_set(v_reuseFailAlloc_480_, 4, v_r_460_);
v___x_473_ = v_reuseFailAlloc_480_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_475_; 
lean_inc(v_r_460_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 3, v_r_460_);
lean_ctor_set(v___x_464_, 0, v___x_375_);
v___x_475_ = v___x_464_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_k_461_);
lean_ctor_set(v_reuseFailAlloc_479_, 2, v_v_462_);
lean_ctor_set(v_reuseFailAlloc_479_, 3, v_r_460_);
lean_ctor_set(v_reuseFailAlloc_479_, 4, v_r_460_);
v___x_475_ = v_reuseFailAlloc_479_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_477_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 4, v___x_475_);
lean_ctor_set(v___x_370_, 3, v___x_473_);
lean_ctor_set(v___x_370_, 2, v_v_467_);
lean_ctor_set(v___x_370_, 1, v_k_466_);
lean_ctor_set(v___x_370_, 0, v___x_471_);
v___x_477_ = v___x_370_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_k_466_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v_v_467_);
lean_ctor_set(v_reuseFailAlloc_478_, 3, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_478_, 4, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
}
else
{
lean_object* v_r_488_; 
v_r_488_ = lean_ctor_get(v_impl_374_, 4);
lean_inc(v_r_488_);
if (lean_obj_tag(v_r_488_) == 0)
{
lean_object* v_k_489_; lean_object* v_v_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_501_; 
v_k_489_ = lean_ctor_get(v_impl_374_, 1);
v_v_490_ = lean_ctor_get(v_impl_374_, 2);
v_isSharedCheck_501_ = !lean_is_exclusive(v_impl_374_);
if (v_isSharedCheck_501_ == 0)
{
lean_object* v_unused_502_; lean_object* v_unused_503_; lean_object* v_unused_504_; 
v_unused_502_ = lean_ctor_get(v_impl_374_, 4);
lean_dec(v_unused_502_);
v_unused_503_ = lean_ctor_get(v_impl_374_, 3);
lean_dec(v_unused_503_);
v_unused_504_ = lean_ctor_get(v_impl_374_, 0);
lean_dec(v_unused_504_);
v___x_492_ = v_impl_374_;
v_isShared_493_ = v_isSharedCheck_501_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_v_490_);
lean_inc(v_k_489_);
lean_dec(v_impl_374_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_501_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_494_ = lean_unsigned_to_nat(3u);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 4, v_l_459_);
lean_ctor_set(v___x_492_, 2, v_v_366_);
lean_ctor_set(v___x_492_, 1, v_k_365_);
lean_ctor_set(v___x_492_, 0, v___x_375_);
v___x_496_ = v___x_492_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_k_365_);
lean_ctor_set(v_reuseFailAlloc_500_, 2, v_v_366_);
lean_ctor_set(v_reuseFailAlloc_500_, 3, v_l_459_);
lean_ctor_set(v_reuseFailAlloc_500_, 4, v_l_459_);
v___x_496_ = v_reuseFailAlloc_500_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_498_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 4, v_r_488_);
lean_ctor_set(v___x_370_, 3, v___x_496_);
lean_ctor_set(v___x_370_, 2, v_v_490_);
lean_ctor_set(v___x_370_, 1, v_k_489_);
lean_ctor_set(v___x_370_, 0, v___x_494_);
v___x_498_ = v___x_370_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_k_489_);
lean_ctor_set(v_reuseFailAlloc_499_, 2, v_v_490_);
lean_ctor_set(v_reuseFailAlloc_499_, 3, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_499_, 4, v_r_488_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
else
{
lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_505_ = lean_unsigned_to_nat(2u);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 4, v_impl_374_);
lean_ctor_set(v___x_370_, 3, v_r_488_);
lean_ctor_set(v___x_370_, 0, v___x_505_);
v___x_507_ = v___x_370_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_k_365_);
lean_ctor_set(v_reuseFailAlloc_508_, 2, v_v_366_);
lean_ctor_set(v_reuseFailAlloc_508_, 3, v_r_488_);
lean_ctor_set(v_reuseFailAlloc_508_, 4, v_impl_374_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
else
{
lean_object* v___x_510_; 
lean_dec(v_v_366_);
lean_dec(v_k_365_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 2, v_v_362_);
lean_ctor_set(v___x_370_, 1, v_k_361_);
v___x_510_ = v___x_370_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_size_364_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_k_361_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_v_362_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v_l_367_);
lean_ctor_set(v_reuseFailAlloc_511_, 4, v_r_368_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
else
{
lean_object* v_impl_512_; lean_object* v___x_513_; 
lean_dec(v_size_364_);
v_impl_512_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_k_361_, v_v_362_, v_l_367_);
v___x_513_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_368_) == 0)
{
lean_object* v_size_514_; lean_object* v_size_515_; lean_object* v_k_516_; lean_object* v_v_517_; lean_object* v_l_518_; lean_object* v_r_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v_size_514_ = lean_ctor_get(v_r_368_, 0);
v_size_515_ = lean_ctor_get(v_impl_512_, 0);
lean_inc(v_size_515_);
v_k_516_ = lean_ctor_get(v_impl_512_, 1);
lean_inc(v_k_516_);
v_v_517_ = lean_ctor_get(v_impl_512_, 2);
lean_inc(v_v_517_);
v_l_518_ = lean_ctor_get(v_impl_512_, 3);
lean_inc(v_l_518_);
v_r_519_ = lean_ctor_get(v_impl_512_, 4);
lean_inc(v_r_519_);
v___x_520_ = lean_unsigned_to_nat(3u);
v___x_521_ = lean_nat_mul(v___x_520_, v_size_514_);
v___x_522_ = lean_nat_dec_lt(v___x_521_, v_size_515_);
lean_dec(v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
lean_dec(v_r_519_);
lean_dec(v_l_518_);
lean_dec(v_v_517_);
lean_dec(v_k_516_);
v___x_523_ = lean_nat_add(v___x_513_, v_size_515_);
lean_dec(v_size_515_);
v___x_524_ = lean_nat_add(v___x_523_, v_size_514_);
lean_dec(v___x_523_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 3, v_impl_512_);
lean_ctor_set(v___x_370_, 0, v___x_524_);
v___x_526_ = v___x_370_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_k_365_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_v_366_);
lean_ctor_set(v_reuseFailAlloc_527_, 3, v_impl_512_);
lean_ctor_set(v_reuseFailAlloc_527_, 4, v_r_368_);
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
lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_593_; 
v_isSharedCheck_593_ = !lean_is_exclusive(v_impl_512_);
if (v_isSharedCheck_593_ == 0)
{
lean_object* v_unused_594_; lean_object* v_unused_595_; lean_object* v_unused_596_; lean_object* v_unused_597_; lean_object* v_unused_598_; 
v_unused_594_ = lean_ctor_get(v_impl_512_, 4);
lean_dec(v_unused_594_);
v_unused_595_ = lean_ctor_get(v_impl_512_, 3);
lean_dec(v_unused_595_);
v_unused_596_ = lean_ctor_get(v_impl_512_, 2);
lean_dec(v_unused_596_);
v_unused_597_ = lean_ctor_get(v_impl_512_, 1);
lean_dec(v_unused_597_);
v_unused_598_ = lean_ctor_get(v_impl_512_, 0);
lean_dec(v_unused_598_);
v___x_529_ = v_impl_512_;
v_isShared_530_ = v_isSharedCheck_593_;
goto v_resetjp_528_;
}
else
{
lean_dec(v_impl_512_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_593_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v_size_531_; lean_object* v_size_532_; lean_object* v_k_533_; lean_object* v_v_534_; lean_object* v_l_535_; lean_object* v_r_536_; lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v_size_531_ = lean_ctor_get(v_l_518_, 0);
v_size_532_ = lean_ctor_get(v_r_519_, 0);
v_k_533_ = lean_ctor_get(v_r_519_, 1);
v_v_534_ = lean_ctor_get(v_r_519_, 2);
v_l_535_ = lean_ctor_get(v_r_519_, 3);
v_r_536_ = lean_ctor_get(v_r_519_, 4);
v___x_537_ = lean_unsigned_to_nat(2u);
v___x_538_ = lean_nat_mul(v___x_537_, v_size_531_);
v___x_539_ = lean_nat_dec_lt(v_size_532_, v___x_538_);
lean_dec(v___x_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_568_; 
lean_inc(v_r_536_);
lean_inc(v_l_535_);
lean_inc(v_v_534_);
lean_inc(v_k_533_);
v_isSharedCheck_568_ = !lean_is_exclusive(v_r_519_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; lean_object* v_unused_570_; lean_object* v_unused_571_; lean_object* v_unused_572_; lean_object* v_unused_573_; 
v_unused_569_ = lean_ctor_get(v_r_519_, 4);
lean_dec(v_unused_569_);
v_unused_570_ = lean_ctor_get(v_r_519_, 3);
lean_dec(v_unused_570_);
v_unused_571_ = lean_ctor_get(v_r_519_, 2);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_r_519_, 1);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_r_519_, 0);
lean_dec(v_unused_573_);
v___x_541_ = v_r_519_;
v_isShared_542_ = v_isSharedCheck_568_;
goto v_resetjp_540_;
}
else
{
lean_dec(v_r_519_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_568_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___x_556_; lean_object* v___y_558_; 
v___x_543_ = lean_nat_add(v___x_513_, v_size_515_);
lean_dec(v_size_515_);
v___x_544_ = lean_nat_add(v___x_543_, v_size_514_);
lean_dec(v___x_543_);
v___x_556_ = lean_nat_add(v___x_513_, v_size_531_);
if (lean_obj_tag(v_l_535_) == 0)
{
lean_object* v_size_566_; 
v_size_566_ = lean_ctor_get(v_l_535_, 0);
lean_inc(v_size_566_);
v___y_558_ = v_size_566_;
goto v___jp_557_;
}
else
{
lean_object* v___x_567_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v___y_558_ = v___x_567_;
goto v___jp_557_;
}
v___jp_545_:
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = lean_nat_add(v___y_547_, v___y_548_);
lean_dec(v___y_548_);
lean_dec(v___y_547_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 4, v_r_368_);
lean_ctor_set(v___x_541_, 3, v_r_536_);
lean_ctor_set(v___x_541_, 2, v_v_366_);
lean_ctor_set(v___x_541_, 1, v_k_365_);
lean_ctor_set(v___x_541_, 0, v___x_549_);
v___x_551_ = v___x_541_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_k_365_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_v_366_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v_r_536_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v_r_368_);
v___x_551_ = v_reuseFailAlloc_555_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_553_; 
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 4, v___x_551_);
lean_ctor_set(v___x_529_, 3, v___y_546_);
lean_ctor_set(v___x_529_, 2, v_v_534_);
lean_ctor_set(v___x_529_, 1, v_k_533_);
lean_ctor_set(v___x_529_, 0, v___x_544_);
v___x_553_ = v___x_529_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_k_533_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_v_534_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v___y_546_);
lean_ctor_set(v_reuseFailAlloc_554_, 4, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
v___jp_557_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = lean_nat_add(v___x_556_, v___y_558_);
lean_dec(v___y_558_);
lean_dec(v___x_556_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 4, v_l_535_);
lean_ctor_set(v___x_370_, 3, v_l_518_);
lean_ctor_set(v___x_370_, 2, v_v_517_);
lean_ctor_set(v___x_370_, 1, v_k_516_);
lean_ctor_set(v___x_370_, 0, v___x_559_);
v___x_561_ = v___x_370_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_k_516_);
lean_ctor_set(v_reuseFailAlloc_565_, 2, v_v_517_);
lean_ctor_set(v_reuseFailAlloc_565_, 3, v_l_518_);
lean_ctor_set(v_reuseFailAlloc_565_, 4, v_l_535_);
v___x_561_ = v_reuseFailAlloc_565_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_562_; 
v___x_562_ = lean_nat_add(v___x_513_, v_size_514_);
if (lean_obj_tag(v_r_536_) == 0)
{
lean_object* v_size_563_; 
v_size_563_ = lean_ctor_get(v_r_536_, 0);
lean_inc(v_size_563_);
v___y_546_ = v___x_561_;
v___y_547_ = v___x_562_;
v___y_548_ = v_size_563_;
goto v___jp_545_;
}
else
{
lean_object* v___x_564_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v___y_546_ = v___x_561_;
v___y_547_ = v___x_562_;
v___y_548_ = v___x_564_;
goto v___jp_545_;
}
}
}
}
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
lean_del_object(v___x_370_);
v___x_574_ = lean_nat_add(v___x_513_, v_size_515_);
lean_dec(v_size_515_);
v___x_575_ = lean_nat_add(v___x_574_, v_size_514_);
lean_dec(v___x_574_);
v___x_576_ = lean_nat_add(v___x_513_, v_size_514_);
v___x_577_ = lean_nat_add(v___x_576_, v_size_532_);
lean_dec(v___x_576_);
lean_inc_ref(v_r_368_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 4, v_r_368_);
lean_ctor_set(v___x_529_, 3, v_r_519_);
lean_ctor_set(v___x_529_, 2, v_v_366_);
lean_ctor_set(v___x_529_, 1, v_k_365_);
lean_ctor_set(v___x_529_, 0, v___x_577_);
v___x_579_ = v___x_529_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_k_365_);
lean_ctor_set(v_reuseFailAlloc_592_, 2, v_v_366_);
lean_ctor_set(v_reuseFailAlloc_592_, 3, v_r_519_);
lean_ctor_set(v_reuseFailAlloc_592_, 4, v_r_368_);
v___x_579_ = v_reuseFailAlloc_592_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
v_isSharedCheck_586_ = !lean_is_exclusive(v_r_368_);
if (v_isSharedCheck_586_ == 0)
{
lean_object* v_unused_587_; lean_object* v_unused_588_; lean_object* v_unused_589_; lean_object* v_unused_590_; lean_object* v_unused_591_; 
v_unused_587_ = lean_ctor_get(v_r_368_, 4);
lean_dec(v_unused_587_);
v_unused_588_ = lean_ctor_get(v_r_368_, 3);
lean_dec(v_unused_588_);
v_unused_589_ = lean_ctor_get(v_r_368_, 2);
lean_dec(v_unused_589_);
v_unused_590_ = lean_ctor_get(v_r_368_, 1);
lean_dec(v_unused_590_);
v_unused_591_ = lean_ctor_get(v_r_368_, 0);
lean_dec(v_unused_591_);
v___x_581_ = v_r_368_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_dec(v_r_368_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 4, v___x_579_);
lean_ctor_set(v___x_581_, 3, v_l_518_);
lean_ctor_set(v___x_581_, 2, v_v_517_);
lean_ctor_set(v___x_581_, 1, v_k_516_);
lean_ctor_set(v___x_581_, 0, v___x_575_);
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_k_516_);
lean_ctor_set(v_reuseFailAlloc_585_, 2, v_v_517_);
lean_ctor_set(v_reuseFailAlloc_585_, 3, v_l_518_);
lean_ctor_set(v_reuseFailAlloc_585_, 4, v___x_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_599_; 
v_l_599_ = lean_ctor_get(v_impl_512_, 3);
lean_inc(v_l_599_);
if (lean_obj_tag(v_l_599_) == 0)
{
lean_object* v_r_600_; lean_object* v_k_601_; lean_object* v_v_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_613_; 
v_r_600_ = lean_ctor_get(v_impl_512_, 4);
v_k_601_ = lean_ctor_get(v_impl_512_, 1);
v_v_602_ = lean_ctor_get(v_impl_512_, 2);
v_isSharedCheck_613_ = !lean_is_exclusive(v_impl_512_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; lean_object* v_unused_615_; 
v_unused_614_ = lean_ctor_get(v_impl_512_, 3);
lean_dec(v_unused_614_);
v_unused_615_ = lean_ctor_get(v_impl_512_, 0);
lean_dec(v_unused_615_);
v___x_604_ = v_impl_512_;
v_isShared_605_ = v_isSharedCheck_613_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_r_600_);
lean_inc(v_v_602_);
lean_inc(v_k_601_);
lean_dec(v_impl_512_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_613_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_606_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_600_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 3, v_r_600_);
lean_ctor_set(v___x_604_, 2, v_v_366_);
lean_ctor_set(v___x_604_, 1, v_k_365_);
lean_ctor_set(v___x_604_, 0, v___x_513_);
v___x_608_ = v___x_604_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_k_365_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_v_366_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v_r_600_);
lean_ctor_set(v_reuseFailAlloc_612_, 4, v_r_600_);
v___x_608_ = v_reuseFailAlloc_612_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_610_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 4, v___x_608_);
lean_ctor_set(v___x_370_, 3, v_l_599_);
lean_ctor_set(v___x_370_, 2, v_v_602_);
lean_ctor_set(v___x_370_, 1, v_k_601_);
lean_ctor_set(v___x_370_, 0, v___x_606_);
v___x_610_ = v___x_370_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_k_601_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_v_602_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v_l_599_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
else
{
lean_object* v_r_616_; 
v_r_616_ = lean_ctor_get(v_impl_512_, 4);
lean_inc(v_r_616_);
if (lean_obj_tag(v_r_616_) == 0)
{
lean_object* v_k_617_; lean_object* v_v_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_641_; 
v_k_617_ = lean_ctor_get(v_impl_512_, 1);
v_v_618_ = lean_ctor_get(v_impl_512_, 2);
v_isSharedCheck_641_ = !lean_is_exclusive(v_impl_512_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; lean_object* v_unused_643_; lean_object* v_unused_644_; 
v_unused_642_ = lean_ctor_get(v_impl_512_, 4);
lean_dec(v_unused_642_);
v_unused_643_ = lean_ctor_get(v_impl_512_, 3);
lean_dec(v_unused_643_);
v_unused_644_ = lean_ctor_get(v_impl_512_, 0);
lean_dec(v_unused_644_);
v___x_620_ = v_impl_512_;
v_isShared_621_ = v_isSharedCheck_641_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_v_618_);
lean_inc(v_k_617_);
lean_dec(v_impl_512_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_641_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v_k_622_; lean_object* v_v_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_637_; 
v_k_622_ = lean_ctor_get(v_r_616_, 1);
v_v_623_ = lean_ctor_get(v_r_616_, 2);
v_isSharedCheck_637_ = !lean_is_exclusive(v_r_616_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; lean_object* v_unused_639_; lean_object* v_unused_640_; 
v_unused_638_ = lean_ctor_get(v_r_616_, 4);
lean_dec(v_unused_638_);
v_unused_639_ = lean_ctor_get(v_r_616_, 3);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v_r_616_, 0);
lean_dec(v_unused_640_);
v___x_625_ = v_r_616_;
v_isShared_626_ = v_isSharedCheck_637_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_v_623_);
lean_inc(v_k_622_);
lean_dec(v_r_616_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_637_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_627_ = lean_unsigned_to_nat(3u);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v_l_599_);
lean_ctor_set(v___x_625_, 3, v_l_599_);
lean_ctor_set(v___x_625_, 2, v_v_618_);
lean_ctor_set(v___x_625_, 1, v_k_617_);
lean_ctor_set(v___x_625_, 0, v___x_513_);
v___x_629_ = v___x_625_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_k_617_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_v_618_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_l_599_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v_l_599_);
v___x_629_ = v_reuseFailAlloc_636_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_631_; 
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 4, v_l_599_);
lean_ctor_set(v___x_620_, 2, v_v_366_);
lean_ctor_set(v___x_620_, 1, v_k_365_);
lean_ctor_set(v___x_620_, 0, v___x_513_);
v___x_631_ = v___x_620_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_k_365_);
lean_ctor_set(v_reuseFailAlloc_635_, 2, v_v_366_);
lean_ctor_set(v_reuseFailAlloc_635_, 3, v_l_599_);
lean_ctor_set(v_reuseFailAlloc_635_, 4, v_l_599_);
v___x_631_ = v_reuseFailAlloc_635_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_633_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 4, v___x_631_);
lean_ctor_set(v___x_370_, 3, v___x_629_);
lean_ctor_set(v___x_370_, 2, v_v_623_);
lean_ctor_set(v___x_370_, 1, v_k_622_);
lean_ctor_set(v___x_370_, 0, v___x_627_);
v___x_633_ = v___x_370_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_k_622_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v_v_623_);
lean_ctor_set(v_reuseFailAlloc_634_, 3, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_634_, 4, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
}
else
{
lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_645_ = lean_unsigned_to_nat(2u);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 4, v_r_616_);
lean_ctor_set(v___x_370_, 3, v_impl_512_);
lean_ctor_set(v___x_370_, 0, v___x_645_);
v___x_647_ = v___x_370_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_k_365_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v_v_366_);
lean_ctor_set(v_reuseFailAlloc_648_, 3, v_impl_512_);
lean_ctor_set(v_reuseFailAlloc_648_, 4, v_r_616_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_unsigned_to_nat(1u);
v___x_651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v_k_361_);
lean_ctor_set(v___x_651_, 2, v_v_362_);
lean_ctor_set(v___x_651_, 3, v_t_363_);
lean_ctor_set(v___x_651_, 4, v_t_363_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(lean_object* v_a_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_fst_659_; lean_object* v_snd_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_694_; 
v_fst_659_ = lean_ctor_get(v_a_652_, 0);
v_snd_660_ = lean_ctor_get(v_a_652_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_a_652_);
if (v_isSharedCheck_694_ == 0)
{
v___x_662_ = v_a_652_;
v_isShared_663_ = v_isSharedCheck_694_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_snd_660_);
lean_inc(v_fst_659_);
lean_dec(v_a_652_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_694_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_st_ref_get(v___y_653_);
lean_inc(v_snd_660_);
v___x_665_ = l_Lean_Meta_Grind_Goal_getENode(v___x_664_, v_snd_660_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec(v___x_664_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_685_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_685_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_685_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_685_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v_self_670_; lean_object* v_target_x3f_671_; lean_object* v_idx_672_; lean_object* v___x_673_; 
v_self_670_ = lean_ctor_get(v_a_666_, 0);
lean_inc_ref(v_self_670_);
v_target_x3f_671_ = lean_ctor_get(v_a_666_, 4);
lean_inc(v_target_x3f_671_);
v_idx_672_ = lean_ctor_get(v_a_666_, 7);
lean_inc(v_idx_672_);
lean_dec(v_a_666_);
v___x_673_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_idx_672_, v_self_670_, v_fst_659_);
if (lean_obj_tag(v_target_x3f_671_) == 1)
{
lean_object* v_val_674_; lean_object* v___x_676_; 
lean_del_object(v___x_668_);
lean_dec(v_snd_660_);
v_val_674_ = lean_ctor_get(v_target_x3f_671_, 0);
lean_inc(v_val_674_);
lean_dec_ref_known(v_target_x3f_671_, 1);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 1, v_val_674_);
lean_ctor_set(v___x_662_, 0, v___x_673_);
v___x_676_ = v___x_662_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_val_674_);
v___x_676_ = v_reuseFailAlloc_678_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
v_a_652_ = v___x_676_;
goto _start;
}
}
else
{
lean_object* v___x_680_; 
lean_dec(v_target_x3f_671_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_673_);
v___x_680_ = v___x_662_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_snd_660_);
v___x_680_ = v_reuseFailAlloc_684_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_682_; 
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_680_);
v___x_682_ = v___x_668_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
lean_del_object(v___x_662_);
lean_dec(v_snd_660_);
lean_dec(v_fst_659_);
v_a_686_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_665_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_665_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg___boxed(lean_object* v_a_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(v_a_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
return v_res_702_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_703_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_704_ = lean_unsigned_to_nat(2u);
v___x_705_ = lean_unsigned_to_nat(89u);
v___x_706_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__1));
v___x_707_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_708_ = l_mkPanicMessageWithDecl(v___x_707_, v___x_706_, v___x_705_, v___x_704_, v___x_703_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(lean_object* v_lhs_709_, lean_object* v_rhs_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_visited_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v_visited_722_ = lean_box(1);
v___x_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_723_, 0, v_visited_722_);
lean_ctor_set(v___x_723_, 1, v_lhs_709_);
v___x_724_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(v___x_723_, v_a_711_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v_fst_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_755_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_725_);
lean_dec_ref_known(v___x_724_, 1);
v_fst_726_ = lean_ctor_get(v_a_725_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v_a_725_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; 
v_unused_756_ = lean_ctor_get(v_a_725_, 1);
lean_dec(v_unused_756_);
v___x_728_ = v_a_725_;
v_isShared_729_ = v_isSharedCheck_755_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_fst_726_);
lean_dec(v_a_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_755_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_730_ = lean_box(0);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 1, v_rhs_710_);
lean_ctor_set(v___x_728_, 0, v___x_730_);
v___x_732_ = v___x_728_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_rhs_710_);
v___x_732_ = v_reuseFailAlloc_754_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; 
v___x_733_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(v_fst_726_, v___x_732_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
lean_dec(v_fst_726_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_745_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_745_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_745_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_745_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v_fst_738_; 
v_fst_738_ = lean_ctor_get(v_a_734_, 0);
lean_inc(v_fst_738_);
lean_dec(v_a_734_);
if (lean_obj_tag(v_fst_738_) == 0)
{
lean_object* v___x_739_; lean_object* v___x_740_; 
lean_del_object(v___x_736_);
v___x_739_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0);
v___x_740_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_739_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
return v___x_740_;
}
else
{
lean_object* v_val_741_; lean_object* v___x_743_; 
v_val_741_ = lean_ctor_get(v_fst_738_, 0);
lean_inc(v_val_741_);
lean_dec_ref_known(v_fst_738_, 1);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v_val_741_);
v___x_743_ = v___x_736_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_val_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
v_a_746_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_733_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_733_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec_ref(v_rhs_710_);
v_a_757_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_724_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_724_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___boxed(lean_object* v_lhs_765_, lean_object* v_rhs_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(v_lhs_765_, v_rhs_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_a_768_);
lean_dec(v_a_767_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0(lean_object* v_00_u03b2_779_, lean_object* v_k_780_, lean_object* v_v_781_, lean_object* v_t_782_, lean_object* v_hl_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_k_780_, v_v_781_, v_t_782_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1(lean_object* v_inst_785_, lean_object* v_a_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(v_a_786_, v___y_787_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___boxed(lean_object* v_inst_799_, lean_object* v_a_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1(v_inst_799_, v_a_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec(v___y_801_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2(lean_object* v_00_u03b4_813_, lean_object* v_t_814_, lean_object* v_k_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(v_t_814_, v_k_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___boxed(lean_object* v_00_u03b4_817_, lean_object* v_t_818_, lean_object* v_k_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2(v_00_u03b4_817_, v_t_818_, v_k_819_);
lean_dec(v_k_819_);
lean_dec(v_t_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4(lean_object* v___x_821_, lean_object* v_inst_822_, lean_object* v_a_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(v___x_821_, v_a_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___boxed(lean_object* v___x_836_, lean_object* v_inst_837_, lean_object* v_a_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4(v___x_836_, v_inst_837_, v_a_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec(v___y_839_);
lean_dec(v___x_836_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(lean_object* v_info_851_, lean_object* v_lhs_852_, lean_object* v_rhs_853_, lean_object* v_i_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
uint8_t v___x_866_; 
v___x_866_ = l_Lean_Expr_isApp(v_lhs_852_);
if (v___x_866_ == 0)
{
uint8_t v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
lean_dec(v_i_854_);
lean_dec_ref(v_rhs_853_);
lean_dec_ref(v_lhs_852_);
v___x_867_ = 1;
v___x_868_ = lean_box(v___x_867_);
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
else
{
lean_object* v_a_u2081_870_; lean_object* v_a_u2082_871_; lean_object* v___x_872_; lean_object* v_i_873_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; size_t v___x_888_; size_t v___x_889_; uint8_t v___x_890_; 
v_a_u2081_870_ = l_Lean_Expr_appArg_x21(v_lhs_852_);
v_a_u2082_871_ = l_Lean_Expr_appArg_x21(v_rhs_853_);
v___x_872_ = lean_unsigned_to_nat(1u);
v_i_873_ = lean_nat_sub(v_i_854_, v___x_872_);
lean_dec(v_i_854_);
v___x_888_ = lean_ptr_addr(v_a_u2081_870_);
lean_dec_ref(v_a_u2081_870_);
v___x_889_ = lean_ptr_addr(v_a_u2082_871_);
lean_dec_ref(v_a_u2082_871_);
v___x_890_ = lean_usize_dec_eq(v___x_888_, v___x_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_891_ = lean_array_get_size(v_info_851_);
v___x_892_ = lean_nat_dec_lt(v_i_873_, v___x_891_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; 
lean_dec(v_i_873_);
lean_dec_ref(v_rhs_853_);
lean_dec_ref(v_lhs_852_);
v___x_893_ = lean_box(v___x_892_);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
else
{
lean_object* v___x_895_; uint8_t v_hasFwdDeps_896_; 
v___x_895_ = lean_array_fget_borrowed(v_info_851_, v_i_873_);
v_hasFwdDeps_896_ = lean_ctor_get_uint8(v___x_895_, sizeof(void*)*1 + 1);
if (v_hasFwdDeps_896_ == 0)
{
v___y_875_ = v_a_855_;
v___y_876_ = v_a_856_;
v___y_877_ = v_a_857_;
v___y_878_ = v_a_858_;
v___y_879_ = v_a_859_;
v___y_880_ = v_a_860_;
v___y_881_ = v_a_861_;
v___y_882_ = v_a_862_;
v___y_883_ = v_a_863_;
v___y_884_ = v_a_864_;
goto v___jp_874_;
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; 
lean_dec(v_i_873_);
lean_dec_ref(v_rhs_853_);
lean_dec_ref(v_lhs_852_);
v___x_897_ = lean_box(v___x_890_);
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
return v___x_898_;
}
}
}
else
{
v___y_875_ = v_a_855_;
v___y_876_ = v_a_856_;
v___y_877_ = v_a_857_;
v___y_878_ = v_a_858_;
v___y_879_ = v_a_859_;
v___y_880_ = v_a_860_;
v___y_881_ = v_a_861_;
v___y_882_ = v_a_862_;
v___y_883_ = v_a_863_;
v___y_884_ = v_a_864_;
goto v___jp_874_;
}
v___jp_874_:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = l_Lean_Expr_appFn_x21(v_lhs_852_);
lean_dec_ref(v_lhs_852_);
v___x_886_ = l_Lean_Expr_appFn_x21(v_rhs_853_);
lean_dec_ref(v_rhs_853_);
v_lhs_852_ = v___x_885_;
v_rhs_853_ = v___x_886_;
v_i_854_ = v_i_873_;
v_a_855_ = v___y_875_;
v_a_856_ = v___y_876_;
v_a_857_ = v___y_877_;
v_a_858_ = v___y_878_;
v_a_859_ = v___y_879_;
v_a_860_ = v___y_880_;
v_a_861_ = v___y_881_;
v_a_862_ = v___y_882_;
v_a_863_ = v___y_883_;
v_a_864_ = v___y_884_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop___boxed(lean_object* v_info_899_, lean_object* v_lhs_900_, lean_object* v_rhs_901_, lean_object* v_i_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(v_info_899_, v_lhs_900_, v_rhs_901_, v_i_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec(v_a_903_);
lean_dec_ref(v_info_899_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(lean_object* v_lhs_915_, lean_object* v_rhs_916_, lean_object* v_f_917_, lean_object* v_g_918_, lean_object* v_numArgs_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
size_t v___x_931_; size_t v___x_932_; uint8_t v___x_933_; 
v___x_931_ = lean_ptr_addr(v_f_917_);
v___x_932_ = lean_ptr_addr(v_g_918_);
v___x_933_ = lean_usize_dec_eq(v___x_931_, v___x_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec(v_numArgs_919_);
lean_dec_ref(v_f_917_);
lean_dec_ref(v_rhs_916_);
lean_dec_ref(v_lhs_915_);
v___x_934_ = lean_box(v___x_933_);
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
return v___x_935_;
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = lean_box(0);
v___x_937_ = l_Lean_Meta_getFunInfo(v_f_917_, v___x_936_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v_paramInfo_939_; lean_object* v___x_940_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
lean_dec_ref_known(v___x_937_, 1);
v_paramInfo_939_ = lean_ctor_get(v_a_938_, 0);
lean_inc_ref(v_paramInfo_939_);
lean_dec(v_a_938_);
v___x_940_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(v_paramInfo_939_, v_lhs_915_, v_rhs_916_, v_numArgs_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
lean_dec_ref(v_paramInfo_939_);
return v___x_940_;
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec(v_numArgs_919_);
lean_dec_ref(v_rhs_916_);
lean_dec_ref(v_lhs_915_);
v_a_941_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_937_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_937_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget___boxed(lean_object* v_lhs_949_, lean_object* v_rhs_950_, lean_object* v_f_951_, lean_object* v_g_952_, lean_object* v_numArgs_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(v_lhs_949_, v_rhs_950_, v_f_951_, v_g_952_, v_numArgs_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_g_952_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(lean_object* v_msg_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; lean_object* v___x_95198__overap_979_; lean_object* v___x_980_; 
v___x_978_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0);
v___x_95198__overap_979_ = lean_panic_fn_borrowed(v___x_978_, v_msg_966_);
lean_inc(v___y_976_);
lean_inc_ref(v___y_975_);
lean_inc(v___y_974_);
lean_inc_ref(v___y_973_);
lean_inc(v___y_972_);
lean_inc_ref(v___y_971_);
lean_inc(v___y_970_);
lean_inc_ref(v___y_969_);
lean_inc(v___y_968_);
lean_inc(v___y_967_);
v___x_980_ = lean_apply_11(v___x_95198__overap_979_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, lean_box(0));
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___boxed(lean_object* v_msg_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v_msg_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec(v___y_982_);
return v_res_993_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = l_Lean_maxRecDepthErrorMessage;
v___x_1000_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3);
v___x_1002_ = l_Lean_MessageData_ofFormat(v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4);
v___x_1004_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__2));
v___x_1005_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v___x_1003_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(lean_object* v_ref_1006_){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5);
v___x_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1009_, 0, v_ref_1006_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___boxed(lean_object* v_ref_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1011_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0(lean_object* v_k_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v_b_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___x_1027_; 
lean_inc(v___y_1025_);
lean_inc_ref(v___y_1024_);
lean_inc(v___y_1023_);
lean_inc_ref(v___y_1022_);
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
lean_inc(v___y_1016_);
lean_inc(v___y_1015_);
v___x_1027_ = lean_apply_12(v_k_1014_, v_b_1021_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, lean_box(0));
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0___boxed(lean_object* v_k_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v_b_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0(v_k_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v_b_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec(v___y_1029_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(lean_object* v_name_1042_, uint8_t v_bi_1043_, lean_object* v_type_1044_, lean_object* v_k_1045_, uint8_t v_kind_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v___f_1058_; lean_object* v___x_1059_; 
lean_inc(v___y_1052_);
lean_inc_ref(v___y_1051_);
lean_inc(v___y_1050_);
lean_inc_ref(v___y_1049_);
lean_inc(v___y_1048_);
lean_inc(v___y_1047_);
v___f_1058_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_1058_, 0, v_k_1045_);
lean_closure_set(v___f_1058_, 1, v___y_1047_);
lean_closure_set(v___f_1058_, 2, v___y_1048_);
lean_closure_set(v___f_1058_, 3, v___y_1049_);
lean_closure_set(v___f_1058_, 4, v___y_1050_);
lean_closure_set(v___f_1058_, 5, v___y_1051_);
lean_closure_set(v___f_1058_, 6, v___y_1052_);
v___x_1059_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1042_, v_bi_1043_, v_type_1044_, v___f_1058_, v_kind_1046_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1059_) == 0)
{
return v___x_1059_;
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1059_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___boxed(lean_object* v_name_1068_, lean_object* v_bi_1069_, lean_object* v_type_1070_, lean_object* v_k_1071_, lean_object* v_kind_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
uint8_t v_bi_boxed_1084_; uint8_t v_kind_boxed_1085_; lean_object* v_res_1086_; 
v_bi_boxed_1084_ = lean_unbox(v_bi_1069_);
v_kind_boxed_1085_ = lean_unbox(v_kind_1072_);
v_res_1086_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_1068_, v_bi_boxed_1084_, v_type_1070_, v_k_1071_, v_kind_boxed_1085_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec(v___y_1073_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(lean_object* v_name_1087_, lean_object* v_type_1088_, lean_object* v_k_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
uint8_t v___x_1101_; uint8_t v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = 0;
v___x_1102_ = 0;
v___x_1103_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_1087_, v___x_1101_, v_type_1088_, v_k_1089_, v___x_1102_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg___boxed(lean_object* v_name_1104_, lean_object* v_type_1105_, lean_object* v_k_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_name_1104_, v_type_1105_, v_k_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec(v___y_1107_);
return v_res_1118_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1119_; lean_object* v_dummy_1120_; 
v___x_1119_ = lean_box(0);
v_dummy_1120_ = l_Lean_Expr_sort___override(v___x_1119_);
return v_dummy_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0(lean_object* v_numArgs_1121_, lean_object* v_rhs_1122_, lean_object* v_lhs_1123_, uint8_t v___x_1124_, uint8_t v___x_1125_, lean_object* v_x_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_dummy_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_dummy_1138_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0);
lean_inc(v_numArgs_1121_);
v___x_1139_ = lean_mk_array(v_numArgs_1121_, v_dummy_1138_);
v___x_1140_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_numArgs_1121_, v_rhs_1122_, v___x_1139_);
lean_inc_ref(v_x_1126_);
v___x_1141_ = l_Lean_mkAppN(v_x_1126_, v___x_1140_);
lean_dec_ref(v___x_1140_);
v___x_1142_ = l_Lean_Meta_mkHEq(v_lhs_1123_, v___x_1141_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; lean_object* v___x_1148_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1142_, 1);
v___x_1144_ = lean_unsigned_to_nat(1u);
v___x_1145_ = lean_mk_empty_array_with_capacity(v___x_1144_);
v___x_1146_ = lean_array_push(v___x_1145_, v_x_1126_);
v___x_1147_ = 1;
v___x_1148_ = l_Lean_Meta_mkLambdaFVars(v___x_1146_, v_a_1143_, v___x_1124_, v___x_1125_, v___x_1124_, v___x_1125_, v___x_1147_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec_ref(v___x_1146_);
return v___x_1148_;
}
else
{
lean_dec_ref(v_x_1126_);
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___boxed(lean_object** _args){
lean_object* v_numArgs_1149_ = _args[0];
lean_object* v_rhs_1150_ = _args[1];
lean_object* v_lhs_1151_ = _args[2];
lean_object* v___x_1152_ = _args[3];
lean_object* v___x_1153_ = _args[4];
lean_object* v_x_1154_ = _args[5];
lean_object* v___y_1155_ = _args[6];
lean_object* v___y_1156_ = _args[7];
lean_object* v___y_1157_ = _args[8];
lean_object* v___y_1158_ = _args[9];
lean_object* v___y_1159_ = _args[10];
lean_object* v___y_1160_ = _args[11];
lean_object* v___y_1161_ = _args[12];
lean_object* v___y_1162_ = _args[13];
lean_object* v___y_1163_ = _args[14];
lean_object* v___y_1164_ = _args[15];
lean_object* v___y_1165_ = _args[16];
_start:
{
uint8_t v___x_102938__boxed_1166_; uint8_t v___x_102939__boxed_1167_; lean_object* v_res_1168_; 
v___x_102938__boxed_1166_ = lean_unbox(v___x_1152_);
v___x_102939__boxed_1167_ = lean_unbox(v___x_1153_);
v_res_1168_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0(v_numArgs_1149_, v_rhs_1150_, v_lhs_1151_, v___x_102938__boxed_1166_, v___x_102939__boxed_1167_, v_x_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec(v___y_1155_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_spec__13(lean_object* v_msg_1169_){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = l_Lean_instInhabitedExpr;
v___x_1171_ = lean_panic_fn_borrowed(v___x_1170_, v_msg_1169_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(lean_object* v_msgData_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; lean_object* v_env_1179_; lean_object* v___x_1180_; lean_object* v_toCold_1181_; lean_object* v_mctx_1182_; lean_object* v_lctx_1183_; lean_object* v_options_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1178_ = lean_st_ref_get(v___y_1176_);
v_env_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc_ref(v_env_1179_);
lean_dec(v___x_1178_);
v___x_1180_ = lean_st_ref_get(v___y_1174_);
v_toCold_1181_ = lean_ctor_get(v___y_1175_, 0);
v_mctx_1182_ = lean_ctor_get(v___x_1180_, 0);
lean_inc_ref(v_mctx_1182_);
lean_dec(v___x_1180_);
v_lctx_1183_ = lean_ctor_get(v___y_1173_, 2);
v_options_1184_ = lean_ctor_get(v_toCold_1181_, 2);
lean_inc_ref(v_options_1184_);
lean_inc_ref(v_lctx_1183_);
v___x_1185_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1185_, 0, v_env_1179_);
lean_ctor_set(v___x_1185_, 1, v_mctx_1182_);
lean_ctor_set(v___x_1185_, 2, v_lctx_1183_);
lean_ctor_set(v___x_1185_, 3, v_options_1184_);
v___x_1186_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
lean_ctor_set(v___x_1186_, 1, v_msgData_1172_);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16___boxed(lean_object* v_msgData_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(v_msgData_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(lean_object* v_msg_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_ref_1201_; lean_object* v___x_1202_; lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1211_; 
v_ref_1201_ = lean_ctor_get(v___y_1198_, 2);
v___x_1202_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(v_msg_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1205_ = v___x_1202_;
v_isShared_1206_ = v_isSharedCheck_1211_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1211_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
lean_inc(v_ref_1201_);
v___x_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1207_, 0, v_ref_1201_);
lean_ctor_set(v___x_1207_, 1, v_a_1203_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set_tag(v___x_1205_, 1);
lean_ctor_set(v___x_1205_, 0, v___x_1207_);
v___x_1209_ = v___x_1205_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg___boxed(lean_object* v_msg_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v_msg_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
return v_res_1218_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__0));
v___x_1221_ = l_Lean_stringToMessageData(v___x_1220_);
return v___x_1221_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__2));
v___x_1224_ = l_Lean_stringToMessageData(v___x_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(lean_object* v_lhs_1225_, lean_object* v_rhs_1226_, lean_object* v_00_u03b1_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1239_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1);
v___x_1240_ = l_Lean_indentExpr(v_lhs_1225_);
v___x_1241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3);
v___x_1243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1241_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = l_Lean_indentExpr(v_rhs_1226_);
v___x_1245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1243_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
v___x_1246_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v___x_1245_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___boxed(lean_object* v_lhs_1247_, lean_object* v_rhs_1248_, lean_object* v_00_u03b1_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1247_, v_rhs_1248_, v_00_u03b1_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec(v___y_1250_);
return v_res_1261_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2(void){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1264_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__1));
v___x_1265_ = lean_unsigned_to_nat(4u);
v___x_1266_ = lean_unsigned_to_nat(198u);
v___x_1267_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__0));
v___x_1268_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1269_ = l_mkPanicMessageWithDecl(v___x_1268_, v___x_1267_, v___x_1266_, v___x_1265_, v___x_1264_);
return v___x_1269_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__1));
v___x_1273_ = lean_unsigned_to_nat(4u);
v___x_1274_ = lean_unsigned_to_nat(318u);
v___x_1275_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0));
v___x_1276_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1277_ = l_mkPanicMessageWithDecl(v___x_1276_, v___x_1275_, v___x_1274_, v___x_1273_, v___x_1272_);
return v___x_1277_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1279_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1280_ = lean_unsigned_to_nat(36u);
v___x_1281_ = lean_unsigned_to_nat(153u);
v___x_1282_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0));
v___x_1283_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1284_ = l_mkPanicMessageWithDecl(v___x_1283_, v___x_1282_, v___x_1281_, v___x_1280_, v___x_1279_);
return v___x_1284_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1285_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1286_ = lean_unsigned_to_nat(34u);
v___x_1287_ = lean_unsigned_to_nat(154u);
v___x_1288_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0));
v___x_1289_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1290_ = l_mkPanicMessageWithDecl(v___x_1289_, v___x_1288_, v___x_1287_, v___x_1286_, v___x_1285_);
return v___x_1290_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1292_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__3));
v___x_1293_ = lean_unsigned_to_nat(4u);
v___x_1294_ = lean_unsigned_to_nat(155u);
v___x_1295_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0));
v___x_1296_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1297_ = l_mkPanicMessageWithDecl(v___x_1296_, v___x_1295_, v___x_1294_, v___x_1293_, v___x_1292_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof(lean_object* v_lhs_1310_, lean_object* v_rhs_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_){
_start:
{
lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; uint8_t v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; uint8_t v___y_1359_; lean_object* v_toCold_1395_; lean_object* v_currRecDepth_1396_; lean_object* v_ref_1397_; uint8_t v_diag_1398_; uint8_t v_suppressElabErrors_1399_; lean_object* v_maxRecDepth_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v_toCold_1395_ = lean_ctor_get(v_a_1320_, 0);
v_currRecDepth_1396_ = lean_ctor_get(v_a_1320_, 1);
v_ref_1397_ = lean_ctor_get(v_a_1320_, 2);
v_diag_1398_ = lean_ctor_get_uint8(v_a_1320_, sizeof(void*)*3);
v_suppressElabErrors_1399_ = lean_ctor_get_uint8(v_a_1320_, sizeof(void*)*3 + 1);
v_maxRecDepth_1400_ = lean_ctor_get(v_toCold_1395_, 3);
v___x_1401_ = l_Lean_Expr_cleanupAnnotations(v_lhs_1310_);
v___x_1402_ = l_Lean_Expr_isApp(v___x_1401_);
v___x_1432_ = lean_unsigned_to_nat(0u);
v___x_1433_ = lean_nat_dec_eq(v_maxRecDepth_1400_, v___x_1432_);
if (v___x_1433_ == 0)
{
uint8_t v___x_1434_; 
v___x_1434_ = lean_nat_dec_eq(v_currRecDepth_1396_, v_maxRecDepth_1400_);
if (v___x_1434_ == 0)
{
goto v___jp_1403_;
}
else
{
lean_object* v___x_1435_; 
lean_dec_ref(v___x_1401_);
lean_dec_ref(v_rhs_1311_);
lean_inc(v_ref_1397_);
v___x_1435_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1397_);
return v___x_1435_;
}
}
else
{
goto v___jp_1403_;
}
v___jp_1323_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1);
v___x_1335_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1334_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec_ref(v___y_1332_);
return v___x_1335_;
}
v___jp_1336_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2);
v___x_1348_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1347_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec_ref(v___y_1345_);
return v___x_1348_;
}
v___jp_1349_:
{
if (v___y_1359_ == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_dec_ref(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1352_);
lean_dec_ref(v___y_1350_);
v___x_1360_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4);
v___x_1361_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1360_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v___y_1351_, v_a_1321_);
lean_dec_ref(v___y_1351_);
return v___x_1361_;
}
else
{
lean_object* v___x_1362_; size_t v___x_1363_; size_t v___x_1364_; uint8_t v___x_1365_; 
v___x_1362_ = l_Lean_Expr_constLevels_x21(v___y_1350_);
lean_dec_ref(v___y_1350_);
v___x_1363_ = lean_ptr_addr(v___y_1358_);
v___x_1364_ = lean_ptr_addr(v___y_1355_);
v___x_1365_ = lean_usize_dec_eq(v___x_1363_, v___x_1364_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; 
lean_inc_ref(v___y_1356_);
lean_inc_ref(v___y_1357_);
v___x_1366_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1357_, v___y_1356_, v___y_1353_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v___y_1351_, v_a_1321_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1368_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___x_1366_, 1);
lean_inc_ref(v___y_1352_);
lean_inc_ref(v___y_1354_);
v___x_1368_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1354_, v___y_1352_, v___y_1353_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v___y_1351_, v_a_1321_);
lean_dec_ref(v___y_1351_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1379_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1379_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1379_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1373_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6));
v___x_1374_ = l_Lean_mkConst(v___x_1373_, v___x_1362_);
v___x_1375_ = l_Lean_mkApp8(v___x_1374_, v___y_1358_, v___y_1355_, v___y_1357_, v___y_1354_, v___y_1352_, v___y_1356_, v_a_1367_, v_a_1369_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1375_);
v___x_1377_ = v___x_1371_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
else
{
lean_dec(v_a_1367_);
lean_dec(v___x_1362_);
lean_dec_ref(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1352_);
return v___x_1368_;
}
}
else
{
lean_dec(v___x_1362_);
lean_dec_ref(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1352_);
lean_dec_ref(v___y_1351_);
return v___x_1366_;
}
}
else
{
uint8_t v___x_1380_; lean_object* v___x_1381_; 
lean_dec_ref(v___y_1355_);
v___x_1380_ = 0;
lean_inc_ref(v___y_1356_);
lean_inc_ref(v___y_1357_);
v___x_1381_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1357_, v___y_1356_, v___x_1380_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v___y_1351_, v_a_1321_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1383_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
lean_inc_ref(v___y_1352_);
lean_inc_ref(v___y_1354_);
v___x_1383_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1354_, v___y_1352_, v___x_1380_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v___y_1351_, v_a_1321_);
lean_dec_ref(v___y_1351_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1394_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1386_ = v___x_1383_;
v_isShared_1387_ = v_isSharedCheck_1394_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1394_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1388_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8));
v___x_1389_ = l_Lean_mkConst(v___x_1388_, v___x_1362_);
v___x_1390_ = l_Lean_mkApp7(v___x_1389_, v___y_1358_, v___y_1357_, v___y_1354_, v___y_1352_, v___y_1356_, v_a_1382_, v_a_1384_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1390_);
v___x_1392_ = v___x_1386_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
else
{
lean_dec(v_a_1382_);
lean_dec(v___x_1362_);
lean_dec_ref(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1352_);
return v___x_1383_;
}
}
else
{
lean_dec(v___x_1362_);
lean_dec_ref(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1352_);
lean_dec_ref(v___y_1351_);
return v___x_1381_;
}
}
}
}
v___jp_1403_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1404_ = lean_unsigned_to_nat(1u);
v___x_1405_ = lean_nat_add(v_currRecDepth_1396_, v___x_1404_);
lean_inc(v_ref_1397_);
lean_inc_ref(v_toCold_1395_);
v___x_1406_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1406_, 0, v_toCold_1395_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
lean_ctor_set(v___x_1406_, 2, v_ref_1397_);
lean_ctor_set_uint8(v___x_1406_, sizeof(void*)*3, v_diag_1398_);
lean_ctor_set_uint8(v___x_1406_, sizeof(void*)*3 + 1, v_suppressElabErrors_1399_);
if (v___x_1402_ == 0)
{
lean_dec_ref(v___x_1401_);
lean_dec_ref(v_rhs_1311_);
v___y_1324_ = v_a_1312_;
v___y_1325_ = v_a_1313_;
v___y_1326_ = v_a_1314_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v_a_1316_;
v___y_1329_ = v_a_1317_;
v___y_1330_ = v_a_1318_;
v___y_1331_ = v_a_1319_;
v___y_1332_ = v___x_1406_;
v___y_1333_ = v_a_1321_;
goto v___jp_1323_;
}
else
{
lean_object* v_arg_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v_arg_1407_ = lean_ctor_get(v___x_1401_, 1);
lean_inc_ref(v_arg_1407_);
v___x_1408_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1401_);
v___x_1409_ = l_Lean_Expr_isApp(v___x_1408_);
if (v___x_1409_ == 0)
{
lean_dec_ref(v___x_1408_);
lean_dec_ref(v_arg_1407_);
lean_dec_ref(v_rhs_1311_);
v___y_1324_ = v_a_1312_;
v___y_1325_ = v_a_1313_;
v___y_1326_ = v_a_1314_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v_a_1316_;
v___y_1329_ = v_a_1317_;
v___y_1330_ = v_a_1318_;
v___y_1331_ = v_a_1319_;
v___y_1332_ = v___x_1406_;
v___y_1333_ = v_a_1321_;
goto v___jp_1323_;
}
else
{
lean_object* v_arg_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v_arg_1410_ = lean_ctor_get(v___x_1408_, 1);
lean_inc_ref(v_arg_1410_);
v___x_1411_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1408_);
v___x_1412_ = l_Lean_Expr_isApp(v___x_1411_);
if (v___x_1412_ == 0)
{
lean_dec_ref(v___x_1411_);
lean_dec_ref(v_arg_1410_);
lean_dec_ref(v_arg_1407_);
lean_dec_ref(v_rhs_1311_);
v___y_1324_ = v_a_1312_;
v___y_1325_ = v_a_1313_;
v___y_1326_ = v_a_1314_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v_a_1316_;
v___y_1329_ = v_a_1317_;
v___y_1330_ = v_a_1318_;
v___y_1331_ = v_a_1319_;
v___y_1332_ = v___x_1406_;
v___y_1333_ = v_a_1321_;
goto v___jp_1323_;
}
else
{
lean_object* v_arg_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; 
v_arg_1413_ = lean_ctor_get(v___x_1411_, 1);
lean_inc_ref(v_arg_1413_);
v___x_1414_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1411_);
v___x_1415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_1416_ = l_Lean_Expr_isConstOf(v___x_1414_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_dec_ref(v___x_1414_);
lean_dec_ref(v_arg_1413_);
lean_dec_ref(v_arg_1410_);
lean_dec_ref(v_arg_1407_);
lean_dec_ref(v_rhs_1311_);
v___y_1324_ = v_a_1312_;
v___y_1325_ = v_a_1313_;
v___y_1326_ = v_a_1314_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v_a_1316_;
v___y_1329_ = v_a_1317_;
v___y_1330_ = v_a_1318_;
v___y_1331_ = v_a_1319_;
v___y_1332_ = v___x_1406_;
v___y_1333_ = v_a_1321_;
goto v___jp_1323_;
}
else
{
lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1417_ = l_Lean_Expr_cleanupAnnotations(v_rhs_1311_);
v___x_1418_ = l_Lean_Expr_isApp(v___x_1417_);
if (v___x_1418_ == 0)
{
lean_dec_ref(v___x_1417_);
lean_dec_ref(v___x_1414_);
lean_dec_ref(v_arg_1413_);
lean_dec_ref(v_arg_1410_);
lean_dec_ref(v_arg_1407_);
v___y_1337_ = v_a_1312_;
v___y_1338_ = v_a_1313_;
v___y_1339_ = v_a_1314_;
v___y_1340_ = v_a_1315_;
v___y_1341_ = v_a_1316_;
v___y_1342_ = v_a_1317_;
v___y_1343_ = v_a_1318_;
v___y_1344_ = v_a_1319_;
v___y_1345_ = v___x_1406_;
v___y_1346_ = v_a_1321_;
goto v___jp_1336_;
}
else
{
lean_object* v_arg_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v_arg_1419_ = lean_ctor_get(v___x_1417_, 1);
lean_inc_ref(v_arg_1419_);
v___x_1420_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1417_);
v___x_1421_ = l_Lean_Expr_isApp(v___x_1420_);
if (v___x_1421_ == 0)
{
lean_dec_ref(v___x_1420_);
lean_dec_ref(v_arg_1419_);
lean_dec_ref(v___x_1414_);
lean_dec_ref(v_arg_1413_);
lean_dec_ref(v_arg_1410_);
lean_dec_ref(v_arg_1407_);
v___y_1337_ = v_a_1312_;
v___y_1338_ = v_a_1313_;
v___y_1339_ = v_a_1314_;
v___y_1340_ = v_a_1315_;
v___y_1341_ = v_a_1316_;
v___y_1342_ = v_a_1317_;
v___y_1343_ = v_a_1318_;
v___y_1344_ = v_a_1319_;
v___y_1345_ = v___x_1406_;
v___y_1346_ = v_a_1321_;
goto v___jp_1336_;
}
else
{
lean_object* v_arg_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v_arg_1422_ = lean_ctor_get(v___x_1420_, 1);
lean_inc_ref(v_arg_1422_);
v___x_1423_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1420_);
v___x_1424_ = l_Lean_Expr_isApp(v___x_1423_);
if (v___x_1424_ == 0)
{
lean_dec_ref(v___x_1423_);
lean_dec_ref(v_arg_1422_);
lean_dec_ref(v_arg_1419_);
lean_dec_ref(v___x_1414_);
lean_dec_ref(v_arg_1413_);
lean_dec_ref(v_arg_1410_);
lean_dec_ref(v_arg_1407_);
v___y_1337_ = v_a_1312_;
v___y_1338_ = v_a_1313_;
v___y_1339_ = v_a_1314_;
v___y_1340_ = v_a_1315_;
v___y_1341_ = v_a_1316_;
v___y_1342_ = v_a_1317_;
v___y_1343_ = v_a_1318_;
v___y_1344_ = v_a_1319_;
v___y_1345_ = v___x_1406_;
v___y_1346_ = v_a_1321_;
goto v___jp_1336_;
}
else
{
lean_object* v_arg_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v_arg_1425_ = lean_ctor_get(v___x_1423_, 1);
lean_inc_ref(v_arg_1425_);
v___x_1426_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1423_);
v___x_1427_ = l_Lean_Expr_isConstOf(v___x_1426_, v___x_1415_);
lean_dec_ref(v___x_1426_);
if (v___x_1427_ == 0)
{
lean_dec_ref(v_arg_1425_);
lean_dec_ref(v_arg_1422_);
lean_dec_ref(v_arg_1419_);
lean_dec_ref(v___x_1414_);
lean_dec_ref(v_arg_1413_);
lean_dec_ref(v_arg_1410_);
lean_dec_ref(v_arg_1407_);
v___y_1337_ = v_a_1312_;
v___y_1338_ = v_a_1313_;
v___y_1339_ = v_a_1314_;
v___y_1340_ = v_a_1315_;
v___y_1341_ = v_a_1316_;
v___y_1342_ = v_a_1317_;
v___y_1343_ = v_a_1318_;
v___y_1344_ = v_a_1319_;
v___y_1345_ = v___x_1406_;
v___y_1346_ = v_a_1321_;
goto v___jp_1336_;
}
else
{
lean_object* v___x_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1428_ = lean_st_ref_get(v_a_1312_);
v___x_1429_ = lean_st_ref_get(v_a_1312_);
v___x_1430_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1428_, v_arg_1410_, v_arg_1419_);
lean_dec(v___x_1428_);
if (v___x_1430_ == 0)
{
lean_dec(v___x_1429_);
v___y_1350_ = v___x_1414_;
v___y_1351_ = v___x_1406_;
v___y_1352_ = v_arg_1422_;
v___y_1353_ = v___x_1427_;
v___y_1354_ = v_arg_1407_;
v___y_1355_ = v_arg_1425_;
v___y_1356_ = v_arg_1419_;
v___y_1357_ = v_arg_1410_;
v___y_1358_ = v_arg_1413_;
v___y_1359_ = v___x_1430_;
goto v___jp_1349_;
}
else
{
uint8_t v___x_1431_; 
v___x_1431_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1429_, v_arg_1407_, v_arg_1422_);
lean_dec(v___x_1429_);
v___y_1350_ = v___x_1414_;
v___y_1351_ = v___x_1406_;
v___y_1352_ = v_arg_1422_;
v___y_1353_ = v___x_1427_;
v___y_1354_ = v_arg_1407_;
v___y_1355_ = v_arg_1425_;
v___y_1356_ = v_arg_1419_;
v___y_1357_ = v_arg_1410_;
v___y_1358_ = v_arg_1413_;
v___y_1359_ = v___x_1431_;
goto v___jp_1349_;
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3(void){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1440_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1441_ = lean_unsigned_to_nat(38u);
v___x_1442_ = lean_unsigned_to_nat(250u);
v___x_1443_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2));
v___x_1444_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1445_ = l_mkPanicMessageWithDecl(v___x_1444_, v___x_1443_, v___x_1442_, v___x_1441_, v___x_1440_);
return v___x_1445_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1447_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4));
v___x_1448_ = lean_unsigned_to_nat(6u);
v___x_1449_ = lean_unsigned_to_nat(260u);
v___x_1450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2));
v___x_1451_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1452_ = l_mkPanicMessageWithDecl(v___x_1451_, v___x_1450_, v___x_1449_, v___x_1448_, v___x_1447_);
return v___x_1452_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2(void){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1455_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__1));
v___x_1456_ = lean_unsigned_to_nat(4u);
v___x_1457_ = lean_unsigned_to_nat(219u);
v___x_1458_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__0));
v___x_1459_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1460_ = l_mkPanicMessageWithDecl(v___x_1459_, v___x_1458_, v___x_1457_, v___x_1456_, v___x_1455_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(lean_object* v_lhs_1461_, lean_object* v_rhs_1462_, uint8_t v_heq_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v_numArgs_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
v_numArgs_1475_ = l_Lean_Expr_getAppNumArgs(v_lhs_1461_);
v___x_1476_ = l_Lean_Expr_getAppNumArgs(v_rhs_1462_);
v___x_1477_ = lean_nat_dec_eq(v___x_1476_, v_numArgs_1475_);
lean_dec(v___x_1476_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec(v_numArgs_1475_);
lean_dec_ref(v_rhs_1462_);
lean_dec_ref(v_lhs_1461_);
v___x_1478_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2);
v___x_1479_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1478_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
return v___x_1479_;
}
else
{
lean_object* v_f_1480_; lean_object* v_g_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_f_1480_ = l_Lean_Expr_getAppFn(v_lhs_1461_);
v_g_1481_ = l_Lean_Expr_getAppFn(v_rhs_1462_);
v___x_1482_ = lean_box(0);
lean_inc_ref(v_f_1480_);
v___x_1483_ = l_Lean_Meta_getFunInfo(v_f_1480_, v___x_1482_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref_known(v___x_1483_, 1);
v___x_1485_ = l_Lean_Meta_FunInfo_getArity(v_a_1484_);
lean_dec(v_a_1484_);
v___x_1486_ = lean_nat_dec_lt(v___x_1485_, v_numArgs_1475_);
lean_dec(v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; 
v___x_1487_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_1480_, v_g_1481_, v_numArgs_1475_, v_lhs_1461_, v_rhs_1462_, v_heq_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
return v___x_1487_;
}
else
{
lean_object* v___x_1488_; 
lean_dec_ref(v_g_1481_);
lean_dec_ref(v_f_1480_);
lean_dec(v_numArgs_1475_);
lean_inc_ref(v_lhs_1461_);
v___x_1488_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(v_lhs_1461_, v_rhs_1462_);
if (lean_obj_tag(v___x_1488_) == 1)
{
lean_object* v_val_1489_; lean_object* v_fst_1490_; lean_object* v_snd_1491_; lean_object* v___y_1493_; lean_object* v___x_1506_; 
v_val_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_val_1489_);
lean_dec_ref_known(v___x_1488_, 1);
v_fst_1490_ = lean_ctor_get(v_val_1489_, 0);
lean_inc(v_fst_1490_);
v_snd_1491_ = lean_ctor_get(v_val_1489_, 1);
lean_inc_n(v_snd_1491_, 2);
lean_dec(v_val_1489_);
v___x_1506_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(v_fst_1490_, v_snd_1491_, v_a_1467_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
if (lean_obj_tag(v___x_1506_) == 0)
{
v___y_1493_ = v___x_1506_;
goto v___jp_1492_;
}
else
{
lean_object* v_a_1507_; uint8_t v___y_1509_; uint8_t v___x_1511_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1507_);
v___x_1511_ = l_Lean_Exception_isInterrupt(v_a_1507_);
if (v___x_1511_ == 0)
{
uint8_t v___x_1512_; 
v___x_1512_ = l_Lean_Exception_isRuntime(v_a_1507_);
v___y_1509_ = v___x_1512_;
goto v___jp_1508_;
}
else
{
lean_dec(v_a_1507_);
v___y_1509_ = v___x_1511_;
goto v___jp_1508_;
}
v___jp_1508_:
{
if (v___y_1509_ == 0)
{
lean_object* v___x_1510_; 
lean_dec_ref_known(v___x_1506_, 1);
lean_inc_ref(v_rhs_1462_);
lean_inc_ref(v_lhs_1461_);
v___x_1510_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1461_, v_rhs_1462_, lean_box(0), v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
v___y_1493_ = v___x_1510_;
goto v___jp_1492_;
}
else
{
v___y_1493_ = v___x_1506_;
goto v___jp_1492_;
}
}
}
v___jp_1492_:
{
if (lean_obj_tag(v___y_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1495_; 
v_a_1494_ = lean_ctor_get(v___y_1493_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v___y_1493_, 1);
v___x_1495_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_1494_, v_lhs_1461_, v_rhs_1462_, v_snd_1491_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
lean_dec(v_snd_1491_);
lean_dec_ref(v_rhs_1462_);
lean_dec_ref(v_lhs_1461_);
lean_dec(v_a_1494_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1497_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1496_);
lean_dec_ref_known(v___x_1495_, 1);
v___x_1497_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_1496_, v_heq_1463_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
return v___x_1497_;
}
else
{
return v___x_1495_;
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec(v_snd_1491_);
lean_dec_ref(v_rhs_1462_);
lean_dec_ref(v_lhs_1461_);
v_a_1498_ = lean_ctor_get(v___y_1493_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___y_1493_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___y_1493_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___y_1493_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
else
{
lean_object* v___x_1513_; 
lean_dec(v___x_1488_);
v___x_1513_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1461_, v_rhs_1462_, lean_box(0), v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
return v___x_1513_;
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec_ref(v_g_1481_);
lean_dec_ref(v_f_1480_);
lean_dec(v_numArgs_1475_);
lean_dec_ref(v_rhs_1462_);
lean_dec_ref(v_lhs_1461_);
v_a_1514_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1483_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1483_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(lean_object* v_lhs_1522_, lean_object* v_rhs_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
uint8_t v___x_1535_; 
v___x_1535_ = l_Lean_Expr_isApp(v_lhs_1522_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = lean_box(0);
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
return v___x_1537_;
}
else
{
lean_object* v_a_u2081_1538_; lean_object* v_a_u2082_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v_a_u2081_1538_ = l_Lean_Expr_appArg_x21(v_lhs_1522_);
v_a_u2082_1539_ = l_Lean_Expr_appArg_x21(v_rhs_1523_);
v___x_1540_ = l_Lean_Expr_appFn_x21(v_lhs_1522_);
v___x_1541_ = l_Lean_Expr_appFn_x21(v_rhs_1523_);
v___x_1542_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v___x_1540_, v___x_1541_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
lean_dec_ref(v___x_1541_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1640_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1640_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1640_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
if (lean_obj_tag(v_a_1543_) == 1)
{
lean_object* v_val_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1604_; 
lean_del_object(v___x_1545_);
lean_dec_ref(v___x_1540_);
v_val_1547_ = lean_ctor_get(v_a_1543_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_a_1543_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1549_ = v_a_1543_;
v_isShared_1550_ = v_isSharedCheck_1604_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_val_1547_);
lean_dec(v_a_1543_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1604_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
size_t v___x_1551_; size_t v___x_1552_; uint8_t v___x_1553_; 
v___x_1551_ = lean_ptr_addr(v_a_u2081_1538_);
v___x_1552_ = lean_ptr_addr(v_a_u2082_1539_);
v___x_1553_ = lean_usize_dec_eq(v___x_1551_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; 
v___x_1554_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_1538_, v_a_u2082_1539_, v___x_1553_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1556_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v___x_1556_ = l_Lean_Meta_mkCongr(v_val_1547_, v_a_1555_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1567_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1559_ = v___x_1556_;
v_isShared_1560_ = v_isSharedCheck_1567_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1556_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1567_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v_a_1557_);
v___x_1562_ = v___x_1549_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
lean_object* v___x_1564_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1562_);
v___x_1564_ = v___x_1559_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_del_object(v___x_1549_);
v_a_1568_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1556_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1556_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_del_object(v___x_1549_);
lean_dec(v_val_1547_);
v_a_1576_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1554_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1554_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
else
{
lean_object* v___x_1584_; 
lean_dec_ref(v_a_u2082_1539_);
v___x_1584_ = l_Lean_Meta_mkCongrFun(v_val_1547_, v_a_u2081_1538_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1595_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1595_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1595_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v_a_1585_);
v___x_1590_ = v___x_1549_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v___x_1592_; 
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1590_);
v___x_1592_ = v___x_1587_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_del_object(v___x_1549_);
v_a_1596_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1584_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1584_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
}
else
{
size_t v___x_1605_; size_t v___x_1606_; uint8_t v___x_1607_; 
lean_dec(v_a_1543_);
v___x_1605_ = lean_ptr_addr(v_a_u2081_1538_);
v___x_1606_ = lean_ptr_addr(v_a_u2082_1539_);
v___x_1607_ = lean_usize_dec_eq(v___x_1605_, v___x_1606_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; 
lean_del_object(v___x_1545_);
v___x_1608_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_1538_, v_a_u2082_1539_, v___x_1607_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1610_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___x_1608_, 1);
v___x_1610_ = l_Lean_Meta_mkCongrArg(v___x_1540_, v_a_1609_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1619_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1619_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1619_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1615_, 0, v_a_1611_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v___x_1615_);
v___x_1617_ = v___x_1613_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
v_a_1620_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1610_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1610_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec_ref(v___x_1540_);
v_a_1628_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1608_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1608_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
else
{
lean_object* v___x_1636_; lean_object* v___x_1638_; 
lean_dec_ref(v___x_1540_);
lean_dec_ref(v_a_u2082_1539_);
lean_dec_ref(v_a_u2081_1538_);
v___x_1636_ = lean_box(0);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1636_);
v___x_1638_ = v___x_1545_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1636_);
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
}
else
{
lean_dec_ref(v___x_1540_);
lean_dec_ref(v_a_u2082_1539_);
lean_dec_ref(v_a_u2081_1538_);
return v___x_1542_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__2));
v___x_1645_ = lean_unsigned_to_nat(14u);
v___x_1646_ = lean_unsigned_to_nat(22u);
v___x_1647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__1));
v___x_1648_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__0));
v___x_1649_ = l_mkPanicMessageWithDecl(v___x_1648_, v___x_1647_, v___x_1646_, v___x_1645_, v___x_1644_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(lean_object* v_lhs_1650_, lean_object* v_rhs_1651_, uint8_t v_heq_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_1650_, v_rhs_1651_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1678_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1667_ = v___x_1664_;
v_isShared_1668_ = v_isSharedCheck_1678_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1664_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1678_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___y_1670_; 
if (lean_obj_tag(v_a_1665_) == 0)
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3);
v___x_1676_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_spec__13(v___x_1675_);
v___y_1670_ = v___x_1676_;
goto v___jp_1669_;
}
else
{
lean_object* v_val_1677_; 
v_val_1677_ = lean_ctor_get(v_a_1665_, 0);
lean_inc(v_val_1677_);
lean_dec_ref_known(v_a_1665_, 1);
v___y_1670_ = v_val_1677_;
goto v___jp_1669_;
}
v___jp_1669_:
{
if (v_heq_1652_ == 0)
{
lean_object* v___x_1672_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v___y_1670_);
v___x_1672_ = v___x_1667_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___y_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
else
{
lean_object* v___x_1674_; 
lean_del_object(v___x_1667_);
v___x_1674_ = l_Lean_Meta_mkHEqOfEq(v___y_1670_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_);
return v___x_1674_;
}
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
v_a_1679_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1664_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1664_);
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
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__1(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1688_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1689_ = lean_unsigned_to_nat(36u);
v___x_1690_ = lean_unsigned_to_nat(143u);
v___x_1691_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1692_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1693_ = l_mkPanicMessageWithDecl(v___x_1692_, v___x_1691_, v___x_1690_, v___x_1689_, v___x_1688_);
return v___x_1693_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__2(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1694_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1695_ = lean_unsigned_to_nat(34u);
v___x_1696_ = lean_unsigned_to_nat(144u);
v___x_1697_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1698_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1699_ = l_mkPanicMessageWithDecl(v___x_1698_, v___x_1697_, v___x_1696_, v___x_1695_, v___x_1694_);
return v___x_1699_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__4(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1701_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__3));
v___x_1702_ = lean_unsigned_to_nat(4u);
v___x_1703_ = lean_unsigned_to_nat(145u);
v___x_1704_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1705_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1706_ = l_mkPanicMessageWithDecl(v___x_1705_, v___x_1704_, v___x_1703_, v___x_1702_, v___x_1701_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrProof(lean_object* v_lhs_1717_, lean_object* v_rhs_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; uint8_t v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; uint8_t v___y_1766_; lean_object* v_toCold_1802_; lean_object* v_currRecDepth_1803_; lean_object* v_ref_1804_; uint8_t v_diag_1805_; uint8_t v_suppressElabErrors_1806_; lean_object* v_maxRecDepth_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; lean_object* v___x_1839_; uint8_t v___x_1840_; 
v_toCold_1802_ = lean_ctor_get(v_a_1727_, 0);
v_currRecDepth_1803_ = lean_ctor_get(v_a_1727_, 1);
v_ref_1804_ = lean_ctor_get(v_a_1727_, 2);
v_diag_1805_ = lean_ctor_get_uint8(v_a_1727_, sizeof(void*)*3);
v_suppressElabErrors_1806_ = lean_ctor_get_uint8(v_a_1727_, sizeof(void*)*3 + 1);
v_maxRecDepth_1807_ = lean_ctor_get(v_toCold_1802_, 3);
v___x_1808_ = l_Lean_Expr_cleanupAnnotations(v_lhs_1717_);
v___x_1809_ = l_Lean_Expr_isApp(v___x_1808_);
v___x_1839_ = lean_unsigned_to_nat(0u);
v___x_1840_ = lean_nat_dec_eq(v_maxRecDepth_1807_, v___x_1839_);
if (v___x_1840_ == 0)
{
uint8_t v___x_1841_; 
v___x_1841_ = lean_nat_dec_eq(v_currRecDepth_1803_, v_maxRecDepth_1807_);
if (v___x_1841_ == 0)
{
goto v___jp_1810_;
}
else
{
lean_object* v___x_1842_; 
lean_dec_ref(v___x_1808_);
lean_dec_ref(v_rhs_1718_);
lean_inc(v_ref_1804_);
v___x_1842_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1804_);
return v___x_1842_;
}
}
else
{
goto v___jp_1810_;
}
v___jp_1730_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__1, &l_Lean_Meta_Grind_mkEqCongrProof___closed__1_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__1);
v___x_1742_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1741_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec_ref(v___y_1739_);
return v___x_1742_;
}
v___jp_1743_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__2, &l_Lean_Meta_Grind_mkEqCongrProof___closed__2_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__2);
v___x_1755_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1754_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec_ref(v___y_1752_);
return v___x_1755_;
}
v___jp_1756_:
{
if (v___y_1766_ == 0)
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
lean_dec_ref(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec_ref(v___y_1757_);
v___x_1767_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__4, &l_Lean_Meta_Grind_mkEqCongrProof___closed__4_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__4);
v___x_1768_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1767_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v___y_1762_, v_a_1728_);
lean_dec_ref(v___y_1762_);
return v___x_1768_;
}
else
{
lean_object* v___x_1769_; size_t v___x_1770_; size_t v___x_1771_; uint8_t v___x_1772_; 
v___x_1769_ = l_Lean_Expr_constLevels_x21(v___y_1765_);
lean_dec_ref(v___y_1765_);
v___x_1770_ = lean_ptr_addr(v___y_1758_);
v___x_1771_ = lean_ptr_addr(v___y_1764_);
v___x_1772_ = lean_usize_dec_eq(v___x_1770_, v___x_1771_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; 
lean_inc_ref(v___y_1760_);
lean_inc_ref(v___y_1759_);
v___x_1773_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1759_, v___y_1760_, v___y_1763_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v___y_1762_, v_a_1728_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1775_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref_known(v___x_1773_, 1);
lean_inc_ref(v___y_1761_);
lean_inc_ref(v___y_1757_);
v___x_1775_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1757_, v___y_1761_, v___y_1763_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v___y_1762_, v_a_1728_);
lean_dec_ref(v___y_1762_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1786_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1786_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1786_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1780_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__6));
v___x_1781_ = l_Lean_mkConst(v___x_1780_, v___x_1769_);
v___x_1782_ = l_Lean_mkApp8(v___x_1781_, v___y_1758_, v___y_1764_, v___y_1759_, v___y_1757_, v___y_1760_, v___y_1761_, v_a_1774_, v_a_1776_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1782_);
v___x_1784_ = v___x_1778_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
else
{
lean_dec(v_a_1774_);
lean_dec(v___x_1769_);
lean_dec_ref(v___y_1764_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec_ref(v___y_1757_);
return v___x_1775_;
}
}
else
{
lean_dec(v___x_1769_);
lean_dec_ref(v___y_1764_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec_ref(v___y_1757_);
return v___x_1773_;
}
}
else
{
uint8_t v___x_1787_; lean_object* v___x_1788_; 
lean_dec_ref(v___y_1764_);
v___x_1787_ = 0;
lean_inc_ref(v___y_1760_);
lean_inc_ref(v___y_1759_);
v___x_1788_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1759_, v___y_1760_, v___x_1787_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v___y_1762_, v_a_1728_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1790_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
lean_inc_ref(v___y_1761_);
lean_inc_ref(v___y_1757_);
v___x_1790_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1757_, v___y_1761_, v___x_1787_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v___y_1762_, v_a_1728_);
lean_dec_ref(v___y_1762_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1801_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1801_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1801_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1799_; 
v___x_1795_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__8));
v___x_1796_ = l_Lean_mkConst(v___x_1795_, v___x_1769_);
v___x_1797_ = l_Lean_mkApp7(v___x_1796_, v___y_1758_, v___y_1759_, v___y_1757_, v___y_1760_, v___y_1761_, v_a_1789_, v_a_1791_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 0, v___x_1797_);
v___x_1799_ = v___x_1793_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
else
{
lean_dec(v_a_1789_);
lean_dec(v___x_1769_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec_ref(v___y_1757_);
return v___x_1790_;
}
}
else
{
lean_dec(v___x_1769_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec_ref(v___y_1757_);
return v___x_1788_;
}
}
}
}
v___jp_1810_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1811_ = lean_unsigned_to_nat(1u);
v___x_1812_ = lean_nat_add(v_currRecDepth_1803_, v___x_1811_);
lean_inc(v_ref_1804_);
lean_inc_ref(v_toCold_1802_);
v___x_1813_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1813_, 0, v_toCold_1802_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
lean_ctor_set(v___x_1813_, 2, v_ref_1804_);
lean_ctor_set_uint8(v___x_1813_, sizeof(void*)*3, v_diag_1805_);
lean_ctor_set_uint8(v___x_1813_, sizeof(void*)*3 + 1, v_suppressElabErrors_1806_);
if (v___x_1809_ == 0)
{
lean_dec_ref(v___x_1808_);
lean_dec_ref(v_rhs_1718_);
v___y_1731_ = v_a_1719_;
v___y_1732_ = v_a_1720_;
v___y_1733_ = v_a_1721_;
v___y_1734_ = v_a_1722_;
v___y_1735_ = v_a_1723_;
v___y_1736_ = v_a_1724_;
v___y_1737_ = v_a_1725_;
v___y_1738_ = v_a_1726_;
v___y_1739_ = v___x_1813_;
v___y_1740_ = v_a_1728_;
goto v___jp_1730_;
}
else
{
lean_object* v_arg_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; 
v_arg_1814_ = lean_ctor_get(v___x_1808_, 1);
lean_inc_ref(v_arg_1814_);
v___x_1815_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1808_);
v___x_1816_ = l_Lean_Expr_isApp(v___x_1815_);
if (v___x_1816_ == 0)
{
lean_dec_ref(v___x_1815_);
lean_dec_ref(v_arg_1814_);
lean_dec_ref(v_rhs_1718_);
v___y_1731_ = v_a_1719_;
v___y_1732_ = v_a_1720_;
v___y_1733_ = v_a_1721_;
v___y_1734_ = v_a_1722_;
v___y_1735_ = v_a_1723_;
v___y_1736_ = v_a_1724_;
v___y_1737_ = v_a_1725_;
v___y_1738_ = v_a_1726_;
v___y_1739_ = v___x_1813_;
v___y_1740_ = v_a_1728_;
goto v___jp_1730_;
}
else
{
lean_object* v_arg_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; 
v_arg_1817_ = lean_ctor_get(v___x_1815_, 1);
lean_inc_ref(v_arg_1817_);
v___x_1818_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1815_);
v___x_1819_ = l_Lean_Expr_isApp(v___x_1818_);
if (v___x_1819_ == 0)
{
lean_dec_ref(v___x_1818_);
lean_dec_ref(v_arg_1817_);
lean_dec_ref(v_arg_1814_);
lean_dec_ref(v_rhs_1718_);
v___y_1731_ = v_a_1719_;
v___y_1732_ = v_a_1720_;
v___y_1733_ = v_a_1721_;
v___y_1734_ = v_a_1722_;
v___y_1735_ = v_a_1723_;
v___y_1736_ = v_a_1724_;
v___y_1737_ = v_a_1725_;
v___y_1738_ = v_a_1726_;
v___y_1739_ = v___x_1813_;
v___y_1740_ = v_a_1728_;
goto v___jp_1730_;
}
else
{
lean_object* v_arg_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
v_arg_1820_ = lean_ctor_get(v___x_1818_, 1);
lean_inc_ref(v_arg_1820_);
v___x_1821_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1818_);
v___x_1822_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_1823_ = l_Lean_Expr_isConstOf(v___x_1821_, v___x_1822_);
if (v___x_1823_ == 0)
{
lean_dec_ref(v___x_1821_);
lean_dec_ref(v_arg_1820_);
lean_dec_ref(v_arg_1817_);
lean_dec_ref(v_arg_1814_);
lean_dec_ref(v_rhs_1718_);
v___y_1731_ = v_a_1719_;
v___y_1732_ = v_a_1720_;
v___y_1733_ = v_a_1721_;
v___y_1734_ = v_a_1722_;
v___y_1735_ = v_a_1723_;
v___y_1736_ = v_a_1724_;
v___y_1737_ = v_a_1725_;
v___y_1738_ = v_a_1726_;
v___y_1739_ = v___x_1813_;
v___y_1740_ = v_a_1728_;
goto v___jp_1730_;
}
else
{
lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1824_ = l_Lean_Expr_cleanupAnnotations(v_rhs_1718_);
v___x_1825_ = l_Lean_Expr_isApp(v___x_1824_);
if (v___x_1825_ == 0)
{
lean_dec_ref(v___x_1824_);
lean_dec_ref(v___x_1821_);
lean_dec_ref(v_arg_1820_);
lean_dec_ref(v_arg_1817_);
lean_dec_ref(v_arg_1814_);
v___y_1744_ = v_a_1719_;
v___y_1745_ = v_a_1720_;
v___y_1746_ = v_a_1721_;
v___y_1747_ = v_a_1722_;
v___y_1748_ = v_a_1723_;
v___y_1749_ = v_a_1724_;
v___y_1750_ = v_a_1725_;
v___y_1751_ = v_a_1726_;
v___y_1752_ = v___x_1813_;
v___y_1753_ = v_a_1728_;
goto v___jp_1743_;
}
else
{
lean_object* v_arg_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v_arg_1826_ = lean_ctor_get(v___x_1824_, 1);
lean_inc_ref(v_arg_1826_);
v___x_1827_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1824_);
v___x_1828_ = l_Lean_Expr_isApp(v___x_1827_);
if (v___x_1828_ == 0)
{
lean_dec_ref(v___x_1827_);
lean_dec_ref(v_arg_1826_);
lean_dec_ref(v___x_1821_);
lean_dec_ref(v_arg_1820_);
lean_dec_ref(v_arg_1817_);
lean_dec_ref(v_arg_1814_);
v___y_1744_ = v_a_1719_;
v___y_1745_ = v_a_1720_;
v___y_1746_ = v_a_1721_;
v___y_1747_ = v_a_1722_;
v___y_1748_ = v_a_1723_;
v___y_1749_ = v_a_1724_;
v___y_1750_ = v_a_1725_;
v___y_1751_ = v_a_1726_;
v___y_1752_ = v___x_1813_;
v___y_1753_ = v_a_1728_;
goto v___jp_1743_;
}
else
{
lean_object* v_arg_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v_arg_1829_ = lean_ctor_get(v___x_1827_, 1);
lean_inc_ref(v_arg_1829_);
v___x_1830_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1827_);
v___x_1831_ = l_Lean_Expr_isApp(v___x_1830_);
if (v___x_1831_ == 0)
{
lean_dec_ref(v___x_1830_);
lean_dec_ref(v_arg_1829_);
lean_dec_ref(v_arg_1826_);
lean_dec_ref(v___x_1821_);
lean_dec_ref(v_arg_1820_);
lean_dec_ref(v_arg_1817_);
lean_dec_ref(v_arg_1814_);
v___y_1744_ = v_a_1719_;
v___y_1745_ = v_a_1720_;
v___y_1746_ = v_a_1721_;
v___y_1747_ = v_a_1722_;
v___y_1748_ = v_a_1723_;
v___y_1749_ = v_a_1724_;
v___y_1750_ = v_a_1725_;
v___y_1751_ = v_a_1726_;
v___y_1752_ = v___x_1813_;
v___y_1753_ = v_a_1728_;
goto v___jp_1743_;
}
else
{
lean_object* v_arg_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v_arg_1832_ = lean_ctor_get(v___x_1830_, 1);
lean_inc_ref(v_arg_1832_);
v___x_1833_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1830_);
v___x_1834_ = l_Lean_Expr_isConstOf(v___x_1833_, v___x_1822_);
lean_dec_ref(v___x_1833_);
if (v___x_1834_ == 0)
{
lean_dec_ref(v_arg_1832_);
lean_dec_ref(v_arg_1829_);
lean_dec_ref(v_arg_1826_);
lean_dec_ref(v___x_1821_);
lean_dec_ref(v_arg_1820_);
lean_dec_ref(v_arg_1817_);
lean_dec_ref(v_arg_1814_);
v___y_1744_ = v_a_1719_;
v___y_1745_ = v_a_1720_;
v___y_1746_ = v_a_1721_;
v___y_1747_ = v_a_1722_;
v___y_1748_ = v_a_1723_;
v___y_1749_ = v_a_1724_;
v___y_1750_ = v_a_1725_;
v___y_1751_ = v_a_1726_;
v___y_1752_ = v___x_1813_;
v___y_1753_ = v_a_1728_;
goto v___jp_1743_;
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1835_ = lean_st_ref_get(v_a_1719_);
v___x_1836_ = lean_st_ref_get(v_a_1719_);
v___x_1837_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1835_, v_arg_1817_, v_arg_1829_);
lean_dec(v___x_1835_);
if (v___x_1837_ == 0)
{
lean_dec(v___x_1836_);
v___y_1757_ = v_arg_1814_;
v___y_1758_ = v_arg_1820_;
v___y_1759_ = v_arg_1817_;
v___y_1760_ = v_arg_1829_;
v___y_1761_ = v_arg_1826_;
v___y_1762_ = v___x_1813_;
v___y_1763_ = v___x_1834_;
v___y_1764_ = v_arg_1832_;
v___y_1765_ = v___x_1821_;
v___y_1766_ = v___x_1837_;
goto v___jp_1756_;
}
else
{
uint8_t v___x_1838_; 
v___x_1838_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1836_, v_arg_1814_, v_arg_1826_);
lean_dec(v___x_1836_);
v___y_1757_ = v_arg_1814_;
v___y_1758_ = v_arg_1820_;
v___y_1759_ = v_arg_1817_;
v___y_1760_ = v_arg_1829_;
v___y_1761_ = v_arg_1826_;
v___y_1762_ = v___x_1813_;
v___y_1763_ = v___x_1834_;
v___y_1764_ = v_arg_1832_;
v___y_1765_ = v___x_1821_;
v___y_1766_ = v___x_1838_;
goto v___jp_1756_;
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1853_ = lean_box(0);
v___x_1854_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3));
v___x_1855_ = l_Lean_mkConst(v___x_1854_, v___x_1853_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(lean_object* v_lhs_1856_, lean_object* v_rhs_1857_, uint8_t v_heq_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v___x_1870_; lean_object* v_p_1871_; lean_object* v_hp_1872_; lean_object* v___x_1873_; lean_object* v_q_1874_; lean_object* v_hq_1875_; uint8_t v___x_1876_; lean_object* v___x_1877_; 
v___x_1870_ = l_Lean_Expr_appFn_x21(v_lhs_1856_);
v_p_1871_ = l_Lean_Expr_appArg_x21(v___x_1870_);
lean_dec_ref(v___x_1870_);
v_hp_1872_ = l_Lean_Expr_appArg_x21(v_lhs_1856_);
v___x_1873_ = l_Lean_Expr_appFn_x21(v_rhs_1857_);
v_q_1874_ = l_Lean_Expr_appArg_x21(v___x_1873_);
lean_dec_ref(v___x_1873_);
v_hq_1875_ = l_Lean_Expr_appArg_x21(v_rhs_1857_);
v___x_1876_ = 0;
lean_inc_ref(v_q_1874_);
lean_inc_ref(v_p_1871_);
v___x_1877_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_p_1871_, v_q_1874_, v___x_1876_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref_known(v___x_1877_, 1);
v___x_1879_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4);
v___x_1880_ = l_Lean_mkApp5(v___x_1879_, v_p_1871_, v_q_1874_, v_a_1878_, v_hp_1872_, v_hq_1875_);
v___x_1881_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v___x_1880_, v_heq_1858_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
return v___x_1881_;
}
else
{
lean_dec_ref(v_hq_1875_);
lean_dec_ref(v_q_1874_);
lean_dec_ref(v_hp_1872_);
lean_dec_ref(v_p_1871_);
return v___x_1877_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = lean_box(0);
v___x_1893_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1));
v___x_1894_ = l_Lean_mkConst(v___x_1893_, v___x_1892_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(lean_object* v_lhs_1895_, lean_object* v_rhs_1896_, uint8_t v_heq_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v___x_1909_; lean_object* v_p_1910_; lean_object* v_hp_1911_; lean_object* v___x_1912_; lean_object* v_q_1913_; lean_object* v_hq_1914_; uint8_t v___x_1915_; lean_object* v___x_1916_; 
v___x_1909_ = l_Lean_Expr_appFn_x21(v_lhs_1895_);
v_p_1910_ = l_Lean_Expr_appArg_x21(v___x_1909_);
lean_dec_ref(v___x_1909_);
v_hp_1911_ = l_Lean_Expr_appArg_x21(v_lhs_1895_);
v___x_1912_ = l_Lean_Expr_appFn_x21(v_rhs_1896_);
v_q_1913_ = l_Lean_Expr_appArg_x21(v___x_1912_);
lean_dec_ref(v___x_1912_);
v_hq_1914_ = l_Lean_Expr_appArg_x21(v_rhs_1896_);
v___x_1915_ = 0;
lean_inc_ref(v_q_1913_);
lean_inc_ref(v_p_1910_);
v___x_1916_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_p_1910_, v_q_1913_, v___x_1915_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1916_, 1);
v___x_1918_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2);
v___x_1919_ = l_Lean_mkApp5(v___x_1918_, v_p_1910_, v_q_1913_, v_a_1917_, v_hp_1911_, v_hq_1914_);
v___x_1920_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v___x_1919_, v_heq_1897_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
return v___x_1920_;
}
else
{
lean_dec_ref(v_hq_1914_);
lean_dec_ref(v_q_1913_);
lean_dec_ref(v_hp_1911_);
lean_dec_ref(v_p_1910_);
return v___x_1916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(lean_object* v_lhs_1921_, lean_object* v_rhs_1922_, uint8_t v_heq_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
if (lean_obj_tag(v_lhs_1921_) == 7)
{
if (lean_obj_tag(v_rhs_1922_) == 7)
{
lean_object* v_binderType_1935_; lean_object* v_body_1936_; lean_object* v_binderType_1937_; lean_object* v_body_1938_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1970_; lean_object* v___x_1999_; uint8_t v_transparency_2000_; uint8_t v___x_2001_; uint8_t v___x_2002_; 
v_binderType_1935_ = lean_ctor_get(v_lhs_1921_, 1);
lean_inc_ref(v_binderType_1935_);
v_body_1936_ = lean_ctor_get(v_lhs_1921_, 2);
lean_inc_ref(v_body_1936_);
lean_dec_ref_known(v_lhs_1921_, 3);
v_binderType_1937_ = lean_ctor_get(v_rhs_1922_, 1);
lean_inc_ref(v_binderType_1937_);
v_body_1938_ = lean_ctor_get(v_rhs_1922_, 2);
lean_inc_ref(v_body_1938_);
lean_dec_ref_known(v_rhs_1922_, 3);
v___x_1999_ = l_Lean_Meta_Context_config(v_a_1930_);
v_transparency_2000_ = lean_ctor_get_uint8(v___x_1999_, 9);
lean_dec_ref(v___x_1999_);
v___x_2001_ = 1;
v___x_2002_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2000_, v___x_2001_);
if (v___x_2002_ == 0)
{
lean_object* v_keyedConfig_2003_; uint8_t v_trackZetaDelta_2004_; lean_object* v_zetaDeltaSet_2005_; lean_object* v_lctx_2006_; lean_object* v_localInstances_2007_; lean_object* v_defEqCtx_x3f_2008_; lean_object* v_synthPendingDepth_2009_; lean_object* v_customCanUnfoldPredicate_x3f_2010_; uint8_t v_univApprox_2011_; uint8_t v_inTypeClassResolution_2012_; uint8_t v_cacheInferType_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v_keyedConfig_2003_ = lean_ctor_get(v_a_1930_, 0);
v_trackZetaDelta_2004_ = lean_ctor_get_uint8(v_a_1930_, sizeof(void*)*7);
v_zetaDeltaSet_2005_ = lean_ctor_get(v_a_1930_, 1);
v_lctx_2006_ = lean_ctor_get(v_a_1930_, 2);
v_localInstances_2007_ = lean_ctor_get(v_a_1930_, 3);
v_defEqCtx_x3f_2008_ = lean_ctor_get(v_a_1930_, 4);
v_synthPendingDepth_2009_ = lean_ctor_get(v_a_1930_, 5);
v_customCanUnfoldPredicate_x3f_2010_ = lean_ctor_get(v_a_1930_, 6);
v_univApprox_2011_ = lean_ctor_get_uint8(v_a_1930_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2012_ = lean_ctor_get_uint8(v_a_1930_, sizeof(void*)*7 + 2);
v_cacheInferType_2013_ = lean_ctor_get_uint8(v_a_1930_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2003_);
v___x_2014_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2001_, v_keyedConfig_2003_);
lean_inc(v_customCanUnfoldPredicate_x3f_2010_);
lean_inc(v_synthPendingDepth_2009_);
lean_inc(v_defEqCtx_x3f_2008_);
lean_inc_ref(v_localInstances_2007_);
lean_inc_ref(v_lctx_2006_);
lean_inc(v_zetaDeltaSet_2005_);
v___x_2015_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
lean_ctor_set(v___x_2015_, 1, v_zetaDeltaSet_2005_);
lean_ctor_set(v___x_2015_, 2, v_lctx_2006_);
lean_ctor_set(v___x_2015_, 3, v_localInstances_2007_);
lean_ctor_set(v___x_2015_, 4, v_defEqCtx_x3f_2008_);
lean_ctor_set(v___x_2015_, 5, v_synthPendingDepth_2009_);
lean_ctor_set(v___x_2015_, 6, v_customCanUnfoldPredicate_x3f_2010_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*7, v_trackZetaDelta_2004_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*7 + 1, v_univApprox_2011_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2012_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*7 + 3, v_cacheInferType_2013_);
lean_inc_ref(v_binderType_1935_);
v___x_2016_ = l_Lean_Meta_getLevel(v_binderType_1935_, v___x_2015_, v_a_1931_, v_a_1932_, v_a_1933_);
lean_dec_ref_known(v___x_2015_, 7);
v___y_1970_ = v___x_2016_;
goto v___jp_1969_;
}
else
{
lean_object* v___x_2017_; 
lean_inc_ref(v_binderType_1935_);
v___x_2017_ = l_Lean_Meta_getLevel(v_binderType_1935_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
v___y_1970_ = v___x_2017_;
goto v___jp_1969_;
}
v___jp_1939_:
{
if (lean_obj_tag(v___y_1941_) == 0)
{
lean_object* v_a_1942_; uint8_t v___x_1943_; lean_object* v___x_1944_; 
v_a_1942_ = lean_ctor_get(v___y_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___y_1941_, 1);
v___x_1943_ = 0;
lean_inc_ref(v_binderType_1937_);
lean_inc_ref(v_binderType_1935_);
v___x_1944_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_binderType_1935_, v_binderType_1937_, v___x_1943_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1946_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1944_, 1);
lean_inc_ref(v_body_1938_);
lean_inc_ref(v_body_1936_);
v___x_1946_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_body_1936_, v_body_1938_, v___x_1943_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1960_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_1960_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1960_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1951_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__1));
v___x_1952_ = lean_box(0);
v___x_1953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1953_, 0, v_a_1942_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___y_1940_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
v___x_1955_ = l_Lean_mkConst(v___x_1951_, v___x_1954_);
v___x_1956_ = l_Lean_mkApp6(v___x_1955_, v_binderType_1935_, v_binderType_1937_, v_body_1936_, v_body_1938_, v_a_1945_, v_a_1947_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_1956_);
v___x_1958_ = v___x_1949_;
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
lean_dec(v_a_1945_);
lean_dec(v_a_1942_);
lean_dec(v___y_1940_);
lean_dec_ref(v_body_1938_);
lean_dec_ref(v_binderType_1937_);
lean_dec_ref(v_body_1936_);
lean_dec_ref(v_binderType_1935_);
return v___x_1946_;
}
}
else
{
lean_dec(v_a_1942_);
lean_dec(v___y_1940_);
lean_dec_ref(v_body_1938_);
lean_dec_ref(v_binderType_1937_);
lean_dec_ref(v_body_1936_);
lean_dec_ref(v_binderType_1935_);
return v___x_1944_;
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec(v___y_1940_);
lean_dec_ref(v_body_1938_);
lean_dec_ref(v_binderType_1937_);
lean_dec_ref(v_body_1936_);
lean_dec_ref(v_binderType_1935_);
v_a_1961_ = lean_ctor_get(v___y_1941_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___y_1941_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___y_1941_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___y_1941_);
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
v___jp_1969_:
{
if (lean_obj_tag(v___y_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1972_; uint8_t v_transparency_1973_; uint8_t v___x_1974_; uint8_t v___x_1975_; 
v_a_1971_ = lean_ctor_get(v___y_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v___y_1970_, 1);
v___x_1972_ = l_Lean_Meta_Context_config(v_a_1930_);
v_transparency_1973_ = lean_ctor_get_uint8(v___x_1972_, 9);
lean_dec_ref(v___x_1972_);
v___x_1974_ = 1;
v___x_1975_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1973_, v___x_1974_);
if (v___x_1975_ == 0)
{
lean_object* v_keyedConfig_1976_; uint8_t v_trackZetaDelta_1977_; lean_object* v_zetaDeltaSet_1978_; lean_object* v_lctx_1979_; lean_object* v_localInstances_1980_; lean_object* v_defEqCtx_x3f_1981_; lean_object* v_synthPendingDepth_1982_; lean_object* v_customCanUnfoldPredicate_x3f_1983_; uint8_t v_univApprox_1984_; uint8_t v_inTypeClassResolution_1985_; uint8_t v_cacheInferType_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v_keyedConfig_1976_ = lean_ctor_get(v_a_1930_, 0);
v_trackZetaDelta_1977_ = lean_ctor_get_uint8(v_a_1930_, sizeof(void*)*7);
v_zetaDeltaSet_1978_ = lean_ctor_get(v_a_1930_, 1);
v_lctx_1979_ = lean_ctor_get(v_a_1930_, 2);
v_localInstances_1980_ = lean_ctor_get(v_a_1930_, 3);
v_defEqCtx_x3f_1981_ = lean_ctor_get(v_a_1930_, 4);
v_synthPendingDepth_1982_ = lean_ctor_get(v_a_1930_, 5);
v_customCanUnfoldPredicate_x3f_1983_ = lean_ctor_get(v_a_1930_, 6);
v_univApprox_1984_ = lean_ctor_get_uint8(v_a_1930_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1985_ = lean_ctor_get_uint8(v_a_1930_, sizeof(void*)*7 + 2);
v_cacheInferType_1986_ = lean_ctor_get_uint8(v_a_1930_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1976_);
v___x_1987_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1974_, v_keyedConfig_1976_);
lean_inc(v_customCanUnfoldPredicate_x3f_1983_);
lean_inc(v_synthPendingDepth_1982_);
lean_inc(v_defEqCtx_x3f_1981_);
lean_inc_ref(v_localInstances_1980_);
lean_inc_ref(v_lctx_1979_);
lean_inc(v_zetaDeltaSet_1978_);
v___x_1988_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
lean_ctor_set(v___x_1988_, 1, v_zetaDeltaSet_1978_);
lean_ctor_set(v___x_1988_, 2, v_lctx_1979_);
lean_ctor_set(v___x_1988_, 3, v_localInstances_1980_);
lean_ctor_set(v___x_1988_, 4, v_defEqCtx_x3f_1981_);
lean_ctor_set(v___x_1988_, 5, v_synthPendingDepth_1982_);
lean_ctor_set(v___x_1988_, 6, v_customCanUnfoldPredicate_x3f_1983_);
lean_ctor_set_uint8(v___x_1988_, sizeof(void*)*7, v_trackZetaDelta_1977_);
lean_ctor_set_uint8(v___x_1988_, sizeof(void*)*7 + 1, v_univApprox_1984_);
lean_ctor_set_uint8(v___x_1988_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1985_);
lean_ctor_set_uint8(v___x_1988_, sizeof(void*)*7 + 3, v_cacheInferType_1986_);
lean_inc_ref(v_body_1936_);
v___x_1989_ = l_Lean_Meta_getLevel(v_body_1936_, v___x_1988_, v_a_1931_, v_a_1932_, v_a_1933_);
lean_dec_ref_known(v___x_1988_, 7);
v___y_1940_ = v_a_1971_;
v___y_1941_ = v___x_1989_;
goto v___jp_1939_;
}
else
{
lean_object* v___x_1990_; 
lean_inc_ref(v_body_1936_);
v___x_1990_ = l_Lean_Meta_getLevel(v_body_1936_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
v___y_1940_ = v_a_1971_;
v___y_1941_ = v___x_1990_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_dec_ref(v_body_1938_);
lean_dec_ref(v_binderType_1937_);
lean_dec_ref(v_body_1936_);
lean_dec_ref(v_binderType_1935_);
v_a_1991_ = lean_ctor_get(v___y_1970_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___y_1970_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___y_1970_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___y_1970_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
lean_dec_ref_known(v_lhs_1921_, 3);
lean_dec_ref(v_rhs_1922_);
v___x_2018_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3);
v___x_2019_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2018_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
return v___x_2019_;
}
}
else
{
lean_object* v___x_2020_; 
lean_inc_ref(v_lhs_1921_);
v___x_2020_ = l_Lean_Meta_Grind_useFunCC___redArg(v_lhs_1921_, v_a_1924_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; uint8_t v___x_2022_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v___x_2020_, 1);
v___x_2022_ = lean_unbox(v_a_2021_);
lean_dec(v_a_2021_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; 
v___x_2023_ = l_Lean_Expr_getAppNumArgs(v_lhs_1921_);
v___x_2024_ = l_Lean_Expr_getAppNumArgs(v_rhs_1922_);
v___x_2025_ = lean_nat_dec_eq(v___x_2024_, v___x_2023_);
lean_dec(v___x_2024_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
lean_dec(v___x_2023_);
lean_dec_ref(v_rhs_1922_);
lean_dec_ref(v_lhs_1921_);
v___x_2026_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5);
v___x_2027_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2026_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
return v___x_2027_;
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2028_ = l_Lean_Expr_getAppFn(v_lhs_1921_);
v___x_2029_ = l_Lean_Expr_getAppFn(v_rhs_1922_);
v___x_2053_ = lean_unsigned_to_nat(2u);
v___x_2054_ = lean_nat_dec_eq(v___x_2023_, v___x_2053_);
if (v___x_2054_ == 0)
{
goto v___jp_2055_;
}
else
{
lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2060_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9));
v___x_2061_ = l_Lean_Expr_isConstOf(v___x_2028_, v___x_2060_);
if (v___x_2061_ == 0)
{
goto v___jp_2055_;
}
else
{
uint8_t v___x_2062_; 
v___x_2062_ = l_Lean_Expr_isConstOf(v___x_2029_, v___x_2060_);
if (v___x_2062_ == 0)
{
goto v___jp_2055_;
}
else
{
lean_object* v___x_2063_; 
lean_dec_ref(v___x_2029_);
lean_dec_ref(v___x_2028_);
lean_dec(v___x_2023_);
v___x_2063_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_1921_, v_rhs_1922_, v_heq_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
lean_dec_ref(v_rhs_1922_);
lean_dec_ref(v_lhs_1921_);
return v___x_2063_;
}
}
}
v___jp_2030_:
{
lean_object* v___x_2031_; 
lean_inc_ref(v_rhs_1922_);
lean_inc_ref(v_lhs_1921_);
v___x_2031_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(v_lhs_1921_, v_rhs_1922_, v___x_2028_, v___x_2029_, v___x_2023_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
lean_dec_ref(v___x_2029_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; uint8_t v___x_2033_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2031_, 1);
v___x_2033_ = lean_unbox(v_a_2032_);
lean_dec(v_a_2032_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; 
v___x_2034_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_1921_, v_rhs_1922_, v_heq_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
return v___x_2034_;
}
else
{
lean_object* v___x_2035_; 
v___x_2035_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_1921_, v_rhs_1922_, v_heq_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
lean_dec_ref(v_rhs_1922_);
lean_dec_ref(v_lhs_1921_);
return v___x_2035_;
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_dec_ref(v_rhs_1922_);
lean_dec_ref(v_lhs_1921_);
v_a_2036_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2031_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2031_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
v___jp_2044_:
{
lean_object* v___x_2045_; uint8_t v___x_2046_; 
v___x_2045_ = lean_unsigned_to_nat(3u);
v___x_2046_ = lean_nat_dec_eq(v___x_2023_, v___x_2045_);
if (v___x_2046_ == 0)
{
goto v___jp_2030_;
}
else
{
lean_object* v___x_2047_; uint8_t v___x_2048_; 
v___x_2047_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_2048_ = l_Lean_Expr_isConstOf(v___x_2028_, v___x_2047_);
if (v___x_2048_ == 0)
{
goto v___jp_2030_;
}
else
{
uint8_t v___x_2049_; 
v___x_2049_ = l_Lean_Expr_isConstOf(v___x_2029_, v___x_2047_);
if (v___x_2049_ == 0)
{
goto v___jp_2030_;
}
else
{
lean_object* v___x_2050_; 
lean_dec_ref(v___x_2029_);
lean_dec_ref(v___x_2028_);
lean_dec(v___x_2023_);
v___x_2050_ = l_Lean_Meta_Grind_mkEqCongrProof(v_lhs_1921_, v_rhs_1922_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
if (lean_obj_tag(v___x_2050_) == 0)
{
if (v_heq_1923_ == 0)
{
return v___x_2050_;
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2052_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref_known(v___x_2050_, 1);
v___x_2052_ = l_Lean_Meta_mkHEqOfEq(v_a_2051_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
return v___x_2052_;
}
}
else
{
return v___x_2050_;
}
}
}
}
}
v___jp_2055_:
{
if (v___x_2054_ == 0)
{
goto v___jp_2044_;
}
else
{
lean_object* v___x_2056_; uint8_t v___x_2057_; 
v___x_2056_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7));
v___x_2057_ = l_Lean_Expr_isConstOf(v___x_2028_, v___x_2056_);
if (v___x_2057_ == 0)
{
goto v___jp_2044_;
}
else
{
uint8_t v___x_2058_; 
v___x_2058_ = l_Lean_Expr_isConstOf(v___x_2029_, v___x_2056_);
if (v___x_2058_ == 0)
{
goto v___jp_2044_;
}
else
{
lean_object* v___x_2059_; 
lean_dec_ref(v___x_2029_);
lean_dec_ref(v___x_2028_);
lean_dec(v___x_2023_);
v___x_2059_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_1921_, v_rhs_1922_, v_heq_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
lean_dec_ref(v_rhs_1922_);
lean_dec_ref(v_lhs_1921_);
return v___x_2059_;
}
}
}
}
}
}
else
{
lean_object* v___x_2064_; 
v___x_2064_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_1921_, v_rhs_1922_, v_heq_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
return v___x_2064_;
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec_ref(v_rhs_1922_);
lean_dec_ref(v_lhs_1921_);
v_a_2065_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2020_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2020_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(lean_object* v_lhs_2073_, lean_object* v_rhs_2074_, lean_object* v_h_2075_, uint8_t v_flipped_2076_, uint8_t v_heq_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2089_ = l_Lean_Meta_Grind_congrPlaceholderProof;
v___x_2090_ = lean_expr_eqv(v_h_2075_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2091_ = l_Lean_Meta_Grind_eqCongrSymmPlaceholderProof;
v___x_2092_ = lean_expr_eqv(v_h_2075_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; 
lean_dec_ref(v_rhs_2074_);
lean_dec_ref(v_lhs_2073_);
v___x_2093_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(v_h_2075_, v_flipped_2076_, v_heq_2077_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
return v___x_2093_;
}
else
{
lean_object* v___x_2094_; 
lean_dec_ref(v_h_2075_);
v___x_2094_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(v_lhs_2073_, v_rhs_2074_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
if (lean_obj_tag(v___x_2094_) == 0)
{
if (v_heq_2077_ == 0)
{
return v___x_2094_;
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2096_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2096_ = l_Lean_Meta_mkHEqOfEq(v_a_2095_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
return v___x_2096_;
}
}
else
{
return v___x_2094_;
}
}
}
else
{
lean_object* v___x_2097_; 
lean_dec_ref(v_h_2075_);
v___x_2097_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(v_lhs_2073_, v_rhs_2074_, v_heq_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
return v___x_2097_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1(void){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2099_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2100_ = lean_unsigned_to_nat(29u);
v___x_2101_ = lean_unsigned_to_nat(288u);
v___x_2102_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0));
v___x_2103_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2104_ = l_mkPanicMessageWithDecl(v___x_2103_, v___x_2102_, v___x_2101_, v___x_2100_, v___x_2099_);
return v___x_2104_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2105_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2106_ = lean_unsigned_to_nat(35u);
v___x_2107_ = lean_unsigned_to_nat(287u);
v___x_2108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0));
v___x_2109_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2110_ = l_mkPanicMessageWithDecl(v___x_2109_, v___x_2108_, v___x_2107_, v___x_2106_, v___x_2105_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(lean_object* v_lhs_2111_, lean_object* v_common_2112_, lean_object* v_acc_2113_, uint8_t v_heq_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
size_t v___x_2126_; size_t v___x_2127_; uint8_t v___x_2128_; 
v___x_2126_ = lean_ptr_addr(v_lhs_2111_);
v___x_2127_ = lean_ptr_addr(v_common_2112_);
v___x_2128_ = lean_usize_dec_eq(v___x_2126_, v___x_2127_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = lean_st_ref_get(v_a_2115_);
lean_inc_ref(v_lhs_2111_);
v___x_2130_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2129_, v_lhs_2111_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
lean_dec(v___x_2129_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v_target_x3f_2132_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v_target_x3f_2132_ = lean_ctor_get(v_a_2131_, 4);
lean_inc(v_target_x3f_2132_);
if (lean_obj_tag(v_target_x3f_2132_) == 1)
{
lean_object* v_proof_x3f_2133_; 
v_proof_x3f_2133_ = lean_ctor_get(v_a_2131_, 5);
lean_inc(v_proof_x3f_2133_);
if (lean_obj_tag(v_proof_x3f_2133_) == 1)
{
uint8_t v_flipped_2134_; lean_object* v_val_2135_; lean_object* v_val_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2164_; 
v_flipped_2134_ = lean_ctor_get_uint8(v_a_2131_, sizeof(void*)*12);
lean_dec(v_a_2131_);
v_val_2135_ = lean_ctor_get(v_target_x3f_2132_, 0);
lean_inc(v_val_2135_);
lean_dec_ref_known(v_target_x3f_2132_, 1);
v_val_2136_ = lean_ctor_get(v_proof_x3f_2133_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_proof_x3f_2133_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2138_ = v_proof_x3f_2133_;
v_isShared_2139_ = v_isSharedCheck_2164_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_val_2136_);
lean_dec(v_proof_x3f_2133_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2164_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; 
lean_inc(v_val_2135_);
v___x_2140_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_lhs_2111_, v_val_2135_, v_val_2136_, v_flipped_2134_, v_heq_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2142_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2140_, 1);
v___x_2142_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_acc_2113_, v_a_2141_, v_heq_2114_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2145_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2142_, 1);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v_a_2143_);
v___x_2145_ = v___x_2138_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2143_);
v___x_2145_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
v_lhs_2111_ = v_val_2135_;
v_acc_2113_ = v___x_2145_;
goto _start;
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_del_object(v___x_2138_);
lean_dec(v_val_2135_);
v_a_2148_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2142_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2142_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
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
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_del_object(v___x_2138_);
lean_dec(v_val_2135_);
lean_dec(v_acc_2113_);
v_a_2156_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2140_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2140_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec(v_proof_x3f_2133_);
lean_dec_ref_known(v_target_x3f_2132_, 1);
lean_dec(v_a_2131_);
lean_dec(v_acc_2113_);
lean_dec_ref(v_lhs_2111_);
v___x_2165_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1);
v___x_2166_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2165_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
return v___x_2166_;
}
}
else
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_dec(v_target_x3f_2132_);
lean_dec(v_a_2131_);
lean_dec(v_acc_2113_);
lean_dec_ref(v_lhs_2111_);
v___x_2167_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2);
v___x_2168_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2167_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
return v___x_2168_;
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
lean_dec(v_acc_2113_);
lean_dec_ref(v_lhs_2111_);
v_a_2169_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2130_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2130_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
else
{
lean_object* v___x_2177_; 
lean_dec_ref(v_lhs_2111_);
v___x_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2177_, 0, v_acc_2113_);
return v___x_2177_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1(void){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2179_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2180_ = lean_unsigned_to_nat(29u);
v___x_2181_ = lean_unsigned_to_nat(300u);
v___x_2182_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0));
v___x_2183_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2184_ = l_mkPanicMessageWithDecl(v___x_2183_, v___x_2182_, v___x_2181_, v___x_2180_, v___x_2179_);
return v___x_2184_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2(void){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2185_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2186_ = lean_unsigned_to_nat(35u);
v___x_2187_ = lean_unsigned_to_nat(299u);
v___x_2188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0));
v___x_2189_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2190_ = l_mkPanicMessageWithDecl(v___x_2189_, v___x_2188_, v___x_2187_, v___x_2186_, v___x_2185_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(lean_object* v_rhs_2191_, lean_object* v_common_2192_, lean_object* v_lhsEqCommon_x3f_2193_, uint8_t v_heq_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_){
_start:
{
size_t v___x_2206_; size_t v___x_2207_; uint8_t v___x_2208_; 
v___x_2206_ = lean_ptr_addr(v_rhs_2191_);
v___x_2207_ = lean_ptr_addr(v_common_2192_);
v___x_2208_ = lean_usize_dec_eq(v___x_2206_, v___x_2207_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = lean_st_ref_get(v_a_2195_);
lean_inc_ref(v_rhs_2191_);
v___x_2210_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2209_, v_rhs_2191_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
lean_dec(v___x_2209_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v_target_x3f_2212_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2211_);
lean_dec_ref_known(v___x_2210_, 1);
v_target_x3f_2212_ = lean_ctor_get(v_a_2211_, 4);
lean_inc(v_target_x3f_2212_);
if (lean_obj_tag(v_target_x3f_2212_) == 1)
{
lean_object* v_proof_x3f_2213_; 
v_proof_x3f_2213_ = lean_ctor_get(v_a_2211_, 5);
lean_inc(v_proof_x3f_2213_);
if (lean_obj_tag(v_proof_x3f_2213_) == 1)
{
uint8_t v_flipped_2214_; lean_object* v_val_2215_; lean_object* v_val_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2255_; 
v_flipped_2214_ = lean_ctor_get_uint8(v_a_2211_, sizeof(void*)*12);
lean_dec(v_a_2211_);
v_val_2215_ = lean_ctor_get(v_target_x3f_2212_, 0);
lean_inc(v_val_2215_);
lean_dec_ref_known(v_target_x3f_2212_, 1);
v_val_2216_ = lean_ctor_get(v_proof_x3f_2213_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v_proof_x3f_2213_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2218_ = v_proof_x3f_2213_;
v_isShared_2219_ = v_isSharedCheck_2255_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_val_2216_);
lean_dec(v_proof_x3f_2213_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2255_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
uint8_t v___y_2221_; 
if (v_flipped_2214_ == 0)
{
uint8_t v___x_2254_; 
v___x_2254_ = 1;
v___y_2221_ = v___x_2254_;
goto v___jp_2220_;
}
else
{
v___y_2221_ = v___x_2208_;
goto v___jp_2220_;
}
v___jp_2220_:
{
lean_object* v___x_2222_; 
lean_inc(v_val_2215_);
v___x_2222_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_val_2215_, v_rhs_2191_, v_val_2216_, v___y_2221_, v_heq_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v___x_2224_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_a_2223_);
lean_dec_ref_known(v___x_2222_, 1);
v___x_2224_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_val_2215_, v_common_2192_, v_lhsEqCommon_x3f_2193_, v_heq_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2226_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref_known(v___x_2224_, 1);
v___x_2226_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_a_2225_, v_a_2223_, v_heq_2194_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2237_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2229_ = v___x_2226_;
v_isShared_2230_ = v_isSharedCheck_2237_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2226_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2237_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 0, v_a_2227_);
v___x_2232_ = v___x_2218_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2234_; 
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2232_);
v___x_2234_ = v___x_2229_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_del_object(v___x_2218_);
v_a_2238_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2226_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2226_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
else
{
lean_dec(v_a_2223_);
lean_del_object(v___x_2218_);
return v___x_2224_;
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_del_object(v___x_2218_);
lean_dec(v_val_2215_);
lean_dec(v_lhsEqCommon_x3f_2193_);
v_a_2246_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2222_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2222_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
}
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
lean_dec(v_proof_x3f_2213_);
lean_dec_ref_known(v_target_x3f_2212_, 1);
lean_dec(v_a_2211_);
lean_dec(v_lhsEqCommon_x3f_2193_);
lean_dec_ref(v_rhs_2191_);
v___x_2256_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1);
v___x_2257_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2256_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
return v___x_2257_;
}
}
else
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
lean_dec(v_target_x3f_2212_);
lean_dec(v_a_2211_);
lean_dec(v_lhsEqCommon_x3f_2193_);
lean_dec_ref(v_rhs_2191_);
v___x_2258_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2);
v___x_2259_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2258_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
return v___x_2259_;
}
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
lean_dec(v_lhsEqCommon_x3f_2193_);
lean_dec_ref(v_rhs_2191_);
v_a_2260_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2210_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2210_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
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
else
{
lean_object* v___x_2268_; 
lean_dec_ref(v_rhs_2191_);
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v_lhsEqCommon_x3f_2193_);
return v___x_2268_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2269_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2270_ = lean_unsigned_to_nat(72u);
v___x_2271_ = lean_unsigned_to_nat(321u);
v___x_2272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0));
v___x_2273_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2274_ = l_mkPanicMessageWithDecl(v___x_2273_, v___x_2272_, v___x_2271_, v___x_2270_, v___x_2269_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(lean_object* v_lhs_2275_, lean_object* v_rhs_2276_, uint8_t v_heq_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
size_t v___x_2289_; size_t v___x_2290_; uint8_t v___x_2291_; 
v___x_2289_ = lean_ptr_addr(v_lhs_2275_);
v___x_2290_ = lean_ptr_addr(v_rhs_2276_);
v___x_2291_ = lean_usize_dec_eq(v___x_2289_, v___x_2290_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2292_; 
lean_inc_ref(v_lhs_2275_);
v___x_2292_ = l_Lean_Meta_Grind_getRootENode___redArg(v_lhs_2275_, v_a_2278_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; uint8_t v_heqProofs_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v___x_2292_, 1);
v_heqProofs_2294_ = lean_ctor_get_uint8(v_a_2293_, sizeof(void*)*12 + 4);
lean_dec(v_a_2293_);
v___x_2295_ = lean_st_ref_get(v_a_2278_);
lean_inc_ref(v_lhs_2275_);
v___x_2296_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2295_, v_lhs_2275_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
lean_dec(v___x_2295_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref_known(v___x_2296_, 1);
v___x_2298_ = lean_st_ref_get(v_a_2278_);
lean_inc_ref(v_rhs_2276_);
v___x_2299_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2298_, v_rhs_2276_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
lean_dec(v___x_2298_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v_root_2301_; lean_object* v_root_2302_; size_t v___x_2303_; size_t v___x_2304_; uint8_t v___x_2305_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v_root_2301_ = lean_ctor_get(v_a_2297_, 2);
lean_inc_ref(v_root_2301_);
lean_dec(v_a_2297_);
v_root_2302_ = lean_ctor_get(v_a_2300_, 2);
lean_inc_ref(v_root_2302_);
lean_dec(v_a_2300_);
v___x_2303_ = lean_ptr_addr(v_root_2301_);
lean_dec_ref(v_root_2301_);
v___x_2304_ = lean_ptr_addr(v_root_2302_);
lean_dec_ref(v_root_2302_);
v___x_2305_ = lean_usize_dec_eq(v___x_2303_, v___x_2304_);
if (v___x_2305_ == 0)
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
lean_dec_ref(v_rhs_2276_);
lean_dec_ref(v_lhs_2275_);
v___x_2306_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2);
v___x_2307_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2306_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_2307_;
}
else
{
lean_object* v___x_2308_; 
lean_inc_ref(v_rhs_2276_);
lean_inc_ref(v_lhs_2275_);
v___x_2308_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(v_lhs_2275_, v_rhs_2276_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2308_, 1);
v___x_2310_ = lean_box(0);
v___x_2311_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_2275_, v_a_2309_, v___x_2310_, v_heqProofs_2294_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2313_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2311_, 1);
v___x_2313_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_2276_, v_a_2309_, v_a_2312_, v_heqProofs_2294_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
lean_dec(v_a_2309_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2329_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2329_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2329_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
if (lean_obj_tag(v_a_2314_) == 1)
{
lean_object* v_val_2318_; uint8_t v___y_2323_; 
v_val_2318_ = lean_ctor_get(v_a_2314_, 0);
lean_inc(v_val_2318_);
lean_dec_ref_known(v_a_2314_, 1);
if (v_heqProofs_2294_ == 0)
{
if (v_heq_2277_ == 0)
{
v___y_2323_ = v___x_2305_;
goto v___jp_2322_;
}
else
{
lean_del_object(v___x_2316_);
goto v___jp_2319_;
}
}
else
{
v___y_2323_ = v_heq_2277_;
goto v___jp_2322_;
}
v___jp_2319_:
{
if (v_heq_2277_ == 0)
{
lean_object* v___x_2320_; 
v___x_2320_ = l_Lean_Meta_mkEqOfHEq(v_val_2318_, v_heq_2277_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_2320_;
}
else
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Lean_Meta_mkHEqOfEq(v_val_2318_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_2321_;
}
}
v___jp_2322_:
{
if (v___y_2323_ == 0)
{
lean_del_object(v___x_2316_);
goto v___jp_2319_;
}
else
{
lean_object* v___x_2325_; 
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v_val_2318_);
v___x_2325_ = v___x_2316_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_val_2318_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
lean_del_object(v___x_2316_);
lean_dec(v_a_2314_);
v___x_2327_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3);
v___x_2328_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2327_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_2328_;
}
}
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
v_a_2330_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2332_ = v___x_2313_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2313_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2330_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec(v_a_2309_);
lean_dec_ref(v_rhs_2276_);
v_a_2338_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2311_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2311_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
else
{
lean_dec_ref(v_rhs_2276_);
lean_dec_ref(v_lhs_2275_);
return v___x_2308_;
}
}
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec(v_a_2297_);
lean_dec_ref(v_rhs_2276_);
lean_dec_ref(v_lhs_2275_);
v_a_2346_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2299_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2299_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec_ref(v_rhs_2276_);
lean_dec_ref(v_lhs_2275_);
v_a_2354_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2296_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2296_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec_ref(v_rhs_2276_);
lean_dec_ref(v_lhs_2275_);
v_a_2362_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2292_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2292_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
else
{
lean_object* v___x_2370_; 
lean_dec_ref(v_rhs_2276_);
v___x_2370_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(v_lhs_2275_, v_heq_2277_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_2370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(lean_object* v_thm_2371_, lean_object* v_lhs_2372_, lean_object* v_rhs_2373_, lean_object* v_i_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v___x_2386_; uint8_t v___x_2387_; 
v___x_2386_ = lean_unsigned_to_nat(0u);
v___x_2387_ = lean_nat_dec_lt(v___x_2386_, v_i_2374_);
if (v___x_2387_ == 0)
{
lean_object* v_proof_2388_; lean_object* v___x_2389_; 
v_proof_2388_ = lean_ctor_get(v_thm_2371_, 1);
lean_inc_ref(v_proof_2388_);
v___x_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2389_, 0, v_proof_2388_);
return v___x_2389_;
}
else
{
uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v_i_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2390_ = 0;
v___x_2391_ = lean_unsigned_to_nat(1u);
v_i_2392_ = lean_nat_sub(v_i_2374_, v___x_2391_);
v___x_2393_ = l_Lean_Expr_appFn_x21(v_lhs_2372_);
v___x_2394_ = l_Lean_Expr_appFn_x21(v_rhs_2373_);
v___x_2395_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_2371_, v___x_2393_, v___x_2394_, v_i_2392_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_);
lean_dec_ref(v___x_2394_);
lean_dec_ref(v___x_2393_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v_argKinds_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; uint8_t v___y_2401_; lean_object* v___x_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2396_);
lean_dec_ref_known(v___x_2395_, 1);
v_argKinds_2397_ = lean_ctor_get(v_thm_2371_, 2);
v___x_2398_ = l_Lean_Expr_appArg_x21(v_lhs_2372_);
v___x_2399_ = l_Lean_Expr_appArg_x21(v_rhs_2373_);
v___x_2412_ = lean_box(v___x_2390_);
v___x_2413_ = lean_array_get(v___x_2412_, v_argKinds_2397_, v_i_2392_);
lean_dec(v_i_2392_);
lean_dec(v___x_2412_);
v___x_2414_ = lean_unbox(v___x_2413_);
lean_dec(v___x_2413_);
if (v___x_2414_ == 4)
{
v___y_2401_ = v___x_2387_;
goto v___jp_2400_;
}
else
{
uint8_t v___x_2415_; 
v___x_2415_ = 0;
v___y_2401_ = v___x_2415_;
goto v___jp_2400_;
}
v___jp_2400_:
{
lean_object* v___x_2402_; 
lean_inc_ref(v___x_2399_);
lean_inc_ref(v___x_2398_);
v___x_2402_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___x_2398_, v___x_2399_, v___y_2401_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2411_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2405_ = v___x_2402_;
v_isShared_2406_ = v_isSharedCheck_2411_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2402_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2411_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2407_ = l_Lean_mkApp3(v_a_2396_, v___x_2398_, v___x_2399_, v_a_2403_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v___x_2407_);
v___x_2409_ = v___x_2405_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
else
{
lean_dec_ref(v___x_2399_);
lean_dec_ref(v___x_2398_);
lean_dec(v_a_2396_);
return v___x_2402_;
}
}
}
else
{
lean_dec(v_i_2392_);
return v___x_2395_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(lean_object* v_f_2419_, lean_object* v_g_2420_, lean_object* v_numArgs_2421_, lean_object* v_lhs_2422_, lean_object* v_rhs_2423_, uint8_t v_heq_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v___x_2436_; 
lean_inc(v_numArgs_2421_);
lean_inc_ref(v_f_2419_);
v___x_2436_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(v_f_2419_, v_numArgs_2421_, v_a_2428_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v_argKinds_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_a_2437_);
lean_dec_ref_known(v___x_2436_, 1);
v_argKinds_2438_ = lean_ctor_get(v_a_2437_, 2);
v___x_2439_ = lean_array_get_size(v_argKinds_2438_);
v___x_2440_ = lean_nat_dec_eq(v___x_2439_, v_numArgs_2421_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
lean_dec(v_a_2437_);
lean_dec_ref(v_rhs_2423_);
lean_dec_ref(v_lhs_2422_);
lean_dec(v_numArgs_2421_);
lean_dec_ref(v_g_2420_);
lean_dec_ref(v_f_2419_);
v___x_2441_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2);
v___x_2442_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2441_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
return v___x_2442_;
}
else
{
lean_object* v___x_2443_; 
v___x_2443_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_2437_, v_lhs_2422_, v_rhs_2423_, v_numArgs_2421_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
lean_dec(v_a_2437_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; size_t v___x_2445_; size_t v___x_2446_; uint8_t v___x_2447_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v___x_2443_, 1);
v___x_2445_ = lean_ptr_addr(v_f_2419_);
v___x_2446_ = lean_ptr_addr(v_g_2420_);
v___x_2447_ = lean_usize_dec_eq(v___x_2445_, v___x_2446_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___f_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2448_ = lean_box(v___x_2447_);
v___x_2449_ = lean_box(v___x_2440_);
v___f_2450_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___boxed), 17, 5);
lean_closure_set(v___f_2450_, 0, v_numArgs_2421_);
lean_closure_set(v___f_2450_, 1, v_rhs_2423_);
lean_closure_set(v___f_2450_, 2, v_lhs_2422_);
lean_closure_set(v___f_2450_, 3, v___x_2448_);
lean_closure_set(v___f_2450_, 4, v___x_2449_);
v___x_2451_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__4));
v___x_2452_ = l_Lean_Core_mkFreshUserName(v___x_2451_, v_a_2433_, v_a_2434_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2454_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
lean_dec_ref_known(v___x_2452_, 1);
lean_inc(v_a_2434_);
lean_inc_ref(v_a_2433_);
lean_inc(v_a_2432_);
lean_inc_ref(v_a_2431_);
lean_inc_ref(v_f_2419_);
v___x_2454_ = lean_infer_type(v_f_2419_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2456_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
lean_dec_ref_known(v___x_2454_, 1);
v___x_2456_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_a_2453_, v_a_2455_, v___f_2450_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2458_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
lean_dec_ref_known(v___x_2456_, 1);
v___x_2458_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_f_2419_, v_g_2420_, v___x_2447_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2460_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___x_2458_, 1);
v___x_2460_ = l_Lean_Meta_mkEqNDRec(v_a_2457_, v_a_2444_, v_a_2459_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2462_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2461_);
lean_dec_ref_known(v___x_2460_, 1);
v___x_2462_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_2461_, v_heq_2424_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
return v___x_2462_;
}
else
{
return v___x_2460_;
}
}
else
{
lean_dec(v_a_2457_);
lean_dec(v_a_2444_);
return v___x_2458_;
}
}
else
{
lean_dec(v_a_2444_);
lean_dec_ref(v_g_2420_);
lean_dec_ref(v_f_2419_);
return v___x_2456_;
}
}
else
{
lean_dec(v_a_2453_);
lean_dec_ref(v___f_2450_);
lean_dec(v_a_2444_);
lean_dec_ref(v_g_2420_);
lean_dec_ref(v_f_2419_);
return v___x_2454_;
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec_ref(v___f_2450_);
lean_dec(v_a_2444_);
lean_dec_ref(v_g_2420_);
lean_dec_ref(v_f_2419_);
v_a_2463_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2452_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2452_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
else
{
lean_object* v___x_2471_; 
lean_dec_ref(v_rhs_2423_);
lean_dec_ref(v_lhs_2422_);
lean_dec(v_numArgs_2421_);
lean_dec_ref(v_g_2420_);
lean_dec_ref(v_f_2419_);
v___x_2471_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_2444_, v_heq_2424_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
return v___x_2471_;
}
}
else
{
lean_dec_ref(v_rhs_2423_);
lean_dec_ref(v_lhs_2422_);
lean_dec(v_numArgs_2421_);
lean_dec_ref(v_g_2420_);
lean_dec_ref(v_f_2419_);
return v___x_2443_;
}
}
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_dec_ref(v_rhs_2423_);
lean_dec_ref(v_lhs_2422_);
lean_dec(v_numArgs_2421_);
lean_dec_ref(v_g_2420_);
lean_dec_ref(v_f_2419_);
v_a_2472_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2436_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2436_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1(void){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2481_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2482_ = lean_unsigned_to_nat(27u);
v___x_2483_ = lean_unsigned_to_nat(237u);
v___x_2484_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0));
v___x_2485_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2486_ = l_mkPanicMessageWithDecl(v___x_2485_, v___x_2484_, v___x_2483_, v___x_2482_, v___x_2481_);
return v___x_2486_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2(void){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2487_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2488_ = lean_unsigned_to_nat(27u);
v___x_2489_ = lean_unsigned_to_nat(236u);
v___x_2490_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0));
v___x_2491_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2492_ = l_mkPanicMessageWithDecl(v___x_2491_, v___x_2490_, v___x_2489_, v___x_2488_, v___x_2487_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(lean_object* v_lhs_2493_, lean_object* v_rhs_2494_, uint8_t v_heq_2495_, lean_object* v_e_u2081_2496_, lean_object* v_e_u2082_2497_, lean_object* v_numArgs_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
if (lean_obj_tag(v_e_u2081_2496_) == 5)
{
if (lean_obj_tag(v_e_u2082_2497_) == 5)
{
lean_object* v_fn_2510_; lean_object* v_fn_2511_; lean_object* v___x_2512_; lean_object* v_numArgs_2513_; size_t v___x_2514_; size_t v___x_2515_; uint8_t v___x_2516_; 
v_fn_2510_ = lean_ctor_get(v_e_u2081_2496_, 0);
lean_inc_ref(v_fn_2510_);
lean_dec_ref_known(v_e_u2081_2496_, 2);
v_fn_2511_ = lean_ctor_get(v_e_u2082_2497_, 0);
lean_inc_ref(v_fn_2511_);
lean_dec_ref_known(v_e_u2082_2497_, 2);
v___x_2512_ = lean_unsigned_to_nat(1u);
v_numArgs_2513_ = lean_nat_add(v_numArgs_2498_, v___x_2512_);
lean_dec(v_numArgs_2498_);
v___x_2514_ = lean_ptr_addr(v_fn_2510_);
v___x_2515_ = lean_ptr_addr(v_fn_2511_);
v___x_2516_ = lean_usize_dec_eq(v___x_2514_, v___x_2515_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; 
lean_inc_ref(v_fn_2511_);
lean_inc_ref(v_fn_2510_);
v___x_2517_ = l_Lean_Meta_Grind_hasSameType(v_fn_2510_, v_fn_2511_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; uint8_t v___x_2519_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2518_);
lean_dec_ref_known(v___x_2517_, 1);
v___x_2519_ = lean_unbox(v_a_2518_);
lean_dec(v_a_2518_);
if (v___x_2519_ == 0)
{
v_e_u2081_2496_ = v_fn_2510_;
v_e_u2082_2497_ = v_fn_2511_;
v_numArgs_2498_ = v_numArgs_2513_;
goto _start;
}
else
{
lean_object* v___x_2521_; 
v___x_2521_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_2510_, v_fn_2511_, v_numArgs_2513_, v_lhs_2493_, v_rhs_2494_, v_heq_2495_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
return v___x_2521_;
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_dec(v_numArgs_2513_);
lean_dec_ref(v_fn_2511_);
lean_dec_ref(v_fn_2510_);
lean_dec_ref(v_rhs_2494_);
lean_dec_ref(v_lhs_2493_);
v_a_2522_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2517_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2517_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
else
{
lean_object* v___x_2530_; 
v___x_2530_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_2510_, v_fn_2511_, v_numArgs_2513_, v_lhs_2493_, v_rhs_2494_, v_heq_2495_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
return v___x_2530_;
}
}
else
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
lean_dec_ref_known(v_e_u2081_2496_, 2);
lean_dec(v_numArgs_2498_);
lean_dec_ref(v_e_u2082_2497_);
lean_dec_ref(v_rhs_2494_);
lean_dec_ref(v_lhs_2493_);
v___x_2531_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1);
v___x_2532_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2531_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
return v___x_2532_;
}
}
else
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
lean_dec(v_numArgs_2498_);
lean_dec_ref(v_e_u2082_2497_);
lean_dec_ref(v_e_u2081_2496_);
lean_dec_ref(v_rhs_2494_);
lean_dec_ref(v_lhs_2493_);
v___x_2533_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2);
v___x_2534_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2533_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
return v___x_2534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(lean_object* v_lhs_2535_, lean_object* v_rhs_2536_, uint8_t v_heq_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2549_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_rhs_2536_);
lean_inc_ref(v_lhs_2535_);
v___x_2550_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(v_lhs_2535_, v_rhs_2536_, v_heq_2537_, v_lhs_2535_, v_rhs_2536_, v___x_2549_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC___boxed(lean_object* v_lhs_2551_, lean_object* v_rhs_2552_, lean_object* v_heq_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_){
_start:
{
uint8_t v_heq_boxed_2565_; lean_object* v_res_2566_; 
v_heq_boxed_2565_ = lean_unbox(v_heq_2553_);
v_res_2566_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_2551_, v_rhs_2552_, v_heq_boxed_2565_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
lean_dec(v_a_2563_);
lean_dec_ref(v_a_2562_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
lean_dec(v_a_2555_);
lean_dec(v_a_2554_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___boxed(lean_object* v_lhs_2567_, lean_object* v_rhs_2568_, lean_object* v_heq_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_){
_start:
{
uint8_t v_heq_boxed_2581_; lean_object* v_res_2582_; 
v_heq_boxed_2581_ = lean_unbox(v_heq_2569_);
v_res_2582_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_2567_, v_rhs_2568_, v_heq_boxed_2581_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
lean_dec(v_a_2571_);
lean_dec(v_a_2570_);
lean_dec_ref(v_rhs_2568_);
lean_dec_ref(v_lhs_2567_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___boxed(lean_object* v_lhs_2583_, lean_object* v_rhs_2584_, lean_object* v_heq_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_){
_start:
{
uint8_t v_heq_boxed_2597_; lean_object* v_res_2598_; 
v_heq_boxed_2597_ = lean_unbox(v_heq_2585_);
v_res_2598_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_2583_, v_rhs_2584_, v_heq_boxed_2597_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_);
lean_dec(v_a_2595_);
lean_dec_ref(v_a_2594_);
lean_dec(v_a_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_a_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_a_2589_);
lean_dec_ref(v_a_2588_);
lean_dec(v_a_2587_);
lean_dec(v_a_2586_);
lean_dec_ref(v_rhs_2584_);
lean_dec_ref(v_lhs_2583_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof___boxed(lean_object* v_lhs_2599_, lean_object* v_rhs_2600_, lean_object* v_h_2601_, lean_object* v_flipped_2602_, lean_object* v_heq_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_){
_start:
{
uint8_t v_flipped_boxed_2615_; uint8_t v_heq_boxed_2616_; lean_object* v_res_2617_; 
v_flipped_boxed_2615_ = lean_unbox(v_flipped_2602_);
v_heq_boxed_2616_ = lean_unbox(v_heq_2603_);
v_res_2617_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_lhs_2599_, v_rhs_2600_, v_h_2601_, v_flipped_boxed_2615_, v_heq_boxed_2616_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_);
lean_dec(v_a_2613_);
lean_dec_ref(v_a_2612_);
lean_dec(v_a_2611_);
lean_dec_ref(v_a_2610_);
lean_dec(v_a_2609_);
lean_dec_ref(v_a_2608_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
lean_dec(v_a_2605_);
lean_dec(v_a_2604_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___boxed(lean_object* v_lhs_2618_, lean_object* v_rhs_2619_, lean_object* v_heq_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
uint8_t v_heq_boxed_2632_; lean_object* v_res_2633_; 
v_heq_boxed_2632_ = lean_unbox(v_heq_2620_);
v_res_2633_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_2618_, v_rhs_2619_, v_heq_boxed_2632_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
lean_dec(v_a_2626_);
lean_dec_ref(v_a_2625_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
lean_dec(v_a_2622_);
lean_dec(v_a_2621_);
lean_dec_ref(v_rhs_2619_);
lean_dec_ref(v_lhs_2618_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper___boxed(lean_object* v_thm_2634_, lean_object* v_lhs_2635_, lean_object* v_rhs_2636_, lean_object* v_i_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_2634_, v_lhs_2635_, v_rhs_2636_, v_i_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
lean_dec(v_a_2639_);
lean_dec(v_a_2638_);
lean_dec(v_i_2637_);
lean_dec_ref(v_rhs_2636_);
lean_dec_ref(v_lhs_2635_);
lean_dec_ref(v_thm_2634_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___boxed(lean_object** _args){
lean_object* v_lhs_2650_ = _args[0];
lean_object* v_rhs_2651_ = _args[1];
lean_object* v_heq_2652_ = _args[2];
lean_object* v_e_u2081_2653_ = _args[3];
lean_object* v_e_u2082_2654_ = _args[4];
lean_object* v_numArgs_2655_ = _args[5];
lean_object* v_a_2656_ = _args[6];
lean_object* v_a_2657_ = _args[7];
lean_object* v_a_2658_ = _args[8];
lean_object* v_a_2659_ = _args[9];
lean_object* v_a_2660_ = _args[10];
lean_object* v_a_2661_ = _args[11];
lean_object* v_a_2662_ = _args[12];
lean_object* v_a_2663_ = _args[13];
lean_object* v_a_2664_ = _args[14];
lean_object* v_a_2665_ = _args[15];
lean_object* v_a_2666_ = _args[16];
_start:
{
uint8_t v_heq_boxed_2667_; lean_object* v_res_2668_; 
v_heq_boxed_2667_ = lean_unbox(v_heq_2652_);
v_res_2668_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(v_lhs_2650_, v_rhs_2651_, v_heq_boxed_2667_, v_e_u2081_2653_, v_e_u2082_2654_, v_numArgs_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec(v_a_2656_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___boxed(lean_object* v_lhs_2669_, lean_object* v_common_2670_, lean_object* v_acc_2671_, lean_object* v_heq_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
uint8_t v_heq_boxed_2684_; lean_object* v_res_2685_; 
v_heq_boxed_2684_ = lean_unbox(v_heq_2672_);
v_res_2685_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_2669_, v_common_2670_, v_acc_2671_, v_heq_boxed_2684_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
lean_dec_ref(v_a_2675_);
lean_dec(v_a_2674_);
lean_dec(v_a_2673_);
lean_dec_ref(v_common_2670_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___boxed(lean_object** _args){
lean_object* v_f_2686_ = _args[0];
lean_object* v_g_2687_ = _args[1];
lean_object* v_numArgs_2688_ = _args[2];
lean_object* v_lhs_2689_ = _args[3];
lean_object* v_rhs_2690_ = _args[4];
lean_object* v_heq_2691_ = _args[5];
lean_object* v_a_2692_ = _args[6];
lean_object* v_a_2693_ = _args[7];
lean_object* v_a_2694_ = _args[8];
lean_object* v_a_2695_ = _args[9];
lean_object* v_a_2696_ = _args[10];
lean_object* v_a_2697_ = _args[11];
lean_object* v_a_2698_ = _args[12];
lean_object* v_a_2699_ = _args[13];
lean_object* v_a_2700_ = _args[14];
lean_object* v_a_2701_ = _args[15];
lean_object* v_a_2702_ = _args[16];
_start:
{
uint8_t v_heq_boxed_2703_; lean_object* v_res_2704_; 
v_heq_boxed_2703_ = lean_unbox(v_heq_2691_);
v_res_2704_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_2686_, v_g_2687_, v_numArgs_2688_, v_lhs_2689_, v_rhs_2690_, v_heq_boxed_2703_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_);
lean_dec(v_a_2701_);
lean_dec_ref(v_a_2700_);
lean_dec(v_a_2699_);
lean_dec_ref(v_a_2698_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
lean_dec(v_a_2693_);
lean_dec(v_a_2692_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___boxed(lean_object* v_rhs_2705_, lean_object* v_common_2706_, lean_object* v_lhsEqCommon_x3f_2707_, lean_object* v_heq_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
uint8_t v_heq_boxed_2720_; lean_object* v_res_2721_; 
v_heq_boxed_2720_ = lean_unbox(v_heq_2708_);
v_res_2721_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_2705_, v_common_2706_, v_lhsEqCommon_x3f_2707_, v_heq_boxed_2720_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_);
lean_dec(v_a_2718_);
lean_dec_ref(v_a_2717_);
lean_dec(v_a_2716_);
lean_dec_ref(v_a_2715_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec(v_a_2710_);
lean_dec(v_a_2709_);
lean_dec_ref(v_common_2706_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___boxed(lean_object* v_lhs_2722_, lean_object* v_rhs_2723_, lean_object* v_heq_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_){
_start:
{
uint8_t v_heq_boxed_2736_; lean_object* v_res_2737_; 
v_heq_boxed_2736_ = lean_unbox(v_heq_2724_);
v_res_2737_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_2722_, v_rhs_2723_, v_heq_boxed_2736_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
lean_dec(v_a_2732_);
lean_dec_ref(v_a_2731_);
lean_dec(v_a_2730_);
lean_dec_ref(v_a_2729_);
lean_dec(v_a_2728_);
lean_dec_ref(v_a_2727_);
lean_dec(v_a_2726_);
lean_dec(v_a_2725_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop___boxed(lean_object* v_lhs_2738_, lean_object* v_rhs_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_2738_, v_rhs_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_);
lean_dec(v_a_2749_);
lean_dec_ref(v_a_2748_);
lean_dec(v_a_2747_);
lean_dec_ref(v_a_2746_);
lean_dec(v_a_2745_);
lean_dec_ref(v_a_2744_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
lean_dec(v_a_2741_);
lean_dec(v_a_2740_);
lean_dec_ref(v_rhs_2739_);
lean_dec_ref(v_lhs_2738_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___boxed(lean_object* v_lhs_2752_, lean_object* v_rhs_2753_, lean_object* v_heq_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_){
_start:
{
uint8_t v_heq_boxed_2766_; lean_object* v_res_2767_; 
v_heq_boxed_2766_ = lean_unbox(v_heq_2754_);
v_res_2767_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_lhs_2752_, v_rhs_2753_, v_heq_boxed_2766_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_);
lean_dec(v_a_2764_);
lean_dec_ref(v_a_2763_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2761_);
lean_dec(v_a_2760_);
lean_dec_ref(v_a_2759_);
lean_dec(v_a_2758_);
lean_dec_ref(v_a_2757_);
lean_dec(v_a_2756_);
lean_dec(v_a_2755_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrProof___boxed(lean_object* v_lhs_2768_, lean_object* v_rhs_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Lean_Meta_Grind_mkEqCongrProof(v_lhs_2768_, v_rhs_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
lean_dec(v_a_2779_);
lean_dec_ref(v_a_2778_);
lean_dec(v_a_2777_);
lean_dec_ref(v_a_2776_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec(v_a_2770_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___boxed(lean_object* v_lhs_2782_, lean_object* v_rhs_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(v_lhs_2782_, v_rhs_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
lean_dec(v_a_2793_);
lean_dec_ref(v_a_2792_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
lean_dec(v_a_2787_);
lean_dec_ref(v_a_2786_);
lean_dec(v_a_2785_);
lean_dec(v_a_2784_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___boxed(lean_object* v_lhs_2796_, lean_object* v_rhs_2797_, lean_object* v_heq_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_){
_start:
{
uint8_t v_heq_boxed_2810_; lean_object* v_res_2811_; 
v_heq_boxed_2810_ = lean_unbox(v_heq_2798_);
v_res_2811_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(v_lhs_2796_, v_rhs_2797_, v_heq_boxed_2810_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
lean_dec(v_a_2808_);
lean_dec_ref(v_a_2807_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
lean_dec(v_a_2800_);
lean_dec(v_a_2799_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(lean_object* v_00_u03b1_2812_, lean_object* v_ref_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_2813_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___boxed(lean_object* v_00_u03b1_2826_, lean_object* v_ref_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(v_00_u03b1_2826_, v_ref_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec(v___y_2828_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(lean_object* v_00_u03b1_2840_, lean_object* v_name_2841_, uint8_t v_bi_2842_, lean_object* v_type_2843_, lean_object* v_k_2844_, uint8_t v_kind_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v___x_2857_; 
v___x_2857_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_2841_, v_bi_2842_, v_type_2843_, v_k_2844_, v_kind_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___boxed(lean_object** _args){
lean_object* v_00_u03b1_2858_ = _args[0];
lean_object* v_name_2859_ = _args[1];
lean_object* v_bi_2860_ = _args[2];
lean_object* v_type_2861_ = _args[3];
lean_object* v_k_2862_ = _args[4];
lean_object* v_kind_2863_ = _args[5];
lean_object* v___y_2864_ = _args[6];
lean_object* v___y_2865_ = _args[7];
lean_object* v___y_2866_ = _args[8];
lean_object* v___y_2867_ = _args[9];
lean_object* v___y_2868_ = _args[10];
lean_object* v___y_2869_ = _args[11];
lean_object* v___y_2870_ = _args[12];
lean_object* v___y_2871_ = _args[13];
lean_object* v___y_2872_ = _args[14];
lean_object* v___y_2873_ = _args[15];
lean_object* v___y_2874_ = _args[16];
_start:
{
uint8_t v_bi_boxed_2875_; uint8_t v_kind_boxed_2876_; lean_object* v_res_2877_; 
v_bi_boxed_2875_ = lean_unbox(v_bi_2860_);
v_kind_boxed_2876_ = lean_unbox(v_kind_2863_);
v_res_2877_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(v_00_u03b1_2858_, v_name_2859_, v_bi_boxed_2875_, v_type_2861_, v_k_2862_, v_kind_boxed_2876_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(lean_object* v_00_u03b1_2878_, lean_object* v_name_2879_, lean_object* v_type_2880_, lean_object* v_k_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_name_2879_, v_type_2880_, v_k_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___boxed(lean_object* v_00_u03b1_2894_, lean_object* v_name_2895_, lean_object* v_type_2896_, lean_object* v_k_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(v_00_u03b1_2894_, v_name_2895_, v_type_2896_, v_k_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec(v___y_2898_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(lean_object* v_00_u03b1_2910_, lean_object* v_msg_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v_msg_2911_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___boxed(lean_object* v_00_u03b1_2924_, lean_object* v_msg_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(v_00_u03b1_2924_, v_msg_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec(v___y_2926_);
return v_res_2937_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__1(void){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__0));
v___x_2940_ = l_Lean_stringToMessageData(v___x_2939_);
return v___x_2940_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__3(void){
_start:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__2));
v___x_2943_ = l_Lean_stringToMessageData(v___x_2942_);
return v___x_2943_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__5(void){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2945_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__4));
v___x_2946_ = l_Lean_stringToMessageData(v___x_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* lean_grind_mk_eq_proof(lean_object* v_a_2947_, lean_object* v_b_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_){
_start:
{
lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___x_2973_; 
lean_inc_ref(v_b_2948_);
lean_inc_ref(v_a_2947_);
v___x_2973_ = l_Lean_Meta_Grind_hasSameType(v_a_2947_, v_b_2948_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; uint8_t v___x_2975_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_a_2974_);
lean_dec_ref_known(v___x_2973_, 1);
v___x_2975_ = lean_unbox(v_a_2974_);
lean_dec(v_a_2974_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; 
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
lean_dec(v_a_2952_);
lean_dec_ref(v_a_2951_);
lean_dec(v_a_2950_);
lean_dec(v_a_2949_);
lean_inc(v_a_2958_);
lean_inc_ref(v_a_2957_);
lean_inc(v_a_2956_);
lean_inc_ref(v_a_2955_);
lean_inc_ref(v_a_2947_);
v___x_2976_ = lean_infer_type(v_a_2947_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v_a_2977_; lean_object* v___x_2978_; 
v_a_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc(v_a_2977_);
lean_dec_ref_known(v___x_2976_, 1);
lean_inc(v_a_2958_);
lean_inc_ref(v_a_2957_);
lean_inc(v_a_2956_);
lean_inc_ref(v_a_2955_);
lean_inc_ref(v_b_2948_);
v___x_2978_ = lean_infer_type(v_b_2948_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2978_, 1);
v___x_2980_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__1, &l_Lean_Meta_Grind_mkEqProofImpl___closed__1_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__1);
v___x_2981_ = l_Lean_indentExpr(v_a_2947_);
v___x_2982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2980_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
v___x_2983_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__3, &l_Lean_Meta_Grind_mkEqProofImpl___closed__3_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__3);
v___x_2984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2982_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
v___x_2985_ = l_Lean_indentExpr(v_a_2977_);
v___x_2986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2984_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
v___x_2987_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__5, &l_Lean_Meta_Grind_mkEqProofImpl___closed__5_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__5);
v___x_2988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2986_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
v___x_2989_ = l_Lean_indentExpr(v_b_2948_);
v___x_2990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2988_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
v___x_2991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
lean_ctor_set(v___x_2991_, 1, v___x_2983_);
v___x_2992_ = l_Lean_indentExpr(v_a_2979_);
v___x_2993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2991_);
lean_ctor_set(v___x_2993_, 1, v___x_2992_);
v___x_2994_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v___x_2993_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2994_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2994_);
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
else
{
lean_dec(v_a_2977_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec_ref(v_b_2948_);
lean_dec_ref(v_a_2947_);
return v___x_2978_;
}
}
else
{
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec_ref(v_b_2948_);
lean_dec_ref(v_a_2947_);
return v___x_2976_;
}
}
else
{
v___y_2961_ = v_a_2949_;
v___y_2962_ = v_a_2950_;
v___y_2963_ = v_a_2951_;
v___y_2964_ = v_a_2952_;
v___y_2965_ = v_a_2953_;
v___y_2966_ = v_a_2954_;
v___y_2967_ = v_a_2955_;
v___y_2968_ = v_a_2956_;
v___y_2969_ = v_a_2957_;
v___y_2970_ = v_a_2958_;
goto v___jp_2960_;
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
lean_dec(v_a_2952_);
lean_dec_ref(v_a_2951_);
lean_dec(v_a_2950_);
lean_dec(v_a_2949_);
lean_dec_ref(v_b_2948_);
lean_dec_ref(v_a_2947_);
v_a_3003_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2973_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2973_);
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
v___jp_2960_:
{
uint8_t v___x_2971_; lean_object* v___x_2972_; 
v___x_2971_ = 0;
v___x_2972_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_2947_, v_b_2948_, v___x_2971_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec(v___y_2962_);
lean_dec(v___y_2961_);
return v___x_2972_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqProofImpl___boxed(lean_object* v_a_3011_, lean_object* v_b_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = lean_grind_mk_eq_proof(v_a_3011_, v_b_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* lean_grind_mk_heq_proof(lean_object* v_a_3025_, lean_object* v_b_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
uint8_t v___x_3038_; lean_object* v___x_3039_; 
v___x_3038_ = 1;
v___x_3039_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_3025_, v_b_3026_, v___x_3038_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
lean_dec(v_a_3036_);
lean_dec_ref(v_a_3035_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
lean_dec(v_a_3028_);
lean_dec(v_a_3027_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHEqProofImpl___boxed(lean_object* v_a_3040_, lean_object* v_b_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = lean_grind_mk_heq_proof(v_a_3040_, v_b_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_);
return v_res_3053_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Proof(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Proof(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Grind_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Proof(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Proof(builtin);
}
#ifdef __cplusplus
}
#endif
