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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof(lean_object* v_h_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_4_ = stack[0].m_obj;
lean_object* v_a_5_ = stack[1].m_obj;
lean_object* v_a_6_ = stack[2].m_obj;
lean_object* v_a_7_ = stack[3].m_obj;
lean_object* v_a_8_ = stack[4].m_obj;
lean_object* v_res_40_;
v_res_40_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof(v_h_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_);
stack->m_obj
 = v_res_40_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___boxed(lean_object* v_h_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof(v_h_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_);
lean_dec(v_a_45_);
lean_dec_ref(v_a_44_);
lean_dec(v_a_43_);
lean_dec_ref(v_a_42_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(lean_object* v_a_48_, lean_object* v_b_49_){
_start:
{
size_t v___x_50_; size_t v___x_51_; uint8_t v___x_52_; 
v___x_50_ = lean_ptr_addr(v_a_48_);
v___x_51_ = lean_ptr_addr(v_b_49_);
v___x_52_ = lean_usize_dec_eq(v___x_50_, v___x_51_);
if (v___x_52_ == 0)
{
uint8_t v___x_53_; 
v___x_53_ = l_Lean_Expr_isApp(v_a_48_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; 
lean_dec_ref(v_a_48_);
v___x_54_ = lean_box(0);
return v___x_54_;
}
else
{
uint8_t v___x_55_; 
v___x_55_ = l_Lean_Expr_isApp(v_b_49_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; 
lean_dec_ref(v_a_48_);
v___x_56_ = lean_box(0);
return v___x_56_;
}
else
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = l_Lean_Expr_appFn_x21(v_a_48_);
lean_dec_ref(v_a_48_);
v___x_58_ = l_Lean_Expr_appFn_x21(v_b_49_);
v___x_59_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(v___x_57_, v___x_58_);
lean_dec_ref(v___x_58_);
if (lean_obj_tag(v___x_59_) == 1)
{
lean_object* v_val_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_78_; 
v_val_60_ = lean_ctor_get(v___x_59_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_78_ == 0)
{
v___x_62_ = v___x_59_;
v_isShared_63_ = v_isSharedCheck_78_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_val_60_);
lean_dec(v___x_59_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_78_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v_fst_64_; lean_object* v_snd_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_77_; 
v_fst_64_ = lean_ctor_get(v_val_60_, 0);
v_snd_65_ = lean_ctor_get(v_val_60_, 1);
v_isSharedCheck_77_ = !lean_is_exclusive(v_val_60_);
if (v_isSharedCheck_77_ == 0)
{
v___x_67_ = v_val_60_;
v_isShared_68_ = v_isSharedCheck_77_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_snd_65_);
lean_inc(v_fst_64_);
lean_dec(v_val_60_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_77_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_69_ = lean_unsigned_to_nat(1u);
v___x_70_ = lean_nat_add(v_snd_65_, v___x_69_);
lean_dec(v_snd_65_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 1, v___x_70_);
v___x_72_ = v___x_67_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_fst_64_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v___x_70_);
v___x_72_ = v_reuseFailAlloc_76_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_74_; 
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 0, v___x_72_);
v___x_74_ = v___x_62_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
}
else
{
lean_object* v___x_79_; 
lean_dec(v___x_59_);
v___x_79_ = lean_box(0);
return v___x_79_;
}
}
}
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_81_, 0, v_a_48_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v___x_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix___boxed(lean_object* v_a_83_, lean_object* v_b_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(v_a_83_, v_b_84_);
lean_dec_ref(v_b_84_);
return v_res_85_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(lean_object* v_h_86_, uint8_t v_flipped_87_, uint8_t v_heq_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_h_x27_95_; lean_object* v___y_96_; lean_object* v___y_97_; lean_object* v___y_98_; lean_object* v___y_99_; 
if (v_heq_88_ == 0)
{
v_h_x27_95_ = v_h_86_;
v___y_96_ = v_a_89_;
v___y_97_ = v_a_90_;
v___y_98_ = v_a_91_;
v___y_99_ = v_a_92_;
goto v___jp_94_;
}
else
{
lean_object* v___x_103_; 
lean_inc_ref(v_h_86_);
v___x_103_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof(v_h_86_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; uint8_t v___x_105_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_a_104_);
lean_dec_ref_known(v___x_103_, 1);
v___x_105_ = lean_unbox(v_a_104_);
lean_dec(v_a_104_);
if (v___x_105_ == 0)
{
v_h_x27_95_ = v_h_86_;
v___y_96_ = v_a_89_;
v___y_97_ = v_a_90_;
v___y_98_ = v_a_91_;
v___y_99_ = v_a_92_;
goto v___jp_94_;
}
else
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_mkHEqOfEq(v_h_86_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_a_107_);
lean_dec_ref_known(v___x_106_, 1);
v_h_x27_95_ = v_a_107_;
v___y_96_ = v_a_89_;
v___y_97_ = v_a_90_;
v___y_98_ = v_a_91_;
v___y_99_ = v_a_92_;
goto v___jp_94_;
}
else
{
return v___x_106_;
}
}
}
else
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_115_; 
lean_dec_ref(v_h_86_);
v_a_108_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_115_ == 0)
{
v___x_110_ = v___x_103_;
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_103_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_113_; 
if (v_isShared_111_ == 0)
{
v___x_113_ = v___x_110_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_108_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
v___jp_94_:
{
if (v_flipped_87_ == 0)
{
lean_object* v___x_100_; 
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v_h_x27_95_);
return v___x_100_;
}
else
{
if (v_heq_88_ == 0)
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_Meta_mkEqSymm(v_h_x27_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
return v___x_101_;
}
else
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Meta_mkHEqSymm(v_h_x27_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
return v___x_102_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_86_ = stack[0].m_obj;
uint8_t v_flipped_87_ = stack[1].m_num;
uint8_t v_heq_88_ = stack[2].m_num;
lean_object* v_a_89_ = stack[3].m_obj;
lean_object* v_a_90_ = stack[4].m_obj;
lean_object* v_a_91_ = stack[5].m_obj;
lean_object* v_a_92_ = stack[6].m_obj;
lean_object* v_res_116_;
v_res_116_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(v_h_86_, v_flipped_87_, v_heq_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
stack->m_obj
 = v_res_116_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof___boxed(lean_object* v_h_117_, lean_object* v_flipped_118_, lean_object* v_heq_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
uint8_t v_flipped_boxed_125_; uint8_t v_heq_boxed_126_; lean_object* v_res_127_; 
v_flipped_boxed_125_ = lean_unbox(v_flipped_118_);
v_heq_boxed_126_ = lean_unbox(v_heq_119_);
v_res_127_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(v_h_117_, v_flipped_boxed_125_, v_heq_boxed_126_, v_a_120_, v_a_121_, v_a_122_, v_a_123_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
return v_res_127_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(lean_object* v_a_128_, uint8_t v_heq_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
if (v_heq_129_ == 0)
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Meta_mkEqRefl(v_a_128_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
return v___x_135_;
}
else
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Meta_mkHEqRefl(v_a_128_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
return v___x_136_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_128_ = stack[0].m_obj;
uint8_t v_heq_129_ = stack[1].m_num;
lean_object* v_a_130_ = stack[2].m_obj;
lean_object* v_a_131_ = stack[3].m_obj;
lean_object* v_a_132_ = stack[4].m_obj;
lean_object* v_a_133_ = stack[5].m_obj;
lean_object* v_res_137_;
v_res_137_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(v_a_128_, v_heq_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
stack->m_obj
 = v_res_137_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl___boxed(lean_object* v_a_138_, lean_object* v_heq_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
uint8_t v_heq_boxed_145_; lean_object* v_res_146_; 
v_heq_boxed_145_ = lean_unbox(v_heq_139_);
v_res_146_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(v_a_138_, v_heq_boxed_145_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
return v_res_146_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans(lean_object* v_h_u2081_147_, lean_object* v_h_u2082_148_, uint8_t v_heq_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
if (v_heq_149_ == 0)
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Meta_mkEqTrans(v_h_u2081_147_, v_h_u2082_148_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
return v___x_155_;
}
else
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Meta_mkHEqTrans(v_h_u2081_147_, v_h_u2082_148_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
return v___x_156_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_u2081_147_ = stack[0].m_obj;
lean_object* v_h_u2082_148_ = stack[1].m_obj;
uint8_t v_heq_149_ = stack[2].m_num;
lean_object* v_a_150_ = stack[3].m_obj;
lean_object* v_a_151_ = stack[4].m_obj;
lean_object* v_a_152_ = stack[5].m_obj;
lean_object* v_a_153_ = stack[6].m_obj;
lean_object* v_res_157_;
v_res_157_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans(v_h_u2081_147_, v_h_u2082_148_, v_heq_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
stack->m_obj
 = v_res_157_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans___boxed(lean_object* v_h_u2081_158_, lean_object* v_h_u2082_159_, lean_object* v_heq_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
uint8_t v_heq_boxed_166_; lean_object* v_res_167_; 
v_heq_boxed_166_ = lean_unbox(v_heq_160_);
v_res_167_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans(v_h_u2081_158_, v_h_u2082_159_, v_heq_boxed_166_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
return v_res_167_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(lean_object* v_h_u2081_168_, lean_object* v_h_u2082_169_, uint8_t v_heq_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
if (lean_obj_tag(v_h_u2081_168_) == 1)
{
lean_object* v_val_176_; lean_object* v___x_177_; 
v_val_176_ = lean_ctor_get(v_h_u2081_168_, 0);
lean_inc(v_val_176_);
lean_dec_ref_known(v_h_u2081_168_, 1);
v___x_177_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans(v_val_176_, v_h_u2082_169_, v_heq_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
return v___x_177_;
}
else
{
lean_object* v___x_178_; 
lean_dec(v_h_u2081_168_);
v___x_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_178_, 0, v_h_u2082_169_);
return v___x_178_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_u2081_168_ = stack[0].m_obj;
lean_object* v_h_u2082_169_ = stack[1].m_obj;
uint8_t v_heq_170_ = stack[2].m_num;
lean_object* v_a_171_ = stack[3].m_obj;
lean_object* v_a_172_ = stack[4].m_obj;
lean_object* v_a_173_ = stack[5].m_obj;
lean_object* v_a_174_ = stack[6].m_obj;
lean_object* v_res_179_;
v_res_179_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_h_u2081_168_, v_h_u2082_169_, v_heq_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
stack->m_obj
 = v_res_179_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27___boxed(lean_object* v_h_u2081_180_, lean_object* v_h_u2082_181_, lean_object* v_heq_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
uint8_t v_heq_boxed_188_; lean_object* v_res_189_; 
v_heq_boxed_188_ = lean_unbox(v_heq_182_);
v_res_189_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_h_u2081_180_, v_h_u2082_181_, v_heq_boxed_188_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
return v_res_189_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(lean_object* v_h_190_, uint8_t v_heq_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
if (v_heq_191_ == 0)
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Meta_mkEqOfHEq(v_h_190_, v_heq_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
return v___x_197_;
}
else
{
lean_object* v___x_198_; 
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v_h_190_);
return v___x_198_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_190_ = stack[0].m_obj;
uint8_t v_heq_191_ = stack[1].m_num;
lean_object* v_a_192_ = stack[2].m_obj;
lean_object* v_a_193_ = stack[3].m_obj;
lean_object* v_a_194_ = stack[4].m_obj;
lean_object* v_a_195_ = stack[5].m_obj;
lean_object* v_res_199_;
v_res_199_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_h_190_, v_heq_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
stack->m_obj
 = v_res_199_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded___boxed(lean_object* v_h_200_, lean_object* v_heq_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
uint8_t v_heq_boxed_207_; lean_object* v_res_208_; 
v_heq_boxed_207_ = lean_unbox(v_heq_201_);
v_res_208_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_h_200_, v_heq_boxed_207_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
return v_res_208_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0(void){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_209_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3(lean_object* v_msg_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___x_222_; lean_object* v___x_12252__overap_223_; lean_object* v___x_224_; 
v___x_222_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0);
v___x_12252__overap_223_ = lean_panic_fn_borrowed(v___x_222_, v_msg_210_);
lean_inc(v___y_220_);
lean_inc_ref(v___y_219_);
lean_inc(v___y_218_);
lean_inc_ref(v___y_217_);
lean_inc(v___y_216_);
lean_inc_ref(v___y_215_);
lean_inc(v___y_214_);
lean_inc_ref(v___y_213_);
lean_inc(v___y_212_);
lean_inc(v___y_211_);
v___x_224_ = lean_apply_11(v___x_12252__overap_223_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, lean_box(0));
return v___x_224_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_210_ = stack[0].m_obj;
lean_object* v___y_211_ = stack[1].m_obj;
lean_object* v___y_212_ = stack[2].m_obj;
lean_object* v___y_213_ = stack[3].m_obj;
lean_object* v___y_214_ = stack[4].m_obj;
lean_object* v___y_215_ = stack[5].m_obj;
lean_object* v___y_216_ = stack[6].m_obj;
lean_object* v___y_217_ = stack[7].m_obj;
lean_object* v___y_218_ = stack[8].m_obj;
lean_object* v___y_219_ = stack[9].m_obj;
lean_object* v___y_220_ = stack[10].m_obj;
lean_object* v_res_225_;
v_res_225_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3(v_msg_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
stack->m_obj
 = v_res_225_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___boxed(lean_object* v_msg_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3(v_msg_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec(v___y_227_);
return v_res_238_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(lean_object* v_msg_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_13049__overap_252_; lean_object* v___x_253_; 
v___x_251_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0);
v___x_13049__overap_252_ = lean_panic_fn_borrowed(v___x_251_, v_msg_239_);
lean_inc(v___y_249_);
lean_inc_ref(v___y_248_);
lean_inc(v___y_247_);
lean_inc_ref(v___y_246_);
lean_inc(v___y_245_);
lean_inc_ref(v___y_244_);
lean_inc(v___y_243_);
lean_inc_ref(v___y_242_);
lean_inc(v___y_241_);
lean_inc(v___y_240_);
v___x_253_ = lean_apply_11(v___x_13049__overap_252_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, lean_box(0));
return v___x_253_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_239_ = stack[0].m_obj;
lean_object* v___y_240_ = stack[1].m_obj;
lean_object* v___y_241_ = stack[2].m_obj;
lean_object* v___y_242_ = stack[3].m_obj;
lean_object* v___y_243_ = stack[4].m_obj;
lean_object* v___y_244_ = stack[5].m_obj;
lean_object* v___y_245_ = stack[6].m_obj;
lean_object* v___y_246_ = stack[7].m_obj;
lean_object* v___y_247_ = stack[8].m_obj;
lean_object* v___y_248_ = stack[9].m_obj;
lean_object* v___y_249_ = stack[10].m_obj;
lean_object* v_res_254_;
v_res_254_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v_msg_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
stack->m_obj
 = v_res_254_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___boxed(lean_object* v_msg_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v_msg_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec(v___y_256_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(lean_object* v_t_268_, lean_object* v_k_269_){
_start:
{
if (lean_obj_tag(v_t_268_) == 0)
{
lean_object* v_k_270_; lean_object* v_v_271_; lean_object* v_l_272_; lean_object* v_r_273_; uint8_t v___x_274_; 
v_k_270_ = lean_ctor_get(v_t_268_, 1);
v_v_271_ = lean_ctor_get(v_t_268_, 2);
v_l_272_ = lean_ctor_get(v_t_268_, 3);
v_r_273_ = lean_ctor_get(v_t_268_, 4);
v___x_274_ = lean_nat_dec_lt(v_k_269_, v_k_270_);
if (v___x_274_ == 0)
{
uint8_t v___x_275_; 
v___x_275_ = lean_nat_dec_eq(v_k_269_, v_k_270_);
if (v___x_275_ == 0)
{
v_t_268_ = v_r_273_;
goto _start;
}
else
{
lean_object* v___x_277_; 
lean_inc(v_v_271_);
v___x_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_277_, 0, v_v_271_);
return v___x_277_;
}
}
else
{
v_t_268_ = v_l_272_;
goto _start;
}
}
else
{
lean_object* v___x_279_; 
v___x_279_ = lean_box(0);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg___boxed(lean_object* v_t_280_, lean_object* v_k_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(v_t_280_, v_k_281_);
lean_dec(v_k_281_);
lean_dec(v_t_280_);
return v_res_282_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_286_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_287_ = lean_unsigned_to_nat(35u);
v___x_288_ = lean_unsigned_to_nat(87u);
v___x_289_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__1));
v___x_290_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_291_ = l_mkPanicMessageWithDecl(v___x_290_, v___x_289_, v___x_288_, v___x_287_, v___x_286_);
return v___x_291_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(lean_object* v___x_292_, lean_object* v_a_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_snd_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_353_; 
v_snd_305_ = lean_ctor_get(v_a_293_, 1);
v_isSharedCheck_353_ = !lean_is_exclusive(v_a_293_);
if (v_isSharedCheck_353_ == 0)
{
lean_object* v_unused_354_; 
v_unused_354_ = lean_ctor_get(v_a_293_, 0);
lean_dec(v_unused_354_);
v___x_307_ = v_a_293_;
v_isShared_308_ = v_isSharedCheck_353_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_snd_305_);
lean_dec(v_a_293_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_353_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_box(0);
v___x_310_ = lean_st_ref_get(v___y_294_);
lean_inc(v_snd_305_);
v___x_311_ = l_Lean_Meta_Grind_Goal_getENode(v___x_310_, v_snd_305_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___x_310_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_344_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_344_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_344_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_344_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v_target_x3f_316_; lean_object* v_idx_317_; lean_object* v___x_318_; 
v_target_x3f_316_ = lean_ctor_get(v_a_312_, 4);
lean_inc(v_target_x3f_316_);
v_idx_317_ = lean_ctor_get(v_a_312_, 7);
lean_inc(v_idx_317_);
lean_dec(v_a_312_);
v___x_318_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(v___x_292_, v_idx_317_);
lean_dec(v_idx_317_);
if (lean_obj_tag(v___x_318_) == 1)
{
lean_object* v___x_320_; 
lean_dec(v_target_x3f_316_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_318_);
v___x_320_ = v___x_307_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_snd_305_);
v___x_320_ = v_reuseFailAlloc_324_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_322_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_320_);
v___x_322_ = v___x_314_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
else
{
lean_dec(v___x_318_);
lean_del_object(v___x_314_);
if (lean_obj_tag(v_target_x3f_316_) == 1)
{
lean_object* v_val_325_; lean_object* v___x_327_; 
lean_dec(v_snd_305_);
v_val_325_ = lean_ctor_get(v_target_x3f_316_, 0);
lean_inc(v_val_325_);
lean_dec_ref_known(v_target_x3f_316_, 1);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v_val_325_);
lean_ctor_set(v___x_307_, 0, v___x_309_);
v___x_327_ = v___x_307_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_val_325_);
v___x_327_ = v_reuseFailAlloc_329_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
v_a_293_ = v___x_327_;
goto _start;
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v_target_x3f_316_);
v___x_330_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3);
v___x_331_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3(v___x_330_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v___x_333_; 
lean_dec_ref_known(v___x_331_, 1);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_309_);
v___x_333_ = v___x_307_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_snd_305_);
v___x_333_ = v_reuseFailAlloc_335_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
v_a_293_ = v___x_333_;
goto _start;
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_del_object(v___x_307_);
lean_dec(v_snd_305_);
v_a_336_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_331_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_331_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_del_object(v___x_307_);
lean_dec(v_snd_305_);
v_a_345_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_311_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_311_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_292_ = stack[0].m_obj;
lean_object* v_a_293_ = stack[1].m_obj;
lean_object* v___y_294_ = stack[2].m_obj;
lean_object* v___y_295_ = stack[3].m_obj;
lean_object* v___y_296_ = stack[4].m_obj;
lean_object* v___y_297_ = stack[5].m_obj;
lean_object* v___y_298_ = stack[6].m_obj;
lean_object* v___y_299_ = stack[7].m_obj;
lean_object* v___y_300_ = stack[8].m_obj;
lean_object* v___y_301_ = stack[9].m_obj;
lean_object* v___y_302_ = stack[10].m_obj;
lean_object* v___y_303_ = stack[11].m_obj;
lean_object* v_res_355_;
v_res_355_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(v___x_292_, v_a_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
stack->m_obj
 = v_res_355_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___boxed(lean_object* v___x_356_, lean_object* v_a_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(v___x_356_, v_a_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec(v___y_358_);
lean_dec(v___x_356_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(lean_object* v_k_370_, lean_object* v_v_371_, lean_object* v_t_372_){
_start:
{
if (lean_obj_tag(v_t_372_) == 0)
{
lean_object* v_size_373_; lean_object* v_k_374_; lean_object* v_v_375_; lean_object* v_l_376_; lean_object* v_r_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_658_; 
v_size_373_ = lean_ctor_get(v_t_372_, 0);
v_k_374_ = lean_ctor_get(v_t_372_, 1);
v_v_375_ = lean_ctor_get(v_t_372_, 2);
v_l_376_ = lean_ctor_get(v_t_372_, 3);
v_r_377_ = lean_ctor_get(v_t_372_, 4);
v_isSharedCheck_658_ = !lean_is_exclusive(v_t_372_);
if (v_isSharedCheck_658_ == 0)
{
v___x_379_ = v_t_372_;
v_isShared_380_ = v_isSharedCheck_658_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_r_377_);
lean_inc(v_l_376_);
lean_inc(v_v_375_);
lean_inc(v_k_374_);
lean_inc(v_size_373_);
lean_dec(v_t_372_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_658_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
uint8_t v___x_381_; 
v___x_381_ = lean_nat_dec_lt(v_k_370_, v_k_374_);
if (v___x_381_ == 0)
{
uint8_t v___x_382_; 
v___x_382_ = lean_nat_dec_eq(v_k_370_, v_k_374_);
if (v___x_382_ == 0)
{
lean_object* v_impl_383_; lean_object* v___x_384_; 
lean_dec(v_size_373_);
v_impl_383_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_k_370_, v_v_371_, v_r_377_);
v___x_384_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_376_) == 0)
{
lean_object* v_size_385_; lean_object* v_size_386_; lean_object* v_k_387_; lean_object* v_v_388_; lean_object* v_l_389_; lean_object* v_r_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v_size_385_ = lean_ctor_get(v_l_376_, 0);
v_size_386_ = lean_ctor_get(v_impl_383_, 0);
v_k_387_ = lean_ctor_get(v_impl_383_, 1);
v_v_388_ = lean_ctor_get(v_impl_383_, 2);
v_l_389_ = lean_ctor_get(v_impl_383_, 3);
lean_inc(v_l_389_);
v_r_390_ = lean_ctor_get(v_impl_383_, 4);
v___x_391_ = lean_unsigned_to_nat(3u);
v___x_392_ = lean_nat_mul(v___x_391_, v_size_385_);
v___x_393_ = lean_nat_dec_lt(v___x_392_, v_size_386_);
lean_dec(v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
lean_dec(v_l_389_);
v___x_394_ = lean_nat_add(v___x_384_, v_size_385_);
v___x_395_ = lean_nat_add(v___x_394_, v_size_386_);
lean_dec(v___x_394_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 4, v_impl_383_);
lean_ctor_set(v___x_379_, 0, v___x_395_);
v___x_397_ = v___x_379_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_k_374_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_v_375_);
lean_ctor_set(v_reuseFailAlloc_398_, 3, v_l_376_);
lean_ctor_set(v_reuseFailAlloc_398_, 4, v_impl_383_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
else
{
lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_462_; 
lean_inc(v_r_390_);
lean_inc(v_v_388_);
lean_inc(v_k_387_);
lean_inc(v_size_386_);
v_isSharedCheck_462_ = !lean_is_exclusive(v_impl_383_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; lean_object* v_unused_464_; lean_object* v_unused_465_; lean_object* v_unused_466_; lean_object* v_unused_467_; 
v_unused_463_ = lean_ctor_get(v_impl_383_, 4);
lean_dec(v_unused_463_);
v_unused_464_ = lean_ctor_get(v_impl_383_, 3);
lean_dec(v_unused_464_);
v_unused_465_ = lean_ctor_get(v_impl_383_, 2);
lean_dec(v_unused_465_);
v_unused_466_ = lean_ctor_get(v_impl_383_, 1);
lean_dec(v_unused_466_);
v_unused_467_ = lean_ctor_get(v_impl_383_, 0);
lean_dec(v_unused_467_);
v___x_400_ = v_impl_383_;
v_isShared_401_ = v_isSharedCheck_462_;
goto v_resetjp_399_;
}
else
{
lean_dec(v_impl_383_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_462_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v_size_402_; lean_object* v_k_403_; lean_object* v_v_404_; lean_object* v_l_405_; lean_object* v_r_406_; lean_object* v_size_407_; lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v_size_402_ = lean_ctor_get(v_l_389_, 0);
v_k_403_ = lean_ctor_get(v_l_389_, 1);
v_v_404_ = lean_ctor_get(v_l_389_, 2);
v_l_405_ = lean_ctor_get(v_l_389_, 3);
v_r_406_ = lean_ctor_get(v_l_389_, 4);
v_size_407_ = lean_ctor_get(v_r_390_, 0);
v___x_408_ = lean_unsigned_to_nat(2u);
v___x_409_ = lean_nat_mul(v___x_408_, v_size_407_);
v___x_410_ = lean_nat_dec_lt(v_size_402_, v___x_409_);
lean_dec(v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_438_; 
lean_inc(v_r_406_);
lean_inc(v_l_405_);
lean_inc(v_v_404_);
lean_inc(v_k_403_);
v_isSharedCheck_438_ = !lean_is_exclusive(v_l_389_);
if (v_isSharedCheck_438_ == 0)
{
lean_object* v_unused_439_; lean_object* v_unused_440_; lean_object* v_unused_441_; lean_object* v_unused_442_; lean_object* v_unused_443_; 
v_unused_439_ = lean_ctor_get(v_l_389_, 4);
lean_dec(v_unused_439_);
v_unused_440_ = lean_ctor_get(v_l_389_, 3);
lean_dec(v_unused_440_);
v_unused_441_ = lean_ctor_get(v_l_389_, 2);
lean_dec(v_unused_441_);
v_unused_442_ = lean_ctor_get(v_l_389_, 1);
lean_dec(v_unused_442_);
v_unused_443_ = lean_ctor_get(v_l_389_, 0);
lean_dec(v_unused_443_);
v___x_412_ = v_l_389_;
v_isShared_413_ = v_isSharedCheck_438_;
goto v_resetjp_411_;
}
else
{
lean_dec(v_l_389_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_438_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_428_; 
v___x_414_ = lean_nat_add(v___x_384_, v_size_385_);
v___x_415_ = lean_nat_add(v___x_414_, v_size_386_);
lean_dec(v_size_386_);
if (lean_obj_tag(v_l_405_) == 0)
{
lean_object* v_size_436_; 
v_size_436_ = lean_ctor_get(v_l_405_, 0);
lean_inc(v_size_436_);
v___y_428_ = v_size_436_;
goto v___jp_427_;
}
else
{
lean_object* v___x_437_; 
v___x_437_ = lean_unsigned_to_nat(0u);
v___y_428_ = v___x_437_;
goto v___jp_427_;
}
v___jp_416_:
{
lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_420_ = lean_nat_add(v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec(v___y_418_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 4, v_r_390_);
lean_ctor_set(v___x_412_, 3, v_r_406_);
lean_ctor_set(v___x_412_, 2, v_v_388_);
lean_ctor_set(v___x_412_, 1, v_k_387_);
lean_ctor_set(v___x_412_, 0, v___x_420_);
v___x_422_ = v___x_412_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_k_387_);
lean_ctor_set(v_reuseFailAlloc_426_, 2, v_v_388_);
lean_ctor_set(v_reuseFailAlloc_426_, 3, v_r_406_);
lean_ctor_set(v_reuseFailAlloc_426_, 4, v_r_390_);
v___x_422_ = v_reuseFailAlloc_426_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_424_; 
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 4, v___x_422_);
lean_ctor_set(v___x_400_, 3, v___y_417_);
lean_ctor_set(v___x_400_, 2, v_v_404_);
lean_ctor_set(v___x_400_, 1, v_k_403_);
lean_ctor_set(v___x_400_, 0, v___x_415_);
v___x_424_ = v___x_400_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_k_403_);
lean_ctor_set(v_reuseFailAlloc_425_, 2, v_v_404_);
lean_ctor_set(v_reuseFailAlloc_425_, 3, v___y_417_);
lean_ctor_set(v_reuseFailAlloc_425_, 4, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
v___jp_427_:
{
lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_429_ = lean_nat_add(v___x_414_, v___y_428_);
lean_dec(v___y_428_);
lean_dec(v___x_414_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 4, v_l_405_);
lean_ctor_set(v___x_379_, 0, v___x_429_);
v___x_431_ = v___x_379_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_k_374_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_v_375_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_l_376_);
lean_ctor_set(v_reuseFailAlloc_435_, 4, v_l_405_);
v___x_431_ = v_reuseFailAlloc_435_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; 
v___x_432_ = lean_nat_add(v___x_384_, v_size_407_);
if (lean_obj_tag(v_r_406_) == 0)
{
lean_object* v_size_433_; 
v_size_433_ = lean_ctor_get(v_r_406_, 0);
lean_inc(v_size_433_);
v___y_417_ = v___x_431_;
v___y_418_ = v___x_432_;
v___y_419_ = v_size_433_;
goto v___jp_416_;
}
else
{
lean_object* v___x_434_; 
v___x_434_ = lean_unsigned_to_nat(0u);
v___y_417_ = v___x_431_;
v___y_418_ = v___x_432_;
v___y_419_ = v___x_434_;
goto v___jp_416_;
}
}
}
}
}
else
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
lean_del_object(v___x_379_);
v___x_444_ = lean_nat_add(v___x_384_, v_size_385_);
v___x_445_ = lean_nat_add(v___x_444_, v_size_386_);
lean_dec(v_size_386_);
v___x_446_ = lean_nat_add(v___x_444_, v_size_402_);
lean_dec(v___x_444_);
lean_inc_ref(v_l_376_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 4, v_l_389_);
lean_ctor_set(v___x_400_, 3, v_l_376_);
lean_ctor_set(v___x_400_, 2, v_v_375_);
lean_ctor_set(v___x_400_, 1, v_k_374_);
lean_ctor_set(v___x_400_, 0, v___x_446_);
v___x_448_ = v___x_400_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_446_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_k_374_);
lean_ctor_set(v_reuseFailAlloc_461_, 2, v_v_375_);
lean_ctor_set(v_reuseFailAlloc_461_, 3, v_l_376_);
lean_ctor_set(v_reuseFailAlloc_461_, 4, v_l_389_);
v___x_448_ = v_reuseFailAlloc_461_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
v_isSharedCheck_455_ = !lean_is_exclusive(v_l_376_);
if (v_isSharedCheck_455_ == 0)
{
lean_object* v_unused_456_; lean_object* v_unused_457_; lean_object* v_unused_458_; lean_object* v_unused_459_; lean_object* v_unused_460_; 
v_unused_456_ = lean_ctor_get(v_l_376_, 4);
lean_dec(v_unused_456_);
v_unused_457_ = lean_ctor_get(v_l_376_, 3);
lean_dec(v_unused_457_);
v_unused_458_ = lean_ctor_get(v_l_376_, 2);
lean_dec(v_unused_458_);
v_unused_459_ = lean_ctor_get(v_l_376_, 1);
lean_dec(v_unused_459_);
v_unused_460_ = lean_ctor_get(v_l_376_, 0);
lean_dec(v_unused_460_);
v___x_450_ = v_l_376_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_dec(v_l_376_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 4, v_r_390_);
lean_ctor_set(v___x_450_, 3, v___x_448_);
lean_ctor_set(v___x_450_, 2, v_v_388_);
lean_ctor_set(v___x_450_, 1, v_k_387_);
lean_ctor_set(v___x_450_, 0, v___x_445_);
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_k_387_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_v_388_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v_r_390_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_468_; 
v_l_468_ = lean_ctor_get(v_impl_383_, 3);
lean_inc(v_l_468_);
if (lean_obj_tag(v_l_468_) == 0)
{
lean_object* v_r_469_; lean_object* v_k_470_; lean_object* v_v_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_494_; 
v_r_469_ = lean_ctor_get(v_impl_383_, 4);
v_k_470_ = lean_ctor_get(v_impl_383_, 1);
v_v_471_ = lean_ctor_get(v_impl_383_, 2);
v_isSharedCheck_494_ = !lean_is_exclusive(v_impl_383_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; lean_object* v_unused_496_; 
v_unused_495_ = lean_ctor_get(v_impl_383_, 3);
lean_dec(v_unused_495_);
v_unused_496_ = lean_ctor_get(v_impl_383_, 0);
lean_dec(v_unused_496_);
v___x_473_ = v_impl_383_;
v_isShared_474_ = v_isSharedCheck_494_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_r_469_);
lean_inc(v_v_471_);
lean_inc(v_k_470_);
lean_dec(v_impl_383_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_494_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v_k_475_; lean_object* v_v_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_490_; 
v_k_475_ = lean_ctor_get(v_l_468_, 1);
v_v_476_ = lean_ctor_get(v_l_468_, 2);
v_isSharedCheck_490_ = !lean_is_exclusive(v_l_468_);
if (v_isSharedCheck_490_ == 0)
{
lean_object* v_unused_491_; lean_object* v_unused_492_; lean_object* v_unused_493_; 
v_unused_491_ = lean_ctor_get(v_l_468_, 4);
lean_dec(v_unused_491_);
v_unused_492_ = lean_ctor_get(v_l_468_, 3);
lean_dec(v_unused_492_);
v_unused_493_ = lean_ctor_get(v_l_468_, 0);
lean_dec(v_unused_493_);
v___x_478_ = v_l_468_;
v_isShared_479_ = v_isSharedCheck_490_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_v_476_);
lean_inc(v_k_475_);
lean_dec(v_l_468_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_490_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v___x_482_; 
v___x_480_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_469_, 2);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 4, v_r_469_);
lean_ctor_set(v___x_478_, 3, v_r_469_);
lean_ctor_set(v___x_478_, 2, v_v_375_);
lean_ctor_set(v___x_478_, 1, v_k_374_);
lean_ctor_set(v___x_478_, 0, v___x_384_);
v___x_482_ = v___x_478_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_k_374_);
lean_ctor_set(v_reuseFailAlloc_489_, 2, v_v_375_);
lean_ctor_set(v_reuseFailAlloc_489_, 3, v_r_469_);
lean_ctor_set(v_reuseFailAlloc_489_, 4, v_r_469_);
v___x_482_ = v_reuseFailAlloc_489_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_484_; 
lean_inc(v_r_469_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 3, v_r_469_);
lean_ctor_set(v___x_473_, 0, v___x_384_);
v___x_484_ = v___x_473_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_488_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_488_, 3, v_r_469_);
lean_ctor_set(v_reuseFailAlloc_488_, 4, v_r_469_);
v___x_484_ = v_reuseFailAlloc_488_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_486_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 4, v___x_484_);
lean_ctor_set(v___x_379_, 3, v___x_482_);
lean_ctor_set(v___x_379_, 2, v_v_476_);
lean_ctor_set(v___x_379_, 1, v_k_475_);
lean_ctor_set(v___x_379_, 0, v___x_480_);
v___x_486_ = v___x_379_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_480_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_k_475_);
lean_ctor_set(v_reuseFailAlloc_487_, 2, v_v_476_);
lean_ctor_set(v_reuseFailAlloc_487_, 3, v___x_482_);
lean_ctor_set(v_reuseFailAlloc_487_, 4, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
}
else
{
lean_object* v_r_497_; 
v_r_497_ = lean_ctor_get(v_impl_383_, 4);
lean_inc(v_r_497_);
if (lean_obj_tag(v_r_497_) == 0)
{
lean_object* v_k_498_; lean_object* v_v_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_510_; 
v_k_498_ = lean_ctor_get(v_impl_383_, 1);
v_v_499_ = lean_ctor_get(v_impl_383_, 2);
v_isSharedCheck_510_ = !lean_is_exclusive(v_impl_383_);
if (v_isSharedCheck_510_ == 0)
{
lean_object* v_unused_511_; lean_object* v_unused_512_; lean_object* v_unused_513_; 
v_unused_511_ = lean_ctor_get(v_impl_383_, 4);
lean_dec(v_unused_511_);
v_unused_512_ = lean_ctor_get(v_impl_383_, 3);
lean_dec(v_unused_512_);
v_unused_513_ = lean_ctor_get(v_impl_383_, 0);
lean_dec(v_unused_513_);
v___x_501_ = v_impl_383_;
v_isShared_502_ = v_isSharedCheck_510_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_v_499_);
lean_inc(v_k_498_);
lean_dec(v_impl_383_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_510_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = lean_unsigned_to_nat(3u);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 4, v_l_468_);
lean_ctor_set(v___x_501_, 2, v_v_375_);
lean_ctor_set(v___x_501_, 1, v_k_374_);
lean_ctor_set(v___x_501_, 0, v___x_384_);
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_k_374_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v_v_375_);
lean_ctor_set(v_reuseFailAlloc_509_, 3, v_l_468_);
lean_ctor_set(v_reuseFailAlloc_509_, 4, v_l_468_);
v___x_505_ = v_reuseFailAlloc_509_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_507_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 4, v_r_497_);
lean_ctor_set(v___x_379_, 3, v___x_505_);
lean_ctor_set(v___x_379_, 2, v_v_499_);
lean_ctor_set(v___x_379_, 1, v_k_498_);
lean_ctor_set(v___x_379_, 0, v___x_503_);
v___x_507_ = v___x_379_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_508_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_508_, 3, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_508_, 4, v_r_497_);
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
else
{
lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_514_ = lean_unsigned_to_nat(2u);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 4, v_impl_383_);
lean_ctor_set(v___x_379_, 3, v_r_497_);
lean_ctor_set(v___x_379_, 0, v___x_514_);
v___x_516_ = v___x_379_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_k_374_);
lean_ctor_set(v_reuseFailAlloc_517_, 2, v_v_375_);
lean_ctor_set(v_reuseFailAlloc_517_, 3, v_r_497_);
lean_ctor_set(v_reuseFailAlloc_517_, 4, v_impl_383_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
else
{
lean_object* v___x_519_; 
lean_dec(v_v_375_);
lean_dec(v_k_374_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 2, v_v_371_);
lean_ctor_set(v___x_379_, 1, v_k_370_);
v___x_519_ = v___x_379_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_size_373_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_k_370_);
lean_ctor_set(v_reuseFailAlloc_520_, 2, v_v_371_);
lean_ctor_set(v_reuseFailAlloc_520_, 3, v_l_376_);
lean_ctor_set(v_reuseFailAlloc_520_, 4, v_r_377_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
else
{
lean_object* v_impl_521_; lean_object* v___x_522_; 
lean_dec(v_size_373_);
v_impl_521_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_k_370_, v_v_371_, v_l_376_);
v___x_522_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_377_) == 0)
{
lean_object* v_size_523_; lean_object* v_size_524_; lean_object* v_k_525_; lean_object* v_v_526_; lean_object* v_l_527_; lean_object* v_r_528_; lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_size_523_ = lean_ctor_get(v_r_377_, 0);
v_size_524_ = lean_ctor_get(v_impl_521_, 0);
v_k_525_ = lean_ctor_get(v_impl_521_, 1);
v_v_526_ = lean_ctor_get(v_impl_521_, 2);
v_l_527_ = lean_ctor_get(v_impl_521_, 3);
v_r_528_ = lean_ctor_get(v_impl_521_, 4);
lean_inc(v_r_528_);
v___x_529_ = lean_unsigned_to_nat(3u);
v___x_530_ = lean_nat_mul(v___x_529_, v_size_523_);
v___x_531_ = lean_nat_dec_lt(v___x_530_, v_size_524_);
lean_dec(v___x_530_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
lean_dec(v_r_528_);
v___x_532_ = lean_nat_add(v___x_522_, v_size_524_);
v___x_533_ = lean_nat_add(v___x_532_, v_size_523_);
lean_dec(v___x_532_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 3, v_impl_521_);
lean_ctor_set(v___x_379_, 0, v___x_533_);
v___x_535_ = v___x_379_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_k_374_);
lean_ctor_set(v_reuseFailAlloc_536_, 2, v_v_375_);
lean_ctor_set(v_reuseFailAlloc_536_, 3, v_impl_521_);
lean_ctor_set(v_reuseFailAlloc_536_, 4, v_r_377_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
else
{
lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_602_; 
lean_inc(v_l_527_);
lean_inc(v_v_526_);
lean_inc(v_k_525_);
lean_inc(v_size_524_);
v_isSharedCheck_602_ = !lean_is_exclusive(v_impl_521_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; lean_object* v_unused_604_; lean_object* v_unused_605_; lean_object* v_unused_606_; lean_object* v_unused_607_; 
v_unused_603_ = lean_ctor_get(v_impl_521_, 4);
lean_dec(v_unused_603_);
v_unused_604_ = lean_ctor_get(v_impl_521_, 3);
lean_dec(v_unused_604_);
v_unused_605_ = lean_ctor_get(v_impl_521_, 2);
lean_dec(v_unused_605_);
v_unused_606_ = lean_ctor_get(v_impl_521_, 1);
lean_dec(v_unused_606_);
v_unused_607_ = lean_ctor_get(v_impl_521_, 0);
lean_dec(v_unused_607_);
v___x_538_ = v_impl_521_;
v_isShared_539_ = v_isSharedCheck_602_;
goto v_resetjp_537_;
}
else
{
lean_dec(v_impl_521_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_602_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v_size_540_; lean_object* v_size_541_; lean_object* v_k_542_; lean_object* v_v_543_; lean_object* v_l_544_; lean_object* v_r_545_; lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v_size_540_ = lean_ctor_get(v_l_527_, 0);
v_size_541_ = lean_ctor_get(v_r_528_, 0);
v_k_542_ = lean_ctor_get(v_r_528_, 1);
v_v_543_ = lean_ctor_get(v_r_528_, 2);
v_l_544_ = lean_ctor_get(v_r_528_, 3);
v_r_545_ = lean_ctor_get(v_r_528_, 4);
v___x_546_ = lean_unsigned_to_nat(2u);
v___x_547_ = lean_nat_mul(v___x_546_, v_size_540_);
v___x_548_ = lean_nat_dec_lt(v_size_541_, v___x_547_);
lean_dec(v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_577_; 
lean_inc(v_r_545_);
lean_inc(v_l_544_);
lean_inc(v_v_543_);
lean_inc(v_k_542_);
v_isSharedCheck_577_ = !lean_is_exclusive(v_r_528_);
if (v_isSharedCheck_577_ == 0)
{
lean_object* v_unused_578_; lean_object* v_unused_579_; lean_object* v_unused_580_; lean_object* v_unused_581_; lean_object* v_unused_582_; 
v_unused_578_ = lean_ctor_get(v_r_528_, 4);
lean_dec(v_unused_578_);
v_unused_579_ = lean_ctor_get(v_r_528_, 3);
lean_dec(v_unused_579_);
v_unused_580_ = lean_ctor_get(v_r_528_, 2);
lean_dec(v_unused_580_);
v_unused_581_ = lean_ctor_get(v_r_528_, 1);
lean_dec(v_unused_581_);
v_unused_582_ = lean_ctor_get(v_r_528_, 0);
lean_dec(v_unused_582_);
v___x_550_ = v_r_528_;
v_isShared_551_ = v_isSharedCheck_577_;
goto v_resetjp_549_;
}
else
{
lean_dec(v_r_528_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_577_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___x_565_; lean_object* v___y_567_; 
v___x_552_ = lean_nat_add(v___x_522_, v_size_524_);
lean_dec(v_size_524_);
v___x_553_ = lean_nat_add(v___x_552_, v_size_523_);
lean_dec(v___x_552_);
v___x_565_ = lean_nat_add(v___x_522_, v_size_540_);
if (lean_obj_tag(v_l_544_) == 0)
{
lean_object* v_size_575_; 
v_size_575_ = lean_ctor_get(v_l_544_, 0);
lean_inc(v_size_575_);
v___y_567_ = v_size_575_;
goto v___jp_566_;
}
else
{
lean_object* v___x_576_; 
v___x_576_ = lean_unsigned_to_nat(0u);
v___y_567_ = v___x_576_;
goto v___jp_566_;
}
v___jp_554_:
{
lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_558_ = lean_nat_add(v___y_555_, v___y_557_);
lean_dec(v___y_557_);
lean_dec(v___y_555_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 4, v_r_377_);
lean_ctor_set(v___x_550_, 3, v_r_545_);
lean_ctor_set(v___x_550_, 2, v_v_375_);
lean_ctor_set(v___x_550_, 1, v_k_374_);
lean_ctor_set(v___x_550_, 0, v___x_558_);
v___x_560_ = v___x_550_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_k_374_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_v_375_);
lean_ctor_set(v_reuseFailAlloc_564_, 3, v_r_545_);
lean_ctor_set(v_reuseFailAlloc_564_, 4, v_r_377_);
v___x_560_ = v_reuseFailAlloc_564_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_562_; 
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 4, v___x_560_);
lean_ctor_set(v___x_538_, 3, v___y_556_);
lean_ctor_set(v___x_538_, 2, v_v_543_);
lean_ctor_set(v___x_538_, 1, v_k_542_);
lean_ctor_set(v___x_538_, 0, v___x_553_);
v___x_562_ = v___x_538_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_k_542_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_v_543_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v___y_556_);
lean_ctor_set(v_reuseFailAlloc_563_, 4, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
v___jp_566_:
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = lean_nat_add(v___x_565_, v___y_567_);
lean_dec(v___y_567_);
lean_dec(v___x_565_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 4, v_l_544_);
lean_ctor_set(v___x_379_, 3, v_l_527_);
lean_ctor_set(v___x_379_, 2, v_v_526_);
lean_ctor_set(v___x_379_, 1, v_k_525_);
lean_ctor_set(v___x_379_, 0, v___x_568_);
v___x_570_ = v___x_379_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_k_525_);
lean_ctor_set(v_reuseFailAlloc_574_, 2, v_v_526_);
lean_ctor_set(v_reuseFailAlloc_574_, 3, v_l_527_);
lean_ctor_set(v_reuseFailAlloc_574_, 4, v_l_544_);
v___x_570_ = v_reuseFailAlloc_574_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; 
v___x_571_ = lean_nat_add(v___x_522_, v_size_523_);
if (lean_obj_tag(v_r_545_) == 0)
{
lean_object* v_size_572_; 
v_size_572_ = lean_ctor_get(v_r_545_, 0);
lean_inc(v_size_572_);
v___y_555_ = v___x_571_;
v___y_556_ = v___x_570_;
v___y_557_ = v_size_572_;
goto v___jp_554_;
}
else
{
lean_object* v___x_573_; 
v___x_573_ = lean_unsigned_to_nat(0u);
v___y_555_ = v___x_571_;
v___y_556_ = v___x_570_;
v___y_557_ = v___x_573_;
goto v___jp_554_;
}
}
}
}
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
lean_del_object(v___x_379_);
v___x_583_ = lean_nat_add(v___x_522_, v_size_524_);
lean_dec(v_size_524_);
v___x_584_ = lean_nat_add(v___x_583_, v_size_523_);
lean_dec(v___x_583_);
v___x_585_ = lean_nat_add(v___x_522_, v_size_523_);
v___x_586_ = lean_nat_add(v___x_585_, v_size_541_);
lean_dec(v___x_585_);
lean_inc_ref(v_r_377_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 4, v_r_377_);
lean_ctor_set(v___x_538_, 3, v_r_528_);
lean_ctor_set(v___x_538_, 2, v_v_375_);
lean_ctor_set(v___x_538_, 1, v_k_374_);
lean_ctor_set(v___x_538_, 0, v___x_586_);
v___x_588_ = v___x_538_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_k_374_);
lean_ctor_set(v_reuseFailAlloc_601_, 2, v_v_375_);
lean_ctor_set(v_reuseFailAlloc_601_, 3, v_r_528_);
lean_ctor_set(v_reuseFailAlloc_601_, 4, v_r_377_);
v___x_588_ = v_reuseFailAlloc_601_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
v_isSharedCheck_595_ = !lean_is_exclusive(v_r_377_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; lean_object* v_unused_597_; lean_object* v_unused_598_; lean_object* v_unused_599_; lean_object* v_unused_600_; 
v_unused_596_ = lean_ctor_get(v_r_377_, 4);
lean_dec(v_unused_596_);
v_unused_597_ = lean_ctor_get(v_r_377_, 3);
lean_dec(v_unused_597_);
v_unused_598_ = lean_ctor_get(v_r_377_, 2);
lean_dec(v_unused_598_);
v_unused_599_ = lean_ctor_get(v_r_377_, 1);
lean_dec(v_unused_599_);
v_unused_600_ = lean_ctor_get(v_r_377_, 0);
lean_dec(v_unused_600_);
v___x_590_ = v_r_377_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_dec(v_r_377_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 4, v___x_588_);
lean_ctor_set(v___x_590_, 3, v_l_527_);
lean_ctor_set(v___x_590_, 2, v_v_526_);
lean_ctor_set(v___x_590_, 1, v_k_525_);
lean_ctor_set(v___x_590_, 0, v___x_584_);
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_k_525_);
lean_ctor_set(v_reuseFailAlloc_594_, 2, v_v_526_);
lean_ctor_set(v_reuseFailAlloc_594_, 3, v_l_527_);
lean_ctor_set(v_reuseFailAlloc_594_, 4, v___x_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_608_; 
v_l_608_ = lean_ctor_get(v_impl_521_, 3);
if (lean_obj_tag(v_l_608_) == 0)
{
lean_object* v_r_609_; lean_object* v_k_610_; lean_object* v_v_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_622_; 
lean_inc_ref(v_l_608_);
v_r_609_ = lean_ctor_get(v_impl_521_, 4);
v_k_610_ = lean_ctor_get(v_impl_521_, 1);
v_v_611_ = lean_ctor_get(v_impl_521_, 2);
v_isSharedCheck_622_ = !lean_is_exclusive(v_impl_521_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; lean_object* v_unused_624_; 
v_unused_623_ = lean_ctor_get(v_impl_521_, 3);
lean_dec(v_unused_623_);
v_unused_624_ = lean_ctor_get(v_impl_521_, 0);
lean_dec(v_unused_624_);
v___x_613_ = v_impl_521_;
v_isShared_614_ = v_isSharedCheck_622_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_r_609_);
lean_inc(v_v_611_);
lean_inc(v_k_610_);
lean_dec(v_impl_521_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_622_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_609_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 3, v_r_609_);
lean_ctor_set(v___x_613_, 2, v_v_375_);
lean_ctor_set(v___x_613_, 1, v_k_374_);
lean_ctor_set(v___x_613_, 0, v___x_522_);
v___x_617_ = v___x_613_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_k_374_);
lean_ctor_set(v_reuseFailAlloc_621_, 2, v_v_375_);
lean_ctor_set(v_reuseFailAlloc_621_, 3, v_r_609_);
lean_ctor_set(v_reuseFailAlloc_621_, 4, v_r_609_);
v___x_617_ = v_reuseFailAlloc_621_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_619_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 4, v___x_617_);
lean_ctor_set(v___x_379_, 3, v_l_608_);
lean_ctor_set(v___x_379_, 2, v_v_611_);
lean_ctor_set(v___x_379_, 1, v_k_610_);
lean_ctor_set(v___x_379_, 0, v___x_615_);
v___x_619_ = v___x_379_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_k_610_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_v_611_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v_l_608_);
lean_ctor_set(v_reuseFailAlloc_620_, 4, v___x_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
else
{
lean_object* v_r_625_; 
v_r_625_ = lean_ctor_get(v_impl_521_, 4);
lean_inc(v_r_625_);
if (lean_obj_tag(v_r_625_) == 0)
{
lean_object* v_k_626_; lean_object* v_v_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_650_; 
lean_inc(v_l_608_);
v_k_626_ = lean_ctor_get(v_impl_521_, 1);
v_v_627_ = lean_ctor_get(v_impl_521_, 2);
v_isSharedCheck_650_ = !lean_is_exclusive(v_impl_521_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; lean_object* v_unused_652_; lean_object* v_unused_653_; 
v_unused_651_ = lean_ctor_get(v_impl_521_, 4);
lean_dec(v_unused_651_);
v_unused_652_ = lean_ctor_get(v_impl_521_, 3);
lean_dec(v_unused_652_);
v_unused_653_ = lean_ctor_get(v_impl_521_, 0);
lean_dec(v_unused_653_);
v___x_629_ = v_impl_521_;
v_isShared_630_ = v_isSharedCheck_650_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_v_627_);
lean_inc(v_k_626_);
lean_dec(v_impl_521_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_650_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v_k_631_; lean_object* v_v_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_646_; 
v_k_631_ = lean_ctor_get(v_r_625_, 1);
v_v_632_ = lean_ctor_get(v_r_625_, 2);
v_isSharedCheck_646_ = !lean_is_exclusive(v_r_625_);
if (v_isSharedCheck_646_ == 0)
{
lean_object* v_unused_647_; lean_object* v_unused_648_; lean_object* v_unused_649_; 
v_unused_647_ = lean_ctor_get(v_r_625_, 4);
lean_dec(v_unused_647_);
v_unused_648_ = lean_ctor_get(v_r_625_, 3);
lean_dec(v_unused_648_);
v_unused_649_ = lean_ctor_get(v_r_625_, 0);
lean_dec(v_unused_649_);
v___x_634_ = v_r_625_;
v_isShared_635_ = v_isSharedCheck_646_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_v_632_);
lean_inc(v_k_631_);
lean_dec(v_r_625_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_646_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_636_ = lean_unsigned_to_nat(3u);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 4, v_l_608_);
lean_ctor_set(v___x_634_, 3, v_l_608_);
lean_ctor_set(v___x_634_, 2, v_v_627_);
lean_ctor_set(v___x_634_, 1, v_k_626_);
lean_ctor_set(v___x_634_, 0, v___x_522_);
v___x_638_ = v___x_634_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_k_626_);
lean_ctor_set(v_reuseFailAlloc_645_, 2, v_v_627_);
lean_ctor_set(v_reuseFailAlloc_645_, 3, v_l_608_);
lean_ctor_set(v_reuseFailAlloc_645_, 4, v_l_608_);
v___x_638_ = v_reuseFailAlloc_645_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_640_; 
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 4, v_l_608_);
lean_ctor_set(v___x_629_, 2, v_v_375_);
lean_ctor_set(v___x_629_, 1, v_k_374_);
lean_ctor_set(v___x_629_, 0, v___x_522_);
v___x_640_ = v___x_629_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_k_374_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_v_375_);
lean_ctor_set(v_reuseFailAlloc_644_, 3, v_l_608_);
lean_ctor_set(v_reuseFailAlloc_644_, 4, v_l_608_);
v___x_640_ = v_reuseFailAlloc_644_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_642_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 4, v___x_640_);
lean_ctor_set(v___x_379_, 3, v___x_638_);
lean_ctor_set(v___x_379_, 2, v_v_632_);
lean_ctor_set(v___x_379_, 1, v_k_631_);
lean_ctor_set(v___x_379_, 0, v___x_636_);
v___x_642_ = v___x_379_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_643_, 3, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_643_, 4, v___x_640_);
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
lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_654_ = lean_unsigned_to_nat(2u);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 4, v_r_625_);
lean_ctor_set(v___x_379_, 3, v_impl_521_);
lean_ctor_set(v___x_379_, 0, v___x_654_);
v___x_656_ = v___x_379_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_k_374_);
lean_ctor_set(v_reuseFailAlloc_657_, 2, v_v_375_);
lean_ctor_set(v_reuseFailAlloc_657_, 3, v_impl_521_);
lean_ctor_set(v_reuseFailAlloc_657_, 4, v_r_625_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v_k_370_);
lean_ctor_set(v___x_660_, 2, v_v_371_);
lean_ctor_set(v___x_660_, 3, v_t_372_);
lean_ctor_set(v___x_660_, 4, v_t_372_);
return v___x_660_;
}
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(lean_object* v_a_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_fst_668_; lean_object* v_snd_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_703_; 
v_fst_668_ = lean_ctor_get(v_a_661_, 0);
v_snd_669_ = lean_ctor_get(v_a_661_, 1);
v_isSharedCheck_703_ = !lean_is_exclusive(v_a_661_);
if (v_isSharedCheck_703_ == 0)
{
v___x_671_ = v_a_661_;
v_isShared_672_ = v_isSharedCheck_703_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_snd_669_);
lean_inc(v_fst_668_);
lean_dec(v_a_661_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_703_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_st_ref_get(v___y_662_);
lean_inc(v_snd_669_);
v___x_674_ = l_Lean_Meta_Grind_Goal_getENode(v___x_673_, v_snd_669_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___x_673_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_694_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_694_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_694_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_694_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v_self_679_; lean_object* v_target_x3f_680_; lean_object* v_idx_681_; lean_object* v___x_682_; 
v_self_679_ = lean_ctor_get(v_a_675_, 0);
lean_inc_ref(v_self_679_);
v_target_x3f_680_ = lean_ctor_get(v_a_675_, 4);
lean_inc(v_target_x3f_680_);
v_idx_681_ = lean_ctor_get(v_a_675_, 7);
lean_inc(v_idx_681_);
lean_dec(v_a_675_);
v___x_682_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_idx_681_, v_self_679_, v_fst_668_);
if (lean_obj_tag(v_target_x3f_680_) == 1)
{
lean_object* v_val_683_; lean_object* v___x_685_; 
lean_del_object(v___x_677_);
lean_dec(v_snd_669_);
v_val_683_ = lean_ctor_get(v_target_x3f_680_, 0);
lean_inc(v_val_683_);
lean_dec_ref_known(v_target_x3f_680_, 1);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 1, v_val_683_);
lean_ctor_set(v___x_671_, 0, v___x_682_);
v___x_685_ = v___x_671_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_val_683_);
v___x_685_ = v_reuseFailAlloc_687_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
v_a_661_ = v___x_685_;
goto _start;
}
}
else
{
lean_object* v___x_689_; 
lean_dec(v_target_x3f_680_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_682_);
v___x_689_ = v___x_671_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_snd_669_);
v___x_689_ = v_reuseFailAlloc_693_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_691_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_689_);
v___x_691_ = v___x_677_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
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
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_del_object(v___x_671_);
lean_dec(v_snd_669_);
lean_dec(v_fst_668_);
v_a_695_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_674_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_674_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_661_ = stack[0].m_obj;
lean_object* v___y_662_ = stack[1].m_obj;
lean_object* v___y_663_ = stack[2].m_obj;
lean_object* v___y_664_ = stack[3].m_obj;
lean_object* v___y_665_ = stack[4].m_obj;
lean_object* v___y_666_ = stack[5].m_obj;
lean_object* v_res_704_;
v_res_704_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(v_a_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
stack->m_obj
 = v_res_704_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg___boxed(lean_object* v_a_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(v_a_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
return v_res_712_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_713_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_714_ = lean_unsigned_to_nat(2u);
v___x_715_ = lean_unsigned_to_nat(89u);
v___x_716_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__1));
v___x_717_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_718_ = l_mkPanicMessageWithDecl(v___x_717_, v___x_716_, v___x_715_, v___x_714_, v___x_713_);
return v___x_718_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(lean_object* v_lhs_719_, lean_object* v_rhs_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_visited_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_visited_732_ = lean_box(1);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v_visited_732_);
lean_ctor_set(v___x_733_, 1, v_lhs_719_);
v___x_734_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(v___x_733_, v_a_721_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v_fst_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_765_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
v_fst_736_ = lean_ctor_get(v_a_735_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v_a_735_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v_a_735_, 1);
lean_dec(v_unused_766_);
v___x_738_ = v_a_735_;
v_isShared_739_ = v_isSharedCheck_765_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_fst_736_);
lean_dec(v_a_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_765_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_740_ = lean_box(0);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 1, v_rhs_720_);
lean_ctor_set(v___x_738_, 0, v___x_740_);
v___x_742_ = v___x_738_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_rhs_720_);
v___x_742_ = v_reuseFailAlloc_764_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; 
v___x_743_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(v_fst_736_, v___x_742_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
lean_dec(v_fst_736_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_755_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_755_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_755_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_755_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v_fst_748_; 
v_fst_748_ = lean_ctor_get(v_a_744_, 0);
lean_inc(v_fst_748_);
lean_dec(v_a_744_);
if (lean_obj_tag(v_fst_748_) == 0)
{
lean_object* v___x_749_; lean_object* v___x_750_; 
lean_del_object(v___x_746_);
v___x_749_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0);
v___x_750_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_749_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
return v___x_750_;
}
else
{
lean_object* v_val_751_; lean_object* v___x_753_; 
v_val_751_ = lean_ctor_get(v_fst_748_, 0);
lean_inc(v_val_751_);
lean_dec_ref_known(v_fst_748_, 1);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v_val_751_);
v___x_753_ = v___x_746_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_val_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
v_a_756_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_743_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_743_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec_ref(v_rhs_720_);
v_a_767_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_734_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_734_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_719_ = stack[0].m_obj;
lean_object* v_rhs_720_ = stack[1].m_obj;
lean_object* v_a_721_ = stack[2].m_obj;
lean_object* v_a_722_ = stack[3].m_obj;
lean_object* v_a_723_ = stack[4].m_obj;
lean_object* v_a_724_ = stack[5].m_obj;
lean_object* v_a_725_ = stack[6].m_obj;
lean_object* v_a_726_ = stack[7].m_obj;
lean_object* v_a_727_ = stack[8].m_obj;
lean_object* v_a_728_ = stack[9].m_obj;
lean_object* v_a_729_ = stack[10].m_obj;
lean_object* v_a_730_ = stack[11].m_obj;
lean_object* v_res_775_;
v_res_775_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(v_lhs_719_, v_rhs_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
stack->m_obj
 = v_res_775_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___boxed(lean_object* v_lhs_776_, lean_object* v_rhs_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(v_lhs_776_, v_rhs_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
lean_dec(v_a_779_);
lean_dec(v_a_778_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0(lean_object* v_00_u03b2_790_, lean_object* v_k_791_, lean_object* v_v_792_, lean_object* v_t_793_, lean_object* v_hl_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_k_791_, v_v_792_, v_t_793_);
return v___x_795_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1(lean_object* v_inst_796_, lean_object* v_a_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(v_a_797_, v___y_798_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
return v___x_809_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_797_ = stack[1].m_obj;
lean_object* v___y_798_ = stack[2].m_obj;
lean_object* v___y_799_ = stack[3].m_obj;
lean_object* v___y_800_ = stack[4].m_obj;
lean_object* v___y_801_ = stack[5].m_obj;
lean_object* v___y_802_ = stack[6].m_obj;
lean_object* v___y_803_ = stack[7].m_obj;
lean_object* v___y_804_ = stack[8].m_obj;
lean_object* v___y_805_ = stack[9].m_obj;
lean_object* v___y_806_ = stack[10].m_obj;
lean_object* v___y_807_ = stack[11].m_obj;
lean_object* v_res_810_;
v_res_810_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1(lean_box(0), v_a_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
stack->m_obj
 = v_res_810_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___boxed(lean_object* v_inst_811_, lean_object* v_a_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1(v_inst_811_, v_a_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec(v___y_813_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2(lean_object* v_00_u03b4_825_, lean_object* v_t_826_, lean_object* v_k_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(v_t_826_, v_k_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___boxed(lean_object* v_00_u03b4_829_, lean_object* v_t_830_, lean_object* v_k_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2(v_00_u03b4_829_, v_t_830_, v_k_831_);
lean_dec(v_k_831_);
lean_dec(v_t_830_);
return v_res_832_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4(lean_object* v___x_833_, lean_object* v_inst_834_, lean_object* v_a_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(v___x_833_, v_a_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
return v___x_847_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_833_ = stack[0].m_obj;
lean_object* v_a_835_ = stack[2].m_obj;
lean_object* v___y_836_ = stack[3].m_obj;
lean_object* v___y_837_ = stack[4].m_obj;
lean_object* v___y_838_ = stack[5].m_obj;
lean_object* v___y_839_ = stack[6].m_obj;
lean_object* v___y_840_ = stack[7].m_obj;
lean_object* v___y_841_ = stack[8].m_obj;
lean_object* v___y_842_ = stack[9].m_obj;
lean_object* v___y_843_ = stack[10].m_obj;
lean_object* v___y_844_ = stack[11].m_obj;
lean_object* v___y_845_ = stack[12].m_obj;
lean_object* v_res_848_;
v_res_848_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4(v___x_833_, lean_box(0), v_a_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
stack->m_obj
 = v_res_848_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___boxed(lean_object* v___x_849_, lean_object* v_inst_850_, lean_object* v_a_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4(v___x_849_, v_inst_850_, v_a_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec(v___y_852_);
lean_dec(v___x_849_);
return v_res_863_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(lean_object* v_info_864_, lean_object* v_lhs_865_, lean_object* v_rhs_866_, lean_object* v_i_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
uint8_t v___x_879_; 
v___x_879_ = l_Lean_Expr_isApp(v_lhs_865_);
if (v___x_879_ == 0)
{
uint8_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
lean_dec(v_i_867_);
lean_dec_ref(v_rhs_866_);
lean_dec_ref(v_lhs_865_);
v___x_880_ = 1;
v___x_881_ = lean_box(v___x_880_);
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
return v___x_882_;
}
else
{
lean_object* v_a_u2081_883_; lean_object* v_a_u2082_884_; lean_object* v___x_885_; lean_object* v_i_886_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; size_t v___x_901_; size_t v___x_902_; uint8_t v___x_903_; 
v_a_u2081_883_ = l_Lean_Expr_appArg_x21(v_lhs_865_);
v_a_u2082_884_ = l_Lean_Expr_appArg_x21(v_rhs_866_);
v___x_885_ = lean_unsigned_to_nat(1u);
v_i_886_ = lean_nat_sub(v_i_867_, v___x_885_);
lean_dec(v_i_867_);
v___x_901_ = lean_ptr_addr(v_a_u2081_883_);
lean_dec_ref(v_a_u2081_883_);
v___x_902_ = lean_ptr_addr(v_a_u2082_884_);
lean_dec_ref(v_a_u2082_884_);
v___x_903_ = lean_usize_dec_eq(v___x_901_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = lean_array_get_size(v_info_864_);
v___x_905_ = lean_nat_dec_lt(v_i_886_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; lean_object* v___x_907_; 
lean_dec(v_i_886_);
lean_dec_ref(v_rhs_866_);
lean_dec_ref(v_lhs_865_);
v___x_906_ = lean_box(v___x_905_);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
return v___x_907_;
}
else
{
lean_object* v___x_908_; uint8_t v_hasFwdDeps_909_; 
v___x_908_ = lean_array_fget_borrowed(v_info_864_, v_i_886_);
v_hasFwdDeps_909_ = lean_ctor_get_uint8(v___x_908_, sizeof(void*)*1 + 1);
if (v_hasFwdDeps_909_ == 0)
{
v___y_888_ = v_a_868_;
v___y_889_ = v_a_869_;
v___y_890_ = v_a_870_;
v___y_891_ = v_a_871_;
v___y_892_ = v_a_872_;
v___y_893_ = v_a_873_;
v___y_894_ = v_a_874_;
v___y_895_ = v_a_875_;
v___y_896_ = v_a_876_;
v___y_897_ = v_a_877_;
goto v___jp_887_;
}
else
{
lean_object* v___x_910_; lean_object* v___x_911_; 
lean_dec(v_i_886_);
lean_dec_ref(v_rhs_866_);
lean_dec_ref(v_lhs_865_);
v___x_910_ = lean_box(v___x_903_);
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
return v___x_911_;
}
}
}
else
{
v___y_888_ = v_a_868_;
v___y_889_ = v_a_869_;
v___y_890_ = v_a_870_;
v___y_891_ = v_a_871_;
v___y_892_ = v_a_872_;
v___y_893_ = v_a_873_;
v___y_894_ = v_a_874_;
v___y_895_ = v_a_875_;
v___y_896_ = v_a_876_;
v___y_897_ = v_a_877_;
goto v___jp_887_;
}
v___jp_887_:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = l_Lean_Expr_appFn_x21(v_lhs_865_);
lean_dec_ref(v_lhs_865_);
v___x_899_ = l_Lean_Expr_appFn_x21(v_rhs_866_);
lean_dec_ref(v_rhs_866_);
v_lhs_865_ = v___x_898_;
v_rhs_866_ = v___x_899_;
v_i_867_ = v_i_886_;
v_a_868_ = v___y_888_;
v_a_869_ = v___y_889_;
v_a_870_ = v___y_890_;
v_a_871_ = v___y_891_;
v_a_872_ = v___y_892_;
v_a_873_ = v___y_893_;
v_a_874_ = v___y_894_;
v_a_875_ = v___y_895_;
v_a_876_ = v___y_896_;
v_a_877_ = v___y_897_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_864_ = stack[0].m_obj;
lean_object* v_lhs_865_ = stack[1].m_obj;
lean_object* v_rhs_866_ = stack[2].m_obj;
lean_object* v_i_867_ = stack[3].m_obj;
lean_object* v_a_868_ = stack[4].m_obj;
lean_object* v_a_869_ = stack[5].m_obj;
lean_object* v_a_870_ = stack[6].m_obj;
lean_object* v_a_871_ = stack[7].m_obj;
lean_object* v_a_872_ = stack[8].m_obj;
lean_object* v_a_873_ = stack[9].m_obj;
lean_object* v_a_874_ = stack[10].m_obj;
lean_object* v_a_875_ = stack[11].m_obj;
lean_object* v_a_876_ = stack[12].m_obj;
lean_object* v_a_877_ = stack[13].m_obj;
lean_object* v_res_912_;
v_res_912_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(v_info_864_, v_lhs_865_, v_rhs_866_, v_i_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
stack->m_obj
 = v_res_912_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop___boxed(lean_object* v_info_913_, lean_object* v_lhs_914_, lean_object* v_rhs_915_, lean_object* v_i_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(v_info_913_, v_lhs_914_, v_rhs_915_, v_i_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec(v_a_917_);
lean_dec_ref(v_info_913_);
return v_res_928_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(lean_object* v_lhs_929_, lean_object* v_rhs_930_, lean_object* v_f_931_, lean_object* v_g_932_, lean_object* v_numArgs_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
size_t v___x_945_; size_t v___x_946_; uint8_t v___x_947_; 
v___x_945_ = lean_ptr_addr(v_f_931_);
v___x_946_ = lean_ptr_addr(v_g_932_);
v___x_947_ = lean_usize_dec_eq(v___x_945_, v___x_946_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; 
lean_dec(v_numArgs_933_);
lean_dec_ref(v_f_931_);
lean_dec_ref(v_rhs_930_);
lean_dec_ref(v_lhs_929_);
v___x_948_ = lean_box(v___x_947_);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = lean_box(0);
v___x_951_ = l_Lean_Meta_getFunInfo(v_f_931_, v___x_950_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v_paramInfo_953_; lean_object* v___x_954_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
v_paramInfo_953_ = lean_ctor_get(v_a_952_, 0);
lean_inc_ref(v_paramInfo_953_);
lean_dec(v_a_952_);
v___x_954_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(v_paramInfo_953_, v_lhs_929_, v_rhs_930_, v_numArgs_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
lean_dec_ref(v_paramInfo_953_);
return v___x_954_;
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_dec(v_numArgs_933_);
lean_dec_ref(v_rhs_930_);
lean_dec_ref(v_lhs_929_);
v_a_955_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_951_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_951_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_929_ = stack[0].m_obj;
lean_object* v_rhs_930_ = stack[1].m_obj;
lean_object* v_f_931_ = stack[2].m_obj;
lean_object* v_g_932_ = stack[3].m_obj;
lean_object* v_numArgs_933_ = stack[4].m_obj;
lean_object* v_a_934_ = stack[5].m_obj;
lean_object* v_a_935_ = stack[6].m_obj;
lean_object* v_a_936_ = stack[7].m_obj;
lean_object* v_a_937_ = stack[8].m_obj;
lean_object* v_a_938_ = stack[9].m_obj;
lean_object* v_a_939_ = stack[10].m_obj;
lean_object* v_a_940_ = stack[11].m_obj;
lean_object* v_a_941_ = stack[12].m_obj;
lean_object* v_a_942_ = stack[13].m_obj;
lean_object* v_a_943_ = stack[14].m_obj;
lean_object* v_res_963_;
v_res_963_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(v_lhs_929_, v_rhs_930_, v_f_931_, v_g_932_, v_numArgs_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
stack->m_obj
 = v_res_963_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget___boxed(lean_object* v_lhs_964_, lean_object* v_rhs_965_, lean_object* v_f_966_, lean_object* v_g_967_, lean_object* v_numArgs_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(v_lhs_964_, v_rhs_965_, v_f_966_, v_g_967_, v_numArgs_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec(v_a_969_);
lean_dec_ref(v_g_967_);
return v_res_980_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(lean_object* v_msg_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_95148__overap_994_; lean_object* v___x_995_; 
v___x_993_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0);
v___x_95148__overap_994_ = lean_panic_fn_borrowed(v___x_993_, v_msg_981_);
lean_inc(v___y_991_);
lean_inc_ref(v___y_990_);
lean_inc(v___y_989_);
lean_inc_ref(v___y_988_);
lean_inc(v___y_987_);
lean_inc_ref(v___y_986_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc(v___y_983_);
lean_inc(v___y_982_);
v___x_995_ = lean_apply_11(v___x_95148__overap_994_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, lean_box(0));
return v___x_995_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_981_ = stack[0].m_obj;
lean_object* v___y_982_ = stack[1].m_obj;
lean_object* v___y_983_ = stack[2].m_obj;
lean_object* v___y_984_ = stack[3].m_obj;
lean_object* v___y_985_ = stack[4].m_obj;
lean_object* v___y_986_ = stack[5].m_obj;
lean_object* v___y_987_ = stack[6].m_obj;
lean_object* v___y_988_ = stack[7].m_obj;
lean_object* v___y_989_ = stack[8].m_obj;
lean_object* v___y_990_ = stack[9].m_obj;
lean_object* v___y_991_ = stack[10].m_obj;
lean_object* v_res_996_;
v_res_996_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v_msg_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
stack->m_obj
 = v_res_996_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___boxed(lean_object* v_msg_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v_msg_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec(v___y_998_);
return v_res_1009_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = l_Lean_maxRecDepthErrorMessage;
v___x_1016_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3);
v___x_1018_ = l_Lean_MessageData_ofFormat(v___x_1017_);
return v___x_1018_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4);
v___x_1020_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__2));
v___x_1021_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v___x_1019_);
return v___x_1021_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(lean_object* v_ref_1022_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v_ref_1022_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1022_ = stack[0].m_obj;
lean_object* v_res_1027_;
v_res_1027_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1022_);
stack->m_obj
 = v_res_1027_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___boxed(lean_object* v_ref_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1028_);
return v_res_1030_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0(lean_object* v_k_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v_b_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v___x_1044_; 
lean_inc(v___y_1042_);
lean_inc_ref(v___y_1041_);
lean_inc(v___y_1040_);
lean_inc_ref(v___y_1039_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
lean_inc(v___y_1035_);
lean_inc_ref(v___y_1034_);
lean_inc(v___y_1033_);
lean_inc(v___y_1032_);
v___x_1044_ = lean_apply_12(v_k_1031_, v_b_1038_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, lean_box(0));
return v___x_1044_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1031_ = stack[0].m_obj;
lean_object* v___y_1032_ = stack[1].m_obj;
lean_object* v___y_1033_ = stack[2].m_obj;
lean_object* v___y_1034_ = stack[3].m_obj;
lean_object* v___y_1035_ = stack[4].m_obj;
lean_object* v___y_1036_ = stack[5].m_obj;
lean_object* v___y_1037_ = stack[6].m_obj;
lean_object* v_b_1038_ = stack[7].m_obj;
lean_object* v___y_1039_ = stack[8].m_obj;
lean_object* v___y_1040_ = stack[9].m_obj;
lean_object* v___y_1041_ = stack[10].m_obj;
lean_object* v___y_1042_ = stack[11].m_obj;
lean_object* v_res_1045_;
v_res_1045_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0(v_k_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v_b_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
stack->m_obj
 = v_res_1045_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0___boxed(lean_object* v_k_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v_b_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0(v_k_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v_b_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec(v___y_1047_);
return v_res_1059_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(lean_object* v_name_1060_, uint8_t v_bi_1061_, lean_object* v_type_1062_, lean_object* v_k_1063_, uint8_t v_kind_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v___f_1076_; lean_object* v___x_1077_; 
lean_inc(v___y_1070_);
lean_inc_ref(v___y_1069_);
lean_inc(v___y_1068_);
lean_inc_ref(v___y_1067_);
lean_inc(v___y_1066_);
lean_inc(v___y_1065_);
v___f_1076_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_1076_, 0, v_k_1063_);
lean_closure_set(v___f_1076_, 1, v___y_1065_);
lean_closure_set(v___f_1076_, 2, v___y_1066_);
lean_closure_set(v___f_1076_, 3, v___y_1067_);
lean_closure_set(v___f_1076_, 4, v___y_1068_);
lean_closure_set(v___f_1076_, 5, v___y_1069_);
lean_closure_set(v___f_1076_, 6, v___y_1070_);
v___x_1077_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1060_, v_bi_1061_, v_type_1062_, v___f_1076_, v_kind_1064_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1077_) == 0)
{
return v___x_1077_;
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1060_ = stack[0].m_obj;
uint8_t v_bi_1061_ = stack[1].m_num;
lean_object* v_type_1062_ = stack[2].m_obj;
lean_object* v_k_1063_ = stack[3].m_obj;
uint8_t v_kind_1064_ = stack[4].m_num;
lean_object* v___y_1065_ = stack[5].m_obj;
lean_object* v___y_1066_ = stack[6].m_obj;
lean_object* v___y_1067_ = stack[7].m_obj;
lean_object* v___y_1068_ = stack[8].m_obj;
lean_object* v___y_1069_ = stack[9].m_obj;
lean_object* v___y_1070_ = stack[10].m_obj;
lean_object* v___y_1071_ = stack[11].m_obj;
lean_object* v___y_1072_ = stack[12].m_obj;
lean_object* v___y_1073_ = stack[13].m_obj;
lean_object* v___y_1074_ = stack[14].m_obj;
lean_object* v_res_1086_;
v_res_1086_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_1060_, v_bi_1061_, v_type_1062_, v_k_1063_, v_kind_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
stack->m_obj
 = v_res_1086_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___boxed(lean_object* v_name_1087_, lean_object* v_bi_1088_, lean_object* v_type_1089_, lean_object* v_k_1090_, lean_object* v_kind_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
uint8_t v_bi_boxed_1103_; uint8_t v_kind_boxed_1104_; lean_object* v_res_1105_; 
v_bi_boxed_1103_ = lean_unbox(v_bi_1088_);
v_kind_boxed_1104_ = lean_unbox(v_kind_1091_);
v_res_1105_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_1087_, v_bi_boxed_1103_, v_type_1089_, v_k_1090_, v_kind_boxed_1104_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec(v___y_1092_);
return v_res_1105_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(lean_object* v_name_1106_, lean_object* v_type_1107_, lean_object* v_k_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
uint8_t v___x_1120_; uint8_t v___x_1121_; lean_object* v___x_1122_; 
v___x_1120_ = 0;
v___x_1121_ = 0;
v___x_1122_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_1106_, v___x_1120_, v_type_1107_, v_k_1108_, v___x_1121_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
return v___x_1122_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1106_ = stack[0].m_obj;
lean_object* v_type_1107_ = stack[1].m_obj;
lean_object* v_k_1108_ = stack[2].m_obj;
lean_object* v___y_1109_ = stack[3].m_obj;
lean_object* v___y_1110_ = stack[4].m_obj;
lean_object* v___y_1111_ = stack[5].m_obj;
lean_object* v___y_1112_ = stack[6].m_obj;
lean_object* v___y_1113_ = stack[7].m_obj;
lean_object* v___y_1114_ = stack[8].m_obj;
lean_object* v___y_1115_ = stack[9].m_obj;
lean_object* v___y_1116_ = stack[10].m_obj;
lean_object* v___y_1117_ = stack[11].m_obj;
lean_object* v___y_1118_ = stack[12].m_obj;
lean_object* v_res_1123_;
v_res_1123_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_name_1106_, v_type_1107_, v_k_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
stack->m_obj
 = v_res_1123_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg___boxed(lean_object* v_name_1124_, lean_object* v_type_1125_, lean_object* v_k_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_name_1124_, v_type_1125_, v_k_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec(v___y_1127_);
return v_res_1138_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1139_; lean_object* v_dummy_1140_; 
v___x_1139_ = lean_box(0);
v_dummy_1140_ = l_Lean_Expr_sort___override(v___x_1139_);
return v_dummy_1140_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0(lean_object* v_numArgs_1141_, lean_object* v_rhs_1142_, lean_object* v_lhs_1143_, uint8_t v___x_1144_, uint8_t v___x_1145_, lean_object* v_x_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_dummy_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_dummy_1158_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0);
lean_inc(v_numArgs_1141_);
v___x_1159_ = lean_mk_array(v_numArgs_1141_, v_dummy_1158_);
v___x_1160_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_numArgs_1141_, v_rhs_1142_, v___x_1159_);
lean_inc_ref(v_x_1146_);
v___x_1161_ = l_Lean_mkAppN(v_x_1146_, v___x_1160_);
lean_dec_ref(v___x_1160_);
v___x_1162_ = l_Lean_Meta_mkHEq(v_lhs_1143_, v___x_1161_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; lean_object* v___x_1168_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = lean_mk_empty_array_with_capacity(v___x_1164_);
v___x_1166_ = lean_array_push(v___x_1165_, v_x_1146_);
v___x_1167_ = 1;
v___x_1168_ = l_Lean_Meta_mkLambdaFVars(v___x_1166_, v_a_1163_, v___x_1144_, v___x_1145_, v___x_1144_, v___x_1145_, v___x_1167_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
lean_dec_ref(v___x_1166_);
return v___x_1168_;
}
else
{
lean_dec_ref(v_x_1146_);
return v___x_1162_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_numArgs_1141_ = stack[0].m_obj;
lean_object* v_rhs_1142_ = stack[1].m_obj;
lean_object* v_lhs_1143_ = stack[2].m_obj;
uint8_t v___x_1144_ = stack[3].m_num;
uint8_t v___x_1145_ = stack[4].m_num;
lean_object* v_x_1146_ = stack[5].m_obj;
lean_object* v___y_1147_ = stack[6].m_obj;
lean_object* v___y_1148_ = stack[7].m_obj;
lean_object* v___y_1149_ = stack[8].m_obj;
lean_object* v___y_1150_ = stack[9].m_obj;
lean_object* v___y_1151_ = stack[10].m_obj;
lean_object* v___y_1152_ = stack[11].m_obj;
lean_object* v___y_1153_ = stack[12].m_obj;
lean_object* v___y_1154_ = stack[13].m_obj;
lean_object* v___y_1155_ = stack[14].m_obj;
lean_object* v___y_1156_ = stack[15].m_obj;
lean_object* v_res_1169_;
v_res_1169_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0(v_numArgs_1141_, v_rhs_1142_, v_lhs_1143_, v___x_1144_, v___x_1145_, v_x_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
stack->m_obj
 = v_res_1169_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___boxed(lean_object** _args){
lean_object* v_numArgs_1170_ = _args[0];
lean_object* v_rhs_1171_ = _args[1];
lean_object* v_lhs_1172_ = _args[2];
lean_object* v___x_1173_ = _args[3];
lean_object* v___x_1174_ = _args[4];
lean_object* v_x_1175_ = _args[5];
lean_object* v___y_1176_ = _args[6];
lean_object* v___y_1177_ = _args[7];
lean_object* v___y_1178_ = _args[8];
lean_object* v___y_1179_ = _args[9];
lean_object* v___y_1180_ = _args[10];
lean_object* v___y_1181_ = _args[11];
lean_object* v___y_1182_ = _args[12];
lean_object* v___y_1183_ = _args[13];
lean_object* v___y_1184_ = _args[14];
lean_object* v___y_1185_ = _args[15];
lean_object* v___y_1186_ = _args[16];
_start:
{
uint8_t v___x_103027__boxed_1187_; uint8_t v___x_103028__boxed_1188_; lean_object* v_res_1189_; 
v___x_103027__boxed_1187_ = lean_unbox(v___x_1173_);
v___x_103028__boxed_1188_ = lean_unbox(v___x_1174_);
v_res_1189_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0(v_numArgs_1170_, v_rhs_1171_, v_lhs_1172_, v___x_103027__boxed_1187_, v___x_103028__boxed_1188_, v_x_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec(v___y_1176_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_spec__13(lean_object* v_msg_1190_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = l_Lean_instInhabitedExpr;
v___x_1192_ = lean_panic_fn_borrowed(v___x_1191_, v_msg_1190_);
return v___x_1192_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(lean_object* v_msgData_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v___x_1199_; lean_object* v_env_1200_; uint8_t v___x_1201_; lean_object* v_env_1202_; lean_object* v___x_1203_; lean_object* v_toCold_1204_; lean_object* v_mctx_1205_; lean_object* v_lctx_1206_; lean_object* v_options_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1199_ = lean_st_ref_get(v___y_1197_);
v_env_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc_ref(v_env_1200_);
lean_dec(v___x_1199_);
v___x_1201_ = 0;
v_env_1202_ = l_Lean_Environment_setRecordingDeps(v_env_1200_, v___x_1201_);
v___x_1203_ = lean_st_ref_get(v___y_1195_);
v_toCold_1204_ = lean_ctor_get(v___y_1196_, 0);
v_mctx_1205_ = lean_ctor_get(v___x_1203_, 0);
lean_inc_ref(v_mctx_1205_);
lean_dec(v___x_1203_);
v_lctx_1206_ = lean_ctor_get(v___y_1194_, 2);
v_options_1207_ = lean_ctor_get(v_toCold_1204_, 2);
lean_inc_ref(v_options_1207_);
lean_inc_ref(v_lctx_1206_);
v___x_1208_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1208_, 0, v_env_1202_);
lean_ctor_set(v___x_1208_, 1, v_mctx_1205_);
lean_ctor_set(v___x_1208_, 2, v_lctx_1206_);
lean_ctor_set(v___x_1208_, 3, v_options_1207_);
v___x_1209_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v_msgData_1193_);
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1193_ = stack[0].m_obj;
lean_object* v___y_1194_ = stack[1].m_obj;
lean_object* v___y_1195_ = stack[2].m_obj;
lean_object* v___y_1196_ = stack[3].m_obj;
lean_object* v___y_1197_ = stack[4].m_obj;
lean_object* v_res_1211_;
v_res_1211_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(v_msgData_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
stack->m_obj
 = v_res_1211_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16___boxed(lean_object* v_msgData_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(v_msgData_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
return v_res_1218_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(lean_object* v_msg_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_ref_1225_; lean_object* v___x_1226_; lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1235_; 
v_ref_1225_ = lean_ctor_get(v___y_1222_, 2);
v___x_1226_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(v_msg_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1229_ = v___x_1226_;
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1226_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1233_; 
lean_inc(v_ref_1225_);
v___x_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1231_, 0, v_ref_1225_);
lean_ctor_set(v___x_1231_, 1, v_a_1227_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set_tag(v___x_1229_, 1);
lean_ctor_set(v___x_1229_, 0, v___x_1231_);
v___x_1233_ = v___x_1229_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1219_ = stack[0].m_obj;
lean_object* v___y_1220_ = stack[1].m_obj;
lean_object* v___y_1221_ = stack[2].m_obj;
lean_object* v___y_1222_ = stack[3].m_obj;
lean_object* v___y_1223_ = stack[4].m_obj;
lean_object* v_res_1236_;
v_res_1236_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v_msg_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
stack->m_obj
 = v_res_1236_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg___boxed(lean_object* v_msg_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v_msg_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
return v_res_1243_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__0));
v___x_1246_ = l_Lean_stringToMessageData(v___x_1245_);
return v___x_1246_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__2));
v___x_1249_ = l_Lean_stringToMessageData(v___x_1248_);
return v___x_1249_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(lean_object* v_lhs_1250_, lean_object* v_rhs_1251_, lean_object* v_00_u03b1_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1264_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1);
v___x_1265_ = l_Lean_indentExpr(v_lhs_1250_);
v___x_1266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1264_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3);
v___x_1268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1266_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = l_Lean_indentExpr(v_rhs_1251_);
v___x_1270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1268_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
v___x_1271_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v___x_1270_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
return v___x_1271_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_1250_ = stack[0].m_obj;
lean_object* v_rhs_1251_ = stack[1].m_obj;
lean_object* v___y_1253_ = stack[3].m_obj;
lean_object* v___y_1254_ = stack[4].m_obj;
lean_object* v___y_1255_ = stack[5].m_obj;
lean_object* v___y_1256_ = stack[6].m_obj;
lean_object* v___y_1257_ = stack[7].m_obj;
lean_object* v___y_1258_ = stack[8].m_obj;
lean_object* v___y_1259_ = stack[9].m_obj;
lean_object* v___y_1260_ = stack[10].m_obj;
lean_object* v___y_1261_ = stack[11].m_obj;
lean_object* v___y_1262_ = stack[12].m_obj;
lean_object* v_res_1272_;
v_res_1272_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1250_, v_rhs_1251_, lean_box(0), v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
stack->m_obj
 = v_res_1272_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___boxed(lean_object* v_lhs_1273_, lean_object* v_rhs_1274_, lean_object* v_00_u03b1_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1273_, v_rhs_1274_, v_00_u03b1_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec(v___y_1276_);
return v_res_1287_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__1));
v___x_1291_ = lean_unsigned_to_nat(4u);
v___x_1292_ = lean_unsigned_to_nat(198u);
v___x_1293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__0));
v___x_1294_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1295_ = l_mkPanicMessageWithDecl(v___x_1294_, v___x_1293_, v___x_1292_, v___x_1291_, v___x_1290_);
return v___x_1295_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1298_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__1));
v___x_1299_ = lean_unsigned_to_nat(4u);
v___x_1300_ = lean_unsigned_to_nat(318u);
v___x_1301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0));
v___x_1302_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1303_ = l_mkPanicMessageWithDecl(v___x_1302_, v___x_1301_, v___x_1300_, v___x_1299_, v___x_1298_);
return v___x_1303_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1305_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1306_ = lean_unsigned_to_nat(36u);
v___x_1307_ = lean_unsigned_to_nat(153u);
v___x_1308_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0));
v___x_1309_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1310_ = l_mkPanicMessageWithDecl(v___x_1309_, v___x_1308_, v___x_1307_, v___x_1306_, v___x_1305_);
return v___x_1310_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1311_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1312_ = lean_unsigned_to_nat(34u);
v___x_1313_ = lean_unsigned_to_nat(154u);
v___x_1314_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0));
v___x_1315_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1316_ = l_mkPanicMessageWithDecl(v___x_1315_, v___x_1314_, v___x_1313_, v___x_1312_, v___x_1311_);
return v___x_1316_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1318_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__3));
v___x_1319_ = lean_unsigned_to_nat(4u);
v___x_1320_ = lean_unsigned_to_nat(155u);
v___x_1321_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0));
v___x_1322_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1323_ = l_mkPanicMessageWithDecl(v___x_1322_, v___x_1321_, v___x_1320_, v___x_1319_, v___x_1318_);
return v___x_1323_;
}
}
lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof(lean_object* v_lhs_1336_, lean_object* v_rhs_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; uint8_t v___y_1384_; uint8_t v___y_1385_; lean_object* v_toCold_1421_; lean_object* v_currRecDepth_1422_; lean_object* v_ref_1423_; uint16_t v_optionFlags_1424_; uint8_t v_suppressElabErrors_1425_; uint8_t v_isRecordingDeps_1426_; lean_object* v_maxRecDepth_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v_toCold_1421_ = lean_ctor_get(v_a_1346_, 0);
v_currRecDepth_1422_ = lean_ctor_get(v_a_1346_, 1);
v_ref_1423_ = lean_ctor_get(v_a_1346_, 2);
v_optionFlags_1424_ = lean_ctor_get_uint16(v_a_1346_, sizeof(void*)*3);
v_suppressElabErrors_1425_ = lean_ctor_get_uint8(v_a_1346_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1426_ = lean_ctor_get_uint8(v_a_1346_, sizeof(void*)*3 + 3);
v_maxRecDepth_1427_ = lean_ctor_get(v_toCold_1421_, 3);
v___x_1428_ = l_Lean_Expr_cleanupAnnotations(v_lhs_1336_);
v___x_1429_ = l_Lean_Expr_isApp(v___x_1428_);
v___x_1459_ = lean_unsigned_to_nat(0u);
v___x_1460_ = lean_nat_dec_eq(v_maxRecDepth_1427_, v___x_1459_);
if (v___x_1460_ == 0)
{
uint8_t v___x_1461_; 
v___x_1461_ = lean_nat_dec_eq(v_currRecDepth_1422_, v_maxRecDepth_1427_);
if (v___x_1461_ == 0)
{
goto v___jp_1430_;
}
else
{
lean_object* v___x_1462_; 
lean_dec_ref(v___x_1428_);
lean_dec_ref(v_rhs_1337_);
lean_inc(v_ref_1423_);
v___x_1462_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1423_);
return v___x_1462_;
}
}
else
{
goto v___jp_1430_;
}
v___jp_1349_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1);
v___x_1361_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1360_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec_ref(v___y_1358_);
return v___x_1361_;
}
v___jp_1362_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2);
v___x_1374_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1373_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec_ref(v___y_1371_);
return v___x_1374_;
}
v___jp_1375_:
{
if (v___y_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
lean_dec_ref(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec_ref(v___y_1376_);
v___x_1386_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4);
v___x_1387_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1386_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v___y_1383_, v_a_1347_);
lean_dec_ref(v___y_1383_);
return v___x_1387_;
}
else
{
lean_object* v___x_1388_; size_t v___x_1389_; size_t v___x_1390_; uint8_t v___x_1391_; 
v___x_1388_ = l_Lean_Expr_constLevels_x21(v___y_1377_);
lean_dec_ref(v___y_1377_);
v___x_1389_ = lean_ptr_addr(v___y_1380_);
v___x_1390_ = lean_ptr_addr(v___y_1379_);
v___x_1391_ = lean_usize_dec_eq(v___x_1389_, v___x_1390_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; 
lean_inc_ref(v___y_1376_);
lean_inc_ref(v___y_1381_);
v___x_1392_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1381_, v___y_1376_, v___y_1384_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v___y_1383_, v_a_1347_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1394_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref_known(v___x_1392_, 1);
lean_inc_ref(v___y_1378_);
lean_inc_ref(v___y_1382_);
v___x_1394_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1382_, v___y_1378_, v___y_1384_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v___y_1383_, v_a_1347_);
lean_dec_ref(v___y_1383_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1405_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1397_ = v___x_1394_;
v_isShared_1398_ = v_isSharedCheck_1405_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1394_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1405_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1403_; 
v___x_1399_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6));
v___x_1400_ = l_Lean_mkConst(v___x_1399_, v___x_1388_);
v___x_1401_ = l_Lean_mkApp8(v___x_1400_, v___y_1380_, v___y_1379_, v___y_1381_, v___y_1382_, v___y_1378_, v___y_1376_, v_a_1393_, v_a_1395_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1401_);
v___x_1403_ = v___x_1397_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
else
{
lean_dec(v_a_1393_);
lean_dec(v___x_1388_);
lean_dec_ref(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec_ref(v___y_1376_);
return v___x_1394_;
}
}
else
{
lean_dec(v___x_1388_);
lean_dec_ref(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec_ref(v___y_1376_);
return v___x_1392_;
}
}
else
{
uint8_t v___x_1406_; lean_object* v___x_1407_; 
lean_dec_ref(v___y_1379_);
v___x_1406_ = 0;
lean_inc_ref(v___y_1376_);
lean_inc_ref(v___y_1381_);
v___x_1407_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1381_, v___y_1376_, v___x_1406_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v___y_1383_, v_a_1347_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1409_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___x_1407_, 1);
lean_inc_ref(v___y_1378_);
lean_inc_ref(v___y_1382_);
v___x_1409_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1382_, v___y_1378_, v___x_1406_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v___y_1383_, v_a_1347_);
lean_dec_ref(v___y_1383_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1420_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1412_ = v___x_1409_;
v_isShared_1413_ = v_isSharedCheck_1420_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1420_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1414_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8));
v___x_1415_ = l_Lean_mkConst(v___x_1414_, v___x_1388_);
v___x_1416_ = l_Lean_mkApp7(v___x_1415_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1378_, v___y_1376_, v_a_1408_, v_a_1410_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v___x_1416_);
v___x_1418_ = v___x_1412_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
else
{
lean_dec(v_a_1408_);
lean_dec(v___x_1388_);
lean_dec_ref(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec_ref(v___y_1378_);
lean_dec_ref(v___y_1376_);
return v___x_1409_;
}
}
else
{
lean_dec(v___x_1388_);
lean_dec_ref(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec_ref(v___y_1378_);
lean_dec_ref(v___y_1376_);
return v___x_1407_;
}
}
}
}
v___jp_1430_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = lean_unsigned_to_nat(1u);
v___x_1432_ = lean_nat_add(v_currRecDepth_1422_, v___x_1431_);
lean_inc(v_ref_1423_);
lean_inc_ref(v_toCold_1421_);
v___x_1433_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1433_, 0, v_toCold_1421_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
lean_ctor_set(v___x_1433_, 2, v_ref_1423_);
lean_ctor_set_uint16(v___x_1433_, sizeof(void*)*3, v_optionFlags_1424_);
lean_ctor_set_uint8(v___x_1433_, sizeof(void*)*3 + 2, v_suppressElabErrors_1425_);
lean_ctor_set_uint8(v___x_1433_, sizeof(void*)*3 + 3, v_isRecordingDeps_1426_);
if (v___x_1429_ == 0)
{
lean_dec_ref(v___x_1428_);
lean_dec_ref(v_rhs_1337_);
v___y_1350_ = v_a_1338_;
v___y_1351_ = v_a_1339_;
v___y_1352_ = v_a_1340_;
v___y_1353_ = v_a_1341_;
v___y_1354_ = v_a_1342_;
v___y_1355_ = v_a_1343_;
v___y_1356_ = v_a_1344_;
v___y_1357_ = v_a_1345_;
v___y_1358_ = v___x_1433_;
v___y_1359_ = v_a_1347_;
goto v___jp_1349_;
}
else
{
lean_object* v_arg_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v_arg_1434_ = lean_ctor_get(v___x_1428_, 1);
lean_inc_ref(v_arg_1434_);
v___x_1435_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1428_);
v___x_1436_ = l_Lean_Expr_isApp(v___x_1435_);
if (v___x_1436_ == 0)
{
lean_dec_ref(v___x_1435_);
lean_dec_ref(v_arg_1434_);
lean_dec_ref(v_rhs_1337_);
v___y_1350_ = v_a_1338_;
v___y_1351_ = v_a_1339_;
v___y_1352_ = v_a_1340_;
v___y_1353_ = v_a_1341_;
v___y_1354_ = v_a_1342_;
v___y_1355_ = v_a_1343_;
v___y_1356_ = v_a_1344_;
v___y_1357_ = v_a_1345_;
v___y_1358_ = v___x_1433_;
v___y_1359_ = v_a_1347_;
goto v___jp_1349_;
}
else
{
lean_object* v_arg_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v_arg_1437_ = lean_ctor_get(v___x_1435_, 1);
lean_inc_ref(v_arg_1437_);
v___x_1438_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1435_);
v___x_1439_ = l_Lean_Expr_isApp(v___x_1438_);
if (v___x_1439_ == 0)
{
lean_dec_ref(v___x_1438_);
lean_dec_ref(v_arg_1437_);
lean_dec_ref(v_arg_1434_);
lean_dec_ref(v_rhs_1337_);
v___y_1350_ = v_a_1338_;
v___y_1351_ = v_a_1339_;
v___y_1352_ = v_a_1340_;
v___y_1353_ = v_a_1341_;
v___y_1354_ = v_a_1342_;
v___y_1355_ = v_a_1343_;
v___y_1356_ = v_a_1344_;
v___y_1357_ = v_a_1345_;
v___y_1358_ = v___x_1433_;
v___y_1359_ = v_a_1347_;
goto v___jp_1349_;
}
else
{
lean_object* v_arg_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; 
v_arg_1440_ = lean_ctor_get(v___x_1438_, 1);
lean_inc_ref(v_arg_1440_);
v___x_1441_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1438_);
v___x_1442_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_1443_ = l_Lean_Expr_isConstOf(v___x_1441_, v___x_1442_);
if (v___x_1443_ == 0)
{
lean_dec_ref(v___x_1441_);
lean_dec_ref(v_arg_1440_);
lean_dec_ref(v_arg_1437_);
lean_dec_ref(v_arg_1434_);
lean_dec_ref(v_rhs_1337_);
v___y_1350_ = v_a_1338_;
v___y_1351_ = v_a_1339_;
v___y_1352_ = v_a_1340_;
v___y_1353_ = v_a_1341_;
v___y_1354_ = v_a_1342_;
v___y_1355_ = v_a_1343_;
v___y_1356_ = v_a_1344_;
v___y_1357_ = v_a_1345_;
v___y_1358_ = v___x_1433_;
v___y_1359_ = v_a_1347_;
goto v___jp_1349_;
}
else
{
lean_object* v___x_1444_; uint8_t v___x_1445_; 
v___x_1444_ = l_Lean_Expr_cleanupAnnotations(v_rhs_1337_);
v___x_1445_ = l_Lean_Expr_isApp(v___x_1444_);
if (v___x_1445_ == 0)
{
lean_dec_ref(v___x_1444_);
lean_dec_ref(v___x_1441_);
lean_dec_ref(v_arg_1440_);
lean_dec_ref(v_arg_1437_);
lean_dec_ref(v_arg_1434_);
v___y_1363_ = v_a_1338_;
v___y_1364_ = v_a_1339_;
v___y_1365_ = v_a_1340_;
v___y_1366_ = v_a_1341_;
v___y_1367_ = v_a_1342_;
v___y_1368_ = v_a_1343_;
v___y_1369_ = v_a_1344_;
v___y_1370_ = v_a_1345_;
v___y_1371_ = v___x_1433_;
v___y_1372_ = v_a_1347_;
goto v___jp_1362_;
}
else
{
lean_object* v_arg_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v_arg_1446_ = lean_ctor_get(v___x_1444_, 1);
lean_inc_ref(v_arg_1446_);
v___x_1447_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1444_);
v___x_1448_ = l_Lean_Expr_isApp(v___x_1447_);
if (v___x_1448_ == 0)
{
lean_dec_ref(v___x_1447_);
lean_dec_ref(v_arg_1446_);
lean_dec_ref(v___x_1441_);
lean_dec_ref(v_arg_1440_);
lean_dec_ref(v_arg_1437_);
lean_dec_ref(v_arg_1434_);
v___y_1363_ = v_a_1338_;
v___y_1364_ = v_a_1339_;
v___y_1365_ = v_a_1340_;
v___y_1366_ = v_a_1341_;
v___y_1367_ = v_a_1342_;
v___y_1368_ = v_a_1343_;
v___y_1369_ = v_a_1344_;
v___y_1370_ = v_a_1345_;
v___y_1371_ = v___x_1433_;
v___y_1372_ = v_a_1347_;
goto v___jp_1362_;
}
else
{
lean_object* v_arg_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v_arg_1449_ = lean_ctor_get(v___x_1447_, 1);
lean_inc_ref(v_arg_1449_);
v___x_1450_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1447_);
v___x_1451_ = l_Lean_Expr_isApp(v___x_1450_);
if (v___x_1451_ == 0)
{
lean_dec_ref(v___x_1450_);
lean_dec_ref(v_arg_1449_);
lean_dec_ref(v_arg_1446_);
lean_dec_ref(v___x_1441_);
lean_dec_ref(v_arg_1440_);
lean_dec_ref(v_arg_1437_);
lean_dec_ref(v_arg_1434_);
v___y_1363_ = v_a_1338_;
v___y_1364_ = v_a_1339_;
v___y_1365_ = v_a_1340_;
v___y_1366_ = v_a_1341_;
v___y_1367_ = v_a_1342_;
v___y_1368_ = v_a_1343_;
v___y_1369_ = v_a_1344_;
v___y_1370_ = v_a_1345_;
v___y_1371_ = v___x_1433_;
v___y_1372_ = v_a_1347_;
goto v___jp_1362_;
}
else
{
lean_object* v_arg_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v_arg_1452_ = lean_ctor_get(v___x_1450_, 1);
lean_inc_ref(v_arg_1452_);
v___x_1453_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1450_);
v___x_1454_ = l_Lean_Expr_isConstOf(v___x_1453_, v___x_1442_);
lean_dec_ref(v___x_1453_);
if (v___x_1454_ == 0)
{
lean_dec_ref(v_arg_1452_);
lean_dec_ref(v_arg_1449_);
lean_dec_ref(v_arg_1446_);
lean_dec_ref(v___x_1441_);
lean_dec_ref(v_arg_1440_);
lean_dec_ref(v_arg_1437_);
lean_dec_ref(v_arg_1434_);
v___y_1363_ = v_a_1338_;
v___y_1364_ = v_a_1339_;
v___y_1365_ = v_a_1340_;
v___y_1366_ = v_a_1341_;
v___y_1367_ = v_a_1342_;
v___y_1368_ = v_a_1343_;
v___y_1369_ = v_a_1344_;
v___y_1370_ = v_a_1345_;
v___y_1371_ = v___x_1433_;
v___y_1372_ = v_a_1347_;
goto v___jp_1362_;
}
else
{
lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1455_ = lean_st_ref_get(v_a_1338_);
v___x_1456_ = lean_st_ref_get(v_a_1338_);
v___x_1457_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1455_, v_arg_1437_, v_arg_1446_);
lean_dec(v___x_1455_);
if (v___x_1457_ == 0)
{
lean_dec(v___x_1456_);
v___y_1376_ = v_arg_1446_;
v___y_1377_ = v___x_1441_;
v___y_1378_ = v_arg_1449_;
v___y_1379_ = v_arg_1452_;
v___y_1380_ = v_arg_1440_;
v___y_1381_ = v_arg_1437_;
v___y_1382_ = v_arg_1434_;
v___y_1383_ = v___x_1433_;
v___y_1384_ = v___x_1454_;
v___y_1385_ = v___x_1457_;
goto v___jp_1375_;
}
else
{
uint8_t v___x_1458_; 
v___x_1458_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1456_, v_arg_1434_, v_arg_1449_);
lean_dec(v___x_1456_);
v___y_1376_ = v_arg_1446_;
v___y_1377_ = v___x_1441_;
v___y_1378_ = v_arg_1449_;
v___y_1379_ = v_arg_1452_;
v___y_1380_ = v_arg_1440_;
v___y_1381_ = v_arg_1437_;
v___y_1382_ = v_arg_1434_;
v___y_1383_ = v___x_1433_;
v___y_1384_ = v___x_1454_;
v___y_1385_ = v___x_1458_;
goto v___jp_1375_;
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
LEAN_EXPORT void l_Lean_Meta_Grind_mkEqCongrSymmProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_1336_ = stack[0].m_obj;
lean_object* v_rhs_1337_ = stack[1].m_obj;
lean_object* v_a_1338_ = stack[2].m_obj;
lean_object* v_a_1339_ = stack[3].m_obj;
lean_object* v_a_1340_ = stack[4].m_obj;
lean_object* v_a_1341_ = stack[5].m_obj;
lean_object* v_a_1342_ = stack[6].m_obj;
lean_object* v_a_1343_ = stack[7].m_obj;
lean_object* v_a_1344_ = stack[8].m_obj;
lean_object* v_a_1345_ = stack[9].m_obj;
lean_object* v_a_1346_ = stack[10].m_obj;
lean_object* v_a_1347_ = stack[11].m_obj;
lean_object* v_res_1463_;
v_res_1463_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(v_lhs_1336_, v_rhs_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
stack->m_obj
 = v_res_1463_;
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1468_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1469_ = lean_unsigned_to_nat(38u);
v___x_1470_ = lean_unsigned_to_nat(250u);
v___x_1471_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2));
v___x_1472_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1473_ = l_mkPanicMessageWithDecl(v___x_1472_, v___x_1471_, v___x_1470_, v___x_1469_, v___x_1468_);
return v___x_1473_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5(void){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1475_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4));
v___x_1476_ = lean_unsigned_to_nat(6u);
v___x_1477_ = lean_unsigned_to_nat(260u);
v___x_1478_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2));
v___x_1479_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1480_ = l_mkPanicMessageWithDecl(v___x_1479_, v___x_1478_, v___x_1477_, v___x_1476_, v___x_1475_);
return v___x_1480_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1483_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__1));
v___x_1484_ = lean_unsigned_to_nat(4u);
v___x_1485_ = lean_unsigned_to_nat(219u);
v___x_1486_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__0));
v___x_1487_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1488_ = l_mkPanicMessageWithDecl(v___x_1487_, v___x_1486_, v___x_1485_, v___x_1484_, v___x_1483_);
return v___x_1488_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(lean_object* v_lhs_1489_, lean_object* v_rhs_1490_, uint8_t v_heq_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v_numArgs_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; 
v_numArgs_1503_ = l_Lean_Expr_getAppNumArgs(v_lhs_1489_);
v___x_1504_ = l_Lean_Expr_getAppNumArgs(v_rhs_1490_);
v___x_1505_ = lean_nat_dec_eq(v___x_1504_, v_numArgs_1503_);
lean_dec(v___x_1504_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec(v_numArgs_1503_);
lean_dec_ref(v_rhs_1490_);
lean_dec_ref(v_lhs_1489_);
v___x_1506_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2);
v___x_1507_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1506_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
return v___x_1507_;
}
else
{
lean_object* v_f_1508_; lean_object* v_g_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v_f_1508_ = l_Lean_Expr_getAppFn(v_lhs_1489_);
v_g_1509_ = l_Lean_Expr_getAppFn(v_rhs_1490_);
v___x_1510_ = lean_box(0);
lean_inc_ref(v_f_1508_);
v___x_1511_ = l_Lean_Meta_getFunInfo(v_f_1508_, v___x_1510_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1511_, 1);
v___x_1513_ = l_Lean_Meta_FunInfo_getArity(v_a_1512_);
lean_dec(v_a_1512_);
v___x_1514_ = lean_nat_dec_lt(v___x_1513_, v_numArgs_1503_);
lean_dec(v___x_1513_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; 
v___x_1515_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_1508_, v_g_1509_, v_numArgs_1503_, v_lhs_1489_, v_rhs_1490_, v_heq_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
return v___x_1515_;
}
else
{
lean_object* v___x_1516_; 
lean_dec_ref(v_g_1509_);
lean_dec_ref(v_f_1508_);
lean_dec(v_numArgs_1503_);
lean_inc_ref(v_lhs_1489_);
v___x_1516_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(v_lhs_1489_, v_rhs_1490_);
if (lean_obj_tag(v___x_1516_) == 1)
{
lean_object* v_val_1517_; lean_object* v_fst_1518_; lean_object* v_snd_1519_; lean_object* v___y_1521_; lean_object* v___x_1534_; 
v_val_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_val_1517_);
lean_dec_ref_known(v___x_1516_, 1);
v_fst_1518_ = lean_ctor_get(v_val_1517_, 0);
lean_inc(v_fst_1518_);
v_snd_1519_ = lean_ctor_get(v_val_1517_, 1);
lean_inc_n(v_snd_1519_, 2);
lean_dec(v_val_1517_);
v___x_1534_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(v_fst_1518_, v_snd_1519_, v_a_1495_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
if (lean_obj_tag(v___x_1534_) == 0)
{
v___y_1521_ = v___x_1534_;
goto v___jp_1520_;
}
else
{
lean_object* v_a_1535_; uint8_t v___y_1537_; uint8_t v___x_1539_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
v___x_1539_ = l_Lean_Exception_isInterrupt(v_a_1535_);
if (v___x_1539_ == 0)
{
uint8_t v___x_1540_; 
lean_inc(v_a_1535_);
v___x_1540_ = l_Lean_Exception_isRuntime(v_a_1535_);
v___y_1537_ = v___x_1540_;
goto v___jp_1536_;
}
else
{
v___y_1537_ = v___x_1539_;
goto v___jp_1536_;
}
v___jp_1536_:
{
if (v___y_1537_ == 0)
{
lean_object* v___x_1538_; 
lean_dec_ref_known(v___x_1534_, 1);
lean_inc_ref(v_rhs_1490_);
lean_inc_ref(v_lhs_1489_);
v___x_1538_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1489_, v_rhs_1490_, lean_box(0), v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
v___y_1521_ = v___x_1538_;
goto v___jp_1520_;
}
else
{
v___y_1521_ = v___x_1534_;
goto v___jp_1520_;
}
}
}
v___jp_1520_:
{
if (lean_obj_tag(v___y_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1523_; 
v_a_1522_ = lean_ctor_get(v___y_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___y_1521_, 1);
v___x_1523_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_1522_, v_lhs_1489_, v_rhs_1490_, v_snd_1519_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
lean_dec(v_snd_1519_);
lean_dec_ref(v_rhs_1490_);
lean_dec_ref(v_lhs_1489_);
lean_dec(v_a_1522_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1525_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1523_, 1);
v___x_1525_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_1524_, v_heq_1491_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
return v___x_1525_;
}
else
{
return v___x_1523_;
}
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
lean_dec(v_snd_1519_);
lean_dec_ref(v_rhs_1490_);
lean_dec_ref(v_lhs_1489_);
v_a_1526_ = lean_ctor_get(v___y_1521_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___y_1521_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___y_1521_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___y_1521_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
}
else
{
lean_object* v___x_1541_; 
lean_dec(v___x_1516_);
v___x_1541_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1489_, v_rhs_1490_, lean_box(0), v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
return v___x_1541_;
}
}
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
lean_dec_ref(v_g_1509_);
lean_dec_ref(v_f_1508_);
lean_dec(v_numArgs_1503_);
lean_dec_ref(v_rhs_1490_);
lean_dec_ref(v_lhs_1489_);
v_a_1542_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1511_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1511_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_1489_ = stack[0].m_obj;
lean_object* v_rhs_1490_ = stack[1].m_obj;
uint8_t v_heq_1491_ = stack[2].m_num;
lean_object* v_a_1492_ = stack[3].m_obj;
lean_object* v_a_1493_ = stack[4].m_obj;
lean_object* v_a_1494_ = stack[5].m_obj;
lean_object* v_a_1495_ = stack[6].m_obj;
lean_object* v_a_1496_ = stack[7].m_obj;
lean_object* v_a_1497_ = stack[8].m_obj;
lean_object* v_a_1498_ = stack[9].m_obj;
lean_object* v_a_1499_ = stack[10].m_obj;
lean_object* v_a_1500_ = stack[11].m_obj;
lean_object* v_a_1501_ = stack[12].m_obj;
lean_object* v_res_1550_;
v_res_1550_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_1489_, v_rhs_1490_, v_heq_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
stack->m_obj
 = v_res_1550_;
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(lean_object* v_lhs_1551_, lean_object* v_rhs_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_){
_start:
{
uint8_t v___x_1564_; 
v___x_1564_ = l_Lean_Expr_isApp(v_lhs_1551_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_box(0);
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
return v___x_1566_;
}
else
{
lean_object* v_a_u2081_1567_; lean_object* v_a_u2082_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_a_u2081_1567_ = l_Lean_Expr_appArg_x21(v_lhs_1551_);
v_a_u2082_1568_ = l_Lean_Expr_appArg_x21(v_rhs_1552_);
v___x_1569_ = l_Lean_Expr_appFn_x21(v_lhs_1551_);
v___x_1570_ = l_Lean_Expr_appFn_x21(v_rhs_1552_);
v___x_1571_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v___x_1569_, v___x_1570_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
lean_dec_ref(v___x_1570_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1669_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1574_ = v___x_1571_;
v_isShared_1575_ = v_isSharedCheck_1669_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1571_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1669_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
if (lean_obj_tag(v_a_1572_) == 1)
{
lean_object* v_val_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1633_; 
lean_del_object(v___x_1574_);
lean_dec_ref(v___x_1569_);
v_val_1576_ = lean_ctor_get(v_a_1572_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_a_1572_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1578_ = v_a_1572_;
v_isShared_1579_ = v_isSharedCheck_1633_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_val_1576_);
lean_dec(v_a_1572_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1633_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
size_t v___x_1580_; size_t v___x_1581_; uint8_t v___x_1582_; 
v___x_1580_ = lean_ptr_addr(v_a_u2081_1567_);
v___x_1581_ = lean_ptr_addr(v_a_u2082_1568_);
v___x_1582_ = lean_usize_dec_eq(v___x_1580_, v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; 
v___x_1583_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_1567_, v_a_u2082_1568_, v___x_1582_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1585_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 1);
v___x_1585_ = l_Lean_Meta_mkCongr(v_val_1576_, v_a_1584_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1596_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1588_ = v___x_1585_;
v_isShared_1589_ = v_isSharedCheck_1596_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1596_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v_a_1586_);
v___x_1591_ = v___x_1578_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1593_; 
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 0, v___x_1591_);
v___x_1593_ = v___x_1588_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_del_object(v___x_1578_);
v_a_1597_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1585_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1585_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_del_object(v___x_1578_);
lean_dec(v_val_1576_);
v_a_1605_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1583_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1583_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
else
{
lean_object* v___x_1613_; 
lean_dec_ref(v_a_u2082_1568_);
v___x_1613_ = l_Lean_Meta_mkCongrFun(v_val_1576_, v_a_u2081_1567_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1624_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1624_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1624_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v_a_1614_);
v___x_1619_ = v___x_1578_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1621_; 
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v___x_1619_);
v___x_1621_ = v___x_1616_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_del_object(v___x_1578_);
v_a_1625_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1613_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1613_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
}
}
else
{
size_t v___x_1634_; size_t v___x_1635_; uint8_t v___x_1636_; 
lean_dec(v_a_1572_);
v___x_1634_ = lean_ptr_addr(v_a_u2081_1567_);
v___x_1635_ = lean_ptr_addr(v_a_u2082_1568_);
v___x_1636_ = lean_usize_dec_eq(v___x_1634_, v___x_1635_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; 
lean_del_object(v___x_1574_);
v___x_1637_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_1567_, v_a_u2082_1568_, v___x_1636_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1639_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1637_, 1);
v___x_1639_ = l_Lean_Meta_mkCongrArg(v___x_1569_, v_a_1638_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1648_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1648_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1648_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1644_, 0, v_a_1640_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1644_);
v___x_1646_ = v___x_1642_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
v_a_1649_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1639_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1639_);
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
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec_ref(v___x_1569_);
v_a_1657_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1637_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1637_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_object* v___x_1665_; lean_object* v___x_1667_; 
lean_dec_ref(v___x_1569_);
lean_dec_ref(v_a_u2082_1568_);
lean_dec_ref(v_a_u2081_1567_);
v___x_1665_ = lean_box(0);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v___x_1665_);
v___x_1667_ = v___x_1574_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1665_);
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
}
else
{
lean_dec_ref(v___x_1569_);
lean_dec_ref(v_a_u2082_1568_);
lean_dec_ref(v_a_u2081_1567_);
return v___x_1571_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_1551_ = stack[0].m_obj;
lean_object* v_rhs_1552_ = stack[1].m_obj;
lean_object* v_a_1553_ = stack[2].m_obj;
lean_object* v_a_1554_ = stack[3].m_obj;
lean_object* v_a_1555_ = stack[4].m_obj;
lean_object* v_a_1556_ = stack[5].m_obj;
lean_object* v_a_1557_ = stack[6].m_obj;
lean_object* v_a_1558_ = stack[7].m_obj;
lean_object* v_a_1559_ = stack[8].m_obj;
lean_object* v_a_1560_ = stack[9].m_obj;
lean_object* v_a_1561_ = stack[10].m_obj;
lean_object* v_a_1562_ = stack[11].m_obj;
lean_object* v_res_1670_;
v_res_1670_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_1551_, v_rhs_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
stack->m_obj
 = v_res_1670_;
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1674_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__2));
v___x_1675_ = lean_unsigned_to_nat(14u);
v___x_1676_ = lean_unsigned_to_nat(22u);
v___x_1677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__1));
v___x_1678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__0));
v___x_1679_ = l_mkPanicMessageWithDecl(v___x_1678_, v___x_1677_, v___x_1676_, v___x_1675_, v___x_1674_);
return v___x_1679_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(lean_object* v_lhs_1680_, lean_object* v_rhs_1681_, uint8_t v_heq_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_1680_, v_rhs_1681_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1708_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1697_ = v___x_1694_;
v_isShared_1698_ = v_isSharedCheck_1708_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1694_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1708_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___y_1700_; 
if (lean_obj_tag(v_a_1695_) == 0)
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3);
v___x_1706_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_spec__13(v___x_1705_);
v___y_1700_ = v___x_1706_;
goto v___jp_1699_;
}
else
{
lean_object* v_val_1707_; 
v_val_1707_ = lean_ctor_get(v_a_1695_, 0);
lean_inc(v_val_1707_);
lean_dec_ref_known(v_a_1695_, 1);
v___y_1700_ = v_val_1707_;
goto v___jp_1699_;
}
v___jp_1699_:
{
if (v_heq_1682_ == 0)
{
lean_object* v___x_1702_; 
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 0, v___y_1700_);
v___x_1702_ = v___x_1697_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___y_1700_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
else
{
lean_object* v___x_1704_; 
lean_del_object(v___x_1697_);
v___x_1704_ = l_Lean_Meta_mkHEqOfEq(v___y_1700_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
return v___x_1704_;
}
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
v_a_1709_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1694_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1694_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_1680_ = stack[0].m_obj;
lean_object* v_rhs_1681_ = stack[1].m_obj;
uint8_t v_heq_1682_ = stack[2].m_num;
lean_object* v_a_1683_ = stack[3].m_obj;
lean_object* v_a_1684_ = stack[4].m_obj;
lean_object* v_a_1685_ = stack[5].m_obj;
lean_object* v_a_1686_ = stack[6].m_obj;
lean_object* v_a_1687_ = stack[7].m_obj;
lean_object* v_a_1688_ = stack[8].m_obj;
lean_object* v_a_1689_ = stack[9].m_obj;
lean_object* v_a_1690_ = stack[10].m_obj;
lean_object* v_a_1691_ = stack[11].m_obj;
lean_object* v_a_1692_ = stack[12].m_obj;
lean_object* v_res_1717_;
v_res_1717_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_1680_, v_rhs_1681_, v_heq_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
stack->m_obj
 = v_res_1717_;
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__1(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1719_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1720_ = lean_unsigned_to_nat(36u);
v___x_1721_ = lean_unsigned_to_nat(143u);
v___x_1722_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1723_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1724_ = l_mkPanicMessageWithDecl(v___x_1723_, v___x_1722_, v___x_1721_, v___x_1720_, v___x_1719_);
return v___x_1724_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__2(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1725_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1726_ = lean_unsigned_to_nat(34u);
v___x_1727_ = lean_unsigned_to_nat(144u);
v___x_1728_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1729_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1730_ = l_mkPanicMessageWithDecl(v___x_1729_, v___x_1728_, v___x_1727_, v___x_1726_, v___x_1725_);
return v___x_1730_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__4(void){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1732_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__3));
v___x_1733_ = lean_unsigned_to_nat(4u);
v___x_1734_ = lean_unsigned_to_nat(145u);
v___x_1735_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1736_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1737_ = l_mkPanicMessageWithDecl(v___x_1736_, v___x_1735_, v___x_1734_, v___x_1733_, v___x_1732_);
return v___x_1737_;
}
}
lean_object* l_Lean_Meta_Grind_mkEqCongrProof(lean_object* v_lhs_1748_, lean_object* v_rhs_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; uint8_t v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; uint8_t v___y_1797_; lean_object* v_toCold_1833_; lean_object* v_currRecDepth_1834_; lean_object* v_ref_1835_; uint16_t v_optionFlags_1836_; uint8_t v_suppressElabErrors_1837_; uint8_t v_isRecordingDeps_1838_; lean_object* v_maxRecDepth_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; lean_object* v___x_1871_; uint8_t v___x_1872_; 
v_toCold_1833_ = lean_ctor_get(v_a_1758_, 0);
v_currRecDepth_1834_ = lean_ctor_get(v_a_1758_, 1);
v_ref_1835_ = lean_ctor_get(v_a_1758_, 2);
v_optionFlags_1836_ = lean_ctor_get_uint16(v_a_1758_, sizeof(void*)*3);
v_suppressElabErrors_1837_ = lean_ctor_get_uint8(v_a_1758_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1838_ = lean_ctor_get_uint8(v_a_1758_, sizeof(void*)*3 + 3);
v_maxRecDepth_1839_ = lean_ctor_get(v_toCold_1833_, 3);
v___x_1840_ = l_Lean_Expr_cleanupAnnotations(v_lhs_1748_);
v___x_1841_ = l_Lean_Expr_isApp(v___x_1840_);
v___x_1871_ = lean_unsigned_to_nat(0u);
v___x_1872_ = lean_nat_dec_eq(v_maxRecDepth_1839_, v___x_1871_);
if (v___x_1872_ == 0)
{
uint8_t v___x_1873_; 
v___x_1873_ = lean_nat_dec_eq(v_currRecDepth_1834_, v_maxRecDepth_1839_);
if (v___x_1873_ == 0)
{
goto v___jp_1842_;
}
else
{
lean_object* v___x_1874_; 
lean_dec_ref(v___x_1840_);
lean_dec_ref(v_rhs_1749_);
lean_inc(v_ref_1835_);
v___x_1874_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1835_);
return v___x_1874_;
}
}
else
{
goto v___jp_1842_;
}
v___jp_1761_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__1, &l_Lean_Meta_Grind_mkEqCongrProof___closed__1_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__1);
v___x_1773_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1772_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec_ref(v___y_1770_);
return v___x_1773_;
}
v___jp_1774_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__2, &l_Lean_Meta_Grind_mkEqCongrProof___closed__2_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__2);
v___x_1786_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1785_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec_ref(v___y_1783_);
return v___x_1786_;
}
v___jp_1787_:
{
if (v___y_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
lean_dec_ref(v___y_1796_);
lean_dec_ref(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v___y_1789_);
v___x_1798_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__4, &l_Lean_Meta_Grind_mkEqCongrProof___closed__4_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__4);
v___x_1799_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1798_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v___y_1795_, v_a_1759_);
lean_dec_ref(v___y_1795_);
return v___x_1799_;
}
else
{
lean_object* v___x_1800_; size_t v___x_1801_; size_t v___x_1802_; uint8_t v___x_1803_; 
v___x_1800_ = l_Lean_Expr_constLevels_x21(v___y_1792_);
lean_dec_ref(v___y_1792_);
v___x_1801_ = lean_ptr_addr(v___y_1791_);
v___x_1802_ = lean_ptr_addr(v___y_1790_);
v___x_1803_ = lean_usize_dec_eq(v___x_1801_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; 
lean_inc_ref(v___y_1796_);
lean_inc_ref(v___y_1789_);
v___x_1804_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1789_, v___y_1796_, v___y_1788_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v___y_1795_, v_a_1759_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1806_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_a_1805_);
lean_dec_ref_known(v___x_1804_, 1);
lean_inc_ref(v___y_1794_);
lean_inc_ref(v___y_1793_);
v___x_1806_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1793_, v___y_1794_, v___y_1788_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v___y_1795_, v_a_1759_);
lean_dec_ref(v___y_1795_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1817_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1817_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1817_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1811_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__6));
v___x_1812_ = l_Lean_mkConst(v___x_1811_, v___x_1800_);
v___x_1813_ = l_Lean_mkApp8(v___x_1812_, v___y_1791_, v___y_1790_, v___y_1789_, v___y_1793_, v___y_1796_, v___y_1794_, v_a_1805_, v_a_1807_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1813_);
v___x_1815_ = v___x_1809_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
else
{
lean_dec(v_a_1805_);
lean_dec(v___x_1800_);
lean_dec_ref(v___y_1796_);
lean_dec_ref(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec_ref(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v___y_1789_);
return v___x_1806_;
}
}
else
{
lean_dec(v___x_1800_);
lean_dec_ref(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec_ref(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v___y_1789_);
return v___x_1804_;
}
}
else
{
uint8_t v___x_1818_; lean_object* v___x_1819_; 
lean_dec_ref(v___y_1790_);
v___x_1818_ = 0;
lean_inc_ref(v___y_1796_);
lean_inc_ref(v___y_1789_);
v___x_1819_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1789_, v___y_1796_, v___x_1818_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v___y_1795_, v_a_1759_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1821_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref_known(v___x_1819_, 1);
lean_inc_ref(v___y_1794_);
lean_inc_ref(v___y_1793_);
v___x_1821_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1793_, v___y_1794_, v___x_1818_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v___y_1795_, v_a_1759_);
lean_dec_ref(v___y_1795_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1832_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1832_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1832_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1826_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__8));
v___x_1827_ = l_Lean_mkConst(v___x_1826_, v___x_1800_);
v___x_1828_ = l_Lean_mkApp7(v___x_1827_, v___y_1791_, v___y_1789_, v___y_1793_, v___y_1796_, v___y_1794_, v_a_1820_, v_a_1822_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1828_);
v___x_1830_ = v___x_1824_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
else
{
lean_dec(v_a_1820_);
lean_dec(v___x_1800_);
lean_dec_ref(v___y_1796_);
lean_dec_ref(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec_ref(v___y_1791_);
lean_dec_ref(v___y_1789_);
return v___x_1821_;
}
}
else
{
lean_dec(v___x_1800_);
lean_dec_ref(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec_ref(v___y_1791_);
lean_dec_ref(v___y_1789_);
return v___x_1819_;
}
}
}
}
v___jp_1842_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = lean_unsigned_to_nat(1u);
v___x_1844_ = lean_nat_add(v_currRecDepth_1834_, v___x_1843_);
lean_inc(v_ref_1835_);
lean_inc_ref(v_toCold_1833_);
v___x_1845_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1845_, 0, v_toCold_1833_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
lean_ctor_set(v___x_1845_, 2, v_ref_1835_);
lean_ctor_set_uint16(v___x_1845_, sizeof(void*)*3, v_optionFlags_1836_);
lean_ctor_set_uint8(v___x_1845_, sizeof(void*)*3 + 2, v_suppressElabErrors_1837_);
lean_ctor_set_uint8(v___x_1845_, sizeof(void*)*3 + 3, v_isRecordingDeps_1838_);
if (v___x_1841_ == 0)
{
lean_dec_ref(v___x_1840_);
lean_dec_ref(v_rhs_1749_);
v___y_1762_ = v_a_1750_;
v___y_1763_ = v_a_1751_;
v___y_1764_ = v_a_1752_;
v___y_1765_ = v_a_1753_;
v___y_1766_ = v_a_1754_;
v___y_1767_ = v_a_1755_;
v___y_1768_ = v_a_1756_;
v___y_1769_ = v_a_1757_;
v___y_1770_ = v___x_1845_;
v___y_1771_ = v_a_1759_;
goto v___jp_1761_;
}
else
{
lean_object* v_arg_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
v_arg_1846_ = lean_ctor_get(v___x_1840_, 1);
lean_inc_ref(v_arg_1846_);
v___x_1847_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1840_);
v___x_1848_ = l_Lean_Expr_isApp(v___x_1847_);
if (v___x_1848_ == 0)
{
lean_dec_ref(v___x_1847_);
lean_dec_ref(v_arg_1846_);
lean_dec_ref(v_rhs_1749_);
v___y_1762_ = v_a_1750_;
v___y_1763_ = v_a_1751_;
v___y_1764_ = v_a_1752_;
v___y_1765_ = v_a_1753_;
v___y_1766_ = v_a_1754_;
v___y_1767_ = v_a_1755_;
v___y_1768_ = v_a_1756_;
v___y_1769_ = v_a_1757_;
v___y_1770_ = v___x_1845_;
v___y_1771_ = v_a_1759_;
goto v___jp_1761_;
}
else
{
lean_object* v_arg_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v_arg_1849_ = lean_ctor_get(v___x_1847_, 1);
lean_inc_ref(v_arg_1849_);
v___x_1850_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1847_);
v___x_1851_ = l_Lean_Expr_isApp(v___x_1850_);
if (v___x_1851_ == 0)
{
lean_dec_ref(v___x_1850_);
lean_dec_ref(v_arg_1849_);
lean_dec_ref(v_arg_1846_);
lean_dec_ref(v_rhs_1749_);
v___y_1762_ = v_a_1750_;
v___y_1763_ = v_a_1751_;
v___y_1764_ = v_a_1752_;
v___y_1765_ = v_a_1753_;
v___y_1766_ = v_a_1754_;
v___y_1767_ = v_a_1755_;
v___y_1768_ = v_a_1756_;
v___y_1769_ = v_a_1757_;
v___y_1770_ = v___x_1845_;
v___y_1771_ = v_a_1759_;
goto v___jp_1761_;
}
else
{
lean_object* v_arg_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; 
v_arg_1852_ = lean_ctor_get(v___x_1850_, 1);
lean_inc_ref(v_arg_1852_);
v___x_1853_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1850_);
v___x_1854_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_1855_ = l_Lean_Expr_isConstOf(v___x_1853_, v___x_1854_);
if (v___x_1855_ == 0)
{
lean_dec_ref(v___x_1853_);
lean_dec_ref(v_arg_1852_);
lean_dec_ref(v_arg_1849_);
lean_dec_ref(v_arg_1846_);
lean_dec_ref(v_rhs_1749_);
v___y_1762_ = v_a_1750_;
v___y_1763_ = v_a_1751_;
v___y_1764_ = v_a_1752_;
v___y_1765_ = v_a_1753_;
v___y_1766_ = v_a_1754_;
v___y_1767_ = v_a_1755_;
v___y_1768_ = v_a_1756_;
v___y_1769_ = v_a_1757_;
v___y_1770_ = v___x_1845_;
v___y_1771_ = v_a_1759_;
goto v___jp_1761_;
}
else
{
lean_object* v___x_1856_; uint8_t v___x_1857_; 
v___x_1856_ = l_Lean_Expr_cleanupAnnotations(v_rhs_1749_);
v___x_1857_ = l_Lean_Expr_isApp(v___x_1856_);
if (v___x_1857_ == 0)
{
lean_dec_ref(v___x_1856_);
lean_dec_ref(v___x_1853_);
lean_dec_ref(v_arg_1852_);
lean_dec_ref(v_arg_1849_);
lean_dec_ref(v_arg_1846_);
v___y_1775_ = v_a_1750_;
v___y_1776_ = v_a_1751_;
v___y_1777_ = v_a_1752_;
v___y_1778_ = v_a_1753_;
v___y_1779_ = v_a_1754_;
v___y_1780_ = v_a_1755_;
v___y_1781_ = v_a_1756_;
v___y_1782_ = v_a_1757_;
v___y_1783_ = v___x_1845_;
v___y_1784_ = v_a_1759_;
goto v___jp_1774_;
}
else
{
lean_object* v_arg_1858_; lean_object* v___x_1859_; uint8_t v___x_1860_; 
v_arg_1858_ = lean_ctor_get(v___x_1856_, 1);
lean_inc_ref(v_arg_1858_);
v___x_1859_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1856_);
v___x_1860_ = l_Lean_Expr_isApp(v___x_1859_);
if (v___x_1860_ == 0)
{
lean_dec_ref(v___x_1859_);
lean_dec_ref(v_arg_1858_);
lean_dec_ref(v___x_1853_);
lean_dec_ref(v_arg_1852_);
lean_dec_ref(v_arg_1849_);
lean_dec_ref(v_arg_1846_);
v___y_1775_ = v_a_1750_;
v___y_1776_ = v_a_1751_;
v___y_1777_ = v_a_1752_;
v___y_1778_ = v_a_1753_;
v___y_1779_ = v_a_1754_;
v___y_1780_ = v_a_1755_;
v___y_1781_ = v_a_1756_;
v___y_1782_ = v_a_1757_;
v___y_1783_ = v___x_1845_;
v___y_1784_ = v_a_1759_;
goto v___jp_1774_;
}
else
{
lean_object* v_arg_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v_arg_1861_ = lean_ctor_get(v___x_1859_, 1);
lean_inc_ref(v_arg_1861_);
v___x_1862_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1859_);
v___x_1863_ = l_Lean_Expr_isApp(v___x_1862_);
if (v___x_1863_ == 0)
{
lean_dec_ref(v___x_1862_);
lean_dec_ref(v_arg_1861_);
lean_dec_ref(v_arg_1858_);
lean_dec_ref(v___x_1853_);
lean_dec_ref(v_arg_1852_);
lean_dec_ref(v_arg_1849_);
lean_dec_ref(v_arg_1846_);
v___y_1775_ = v_a_1750_;
v___y_1776_ = v_a_1751_;
v___y_1777_ = v_a_1752_;
v___y_1778_ = v_a_1753_;
v___y_1779_ = v_a_1754_;
v___y_1780_ = v_a_1755_;
v___y_1781_ = v_a_1756_;
v___y_1782_ = v_a_1757_;
v___y_1783_ = v___x_1845_;
v___y_1784_ = v_a_1759_;
goto v___jp_1774_;
}
else
{
lean_object* v_arg_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; 
v_arg_1864_ = lean_ctor_get(v___x_1862_, 1);
lean_inc_ref(v_arg_1864_);
v___x_1865_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1862_);
v___x_1866_ = l_Lean_Expr_isConstOf(v___x_1865_, v___x_1854_);
lean_dec_ref(v___x_1865_);
if (v___x_1866_ == 0)
{
lean_dec_ref(v_arg_1864_);
lean_dec_ref(v_arg_1861_);
lean_dec_ref(v_arg_1858_);
lean_dec_ref(v___x_1853_);
lean_dec_ref(v_arg_1852_);
lean_dec_ref(v_arg_1849_);
lean_dec_ref(v_arg_1846_);
v___y_1775_ = v_a_1750_;
v___y_1776_ = v_a_1751_;
v___y_1777_ = v_a_1752_;
v___y_1778_ = v_a_1753_;
v___y_1779_ = v_a_1754_;
v___y_1780_ = v_a_1755_;
v___y_1781_ = v_a_1756_;
v___y_1782_ = v_a_1757_;
v___y_1783_ = v___x_1845_;
v___y_1784_ = v_a_1759_;
goto v___jp_1774_;
}
else
{
lean_object* v___x_1867_; lean_object* v___x_1868_; uint8_t v___x_1869_; 
v___x_1867_ = lean_st_ref_get(v_a_1750_);
v___x_1868_ = lean_st_ref_get(v_a_1750_);
v___x_1869_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1867_, v_arg_1849_, v_arg_1861_);
lean_dec(v___x_1867_);
if (v___x_1869_ == 0)
{
lean_dec(v___x_1868_);
v___y_1788_ = v___x_1866_;
v___y_1789_ = v_arg_1849_;
v___y_1790_ = v_arg_1864_;
v___y_1791_ = v_arg_1852_;
v___y_1792_ = v___x_1853_;
v___y_1793_ = v_arg_1846_;
v___y_1794_ = v_arg_1858_;
v___y_1795_ = v___x_1845_;
v___y_1796_ = v_arg_1861_;
v___y_1797_ = v___x_1869_;
goto v___jp_1787_;
}
else
{
uint8_t v___x_1870_; 
v___x_1870_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1868_, v_arg_1846_, v_arg_1858_);
lean_dec(v___x_1868_);
v___y_1788_ = v___x_1866_;
v___y_1789_ = v_arg_1849_;
v___y_1790_ = v_arg_1864_;
v___y_1791_ = v_arg_1852_;
v___y_1792_ = v___x_1853_;
v___y_1793_ = v_arg_1846_;
v___y_1794_ = v_arg_1858_;
v___y_1795_ = v___x_1845_;
v___y_1796_ = v_arg_1861_;
v___y_1797_ = v___x_1870_;
goto v___jp_1787_;
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
LEAN_EXPORT void l_Lean_Meta_Grind_mkEqCongrProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_1748_ = stack[0].m_obj;
lean_object* v_rhs_1749_ = stack[1].m_obj;
lean_object* v_a_1750_ = stack[2].m_obj;
lean_object* v_a_1751_ = stack[3].m_obj;
lean_object* v_a_1752_ = stack[4].m_obj;
lean_object* v_a_1753_ = stack[5].m_obj;
lean_object* v_a_1754_ = stack[6].m_obj;
lean_object* v_a_1755_ = stack[7].m_obj;
lean_object* v_a_1756_ = stack[8].m_obj;
lean_object* v_a_1757_ = stack[9].m_obj;
lean_object* v_a_1758_ = stack[10].m_obj;
lean_object* v_a_1759_ = stack[11].m_obj;
lean_object* v_res_1875_;
v_res_1875_ = l_Lean_Meta_Grind_mkEqCongrProof(v_lhs_1748_, v_rhs_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
stack->m_obj
 = v_res_1875_;
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1886_ = lean_box(0);
v___x_1887_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3));
v___x_1888_ = l_Lean_mkConst(v___x_1887_, v___x_1886_);
return v___x_1888_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(lean_object* v_lhs_1889_, lean_object* v_rhs_1890_, uint8_t v_heq_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v___x_1903_; lean_object* v_p_1904_; lean_object* v_hp_1905_; lean_object* v___x_1906_; lean_object* v_q_1907_; lean_object* v_hq_1908_; uint8_t v___x_1909_; lean_object* v___x_1910_; 
v___x_1903_ = l_Lean_Expr_appFn_x21(v_lhs_1889_);
v_p_1904_ = l_Lean_Expr_appArg_x21(v___x_1903_);
lean_dec_ref(v___x_1903_);
v_hp_1905_ = l_Lean_Expr_appArg_x21(v_lhs_1889_);
v___x_1906_ = l_Lean_Expr_appFn_x21(v_rhs_1890_);
v_q_1907_ = l_Lean_Expr_appArg_x21(v___x_1906_);
lean_dec_ref(v___x_1906_);
v_hq_1908_ = l_Lean_Expr_appArg_x21(v_rhs_1890_);
v___x_1909_ = 0;
lean_inc_ref(v_q_1907_);
lean_inc_ref(v_p_1904_);
v___x_1910_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_p_1904_, v_q_1907_, v___x_1909_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
lean_dec_ref_known(v___x_1910_, 1);
v___x_1912_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4);
v___x_1913_ = l_Lean_mkApp5(v___x_1912_, v_p_1904_, v_q_1907_, v_a_1911_, v_hp_1905_, v_hq_1908_);
v___x_1914_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v___x_1913_, v_heq_1891_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
return v___x_1914_;
}
else
{
lean_dec_ref(v_hq_1908_);
lean_dec_ref(v_q_1907_);
lean_dec_ref(v_hp_1905_);
lean_dec_ref(v_p_1904_);
return v___x_1910_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_1889_ = stack[0].m_obj;
lean_object* v_rhs_1890_ = stack[1].m_obj;
uint8_t v_heq_1891_ = stack[2].m_num;
lean_object* v_a_1892_ = stack[3].m_obj;
lean_object* v_a_1893_ = stack[4].m_obj;
lean_object* v_a_1894_ = stack[5].m_obj;
lean_object* v_a_1895_ = stack[6].m_obj;
lean_object* v_a_1896_ = stack[7].m_obj;
lean_object* v_a_1897_ = stack[8].m_obj;
lean_object* v_a_1898_ = stack[9].m_obj;
lean_object* v_a_1899_ = stack[10].m_obj;
lean_object* v_a_1900_ = stack[11].m_obj;
lean_object* v_a_1901_ = stack[12].m_obj;
lean_object* v_res_1915_;
v_res_1915_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_1889_, v_rhs_1890_, v_heq_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
stack->m_obj
 = v_res_1915_;
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1926_ = lean_box(0);
v___x_1927_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1));
v___x_1928_ = l_Lean_mkConst(v___x_1927_, v___x_1926_);
return v___x_1928_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(lean_object* v_lhs_1929_, lean_object* v_rhs_1930_, uint8_t v_heq_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v___x_1943_; lean_object* v_p_1944_; lean_object* v_hp_1945_; lean_object* v___x_1946_; lean_object* v_q_1947_; lean_object* v_hq_1948_; uint8_t v___x_1949_; lean_object* v___x_1950_; 
v___x_1943_ = l_Lean_Expr_appFn_x21(v_lhs_1929_);
v_p_1944_ = l_Lean_Expr_appArg_x21(v___x_1943_);
lean_dec_ref(v___x_1943_);
v_hp_1945_ = l_Lean_Expr_appArg_x21(v_lhs_1929_);
v___x_1946_ = l_Lean_Expr_appFn_x21(v_rhs_1930_);
v_q_1947_ = l_Lean_Expr_appArg_x21(v___x_1946_);
lean_dec_ref(v___x_1946_);
v_hq_1948_ = l_Lean_Expr_appArg_x21(v_rhs_1930_);
v___x_1949_ = 0;
lean_inc_ref(v_q_1947_);
lean_inc_ref(v_p_1944_);
v___x_1950_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_p_1944_, v_q_1947_, v___x_1949_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref_known(v___x_1950_, 1);
v___x_1952_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2);
v___x_1953_ = l_Lean_mkApp5(v___x_1952_, v_p_1944_, v_q_1947_, v_a_1951_, v_hp_1945_, v_hq_1948_);
v___x_1954_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v___x_1953_, v_heq_1931_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
return v___x_1954_;
}
else
{
lean_dec_ref(v_hq_1948_);
lean_dec_ref(v_q_1947_);
lean_dec_ref(v_hp_1945_);
lean_dec_ref(v_p_1944_);
return v___x_1950_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_1929_ = stack[0].m_obj;
lean_object* v_rhs_1930_ = stack[1].m_obj;
uint8_t v_heq_1931_ = stack[2].m_num;
lean_object* v_a_1932_ = stack[3].m_obj;
lean_object* v_a_1933_ = stack[4].m_obj;
lean_object* v_a_1934_ = stack[5].m_obj;
lean_object* v_a_1935_ = stack[6].m_obj;
lean_object* v_a_1936_ = stack[7].m_obj;
lean_object* v_a_1937_ = stack[8].m_obj;
lean_object* v_a_1938_ = stack[9].m_obj;
lean_object* v_a_1939_ = stack[10].m_obj;
lean_object* v_a_1940_ = stack[11].m_obj;
lean_object* v_a_1941_ = stack[12].m_obj;
lean_object* v_res_1955_;
v_res_1955_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_1929_, v_rhs_1930_, v_heq_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
stack->m_obj
 = v_res_1955_;
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(lean_object* v_lhs_1956_, lean_object* v_rhs_1957_, uint8_t v_heq_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_){
_start:
{
if (lean_obj_tag(v_lhs_1956_) == 7)
{
if (lean_obj_tag(v_rhs_1957_) == 7)
{
lean_object* v_binderType_1970_; lean_object* v_body_1971_; lean_object* v_binderType_1972_; lean_object* v_body_1973_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_2005_; lean_object* v___x_2034_; uint8_t v_transparency_2035_; uint8_t v___x_2036_; uint8_t v___x_2037_; 
v_binderType_1970_ = lean_ctor_get(v_lhs_1956_, 1);
lean_inc_ref(v_binderType_1970_);
v_body_1971_ = lean_ctor_get(v_lhs_1956_, 2);
lean_inc_ref(v_body_1971_);
lean_dec_ref_known(v_lhs_1956_, 3);
v_binderType_1972_ = lean_ctor_get(v_rhs_1957_, 1);
lean_inc_ref(v_binderType_1972_);
v_body_1973_ = lean_ctor_get(v_rhs_1957_, 2);
lean_inc_ref(v_body_1973_);
lean_dec_ref_known(v_rhs_1957_, 3);
v___x_2034_ = l_Lean_Meta_Context_config(v_a_1965_);
v_transparency_2035_ = lean_ctor_get_uint8(v___x_2034_, 9);
lean_dec_ref(v___x_2034_);
v___x_2036_ = 1;
v___x_2037_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2035_, v___x_2036_);
if (v___x_2037_ == 0)
{
lean_object* v_keyedConfig_2038_; uint8_t v_trackZetaDelta_2039_; lean_object* v_zetaDeltaSet_2040_; lean_object* v_lctx_2041_; lean_object* v_localInstances_2042_; lean_object* v_defEqCtx_x3f_2043_; lean_object* v_synthPendingDepth_2044_; lean_object* v_customCanUnfoldPredicate_x3f_2045_; uint8_t v_univApprox_2046_; uint8_t v_inTypeClassResolution_2047_; uint8_t v_cacheInferType_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v_keyedConfig_2038_ = lean_ctor_get(v_a_1965_, 0);
v_trackZetaDelta_2039_ = lean_ctor_get_uint8(v_a_1965_, sizeof(void*)*7);
v_zetaDeltaSet_2040_ = lean_ctor_get(v_a_1965_, 1);
v_lctx_2041_ = lean_ctor_get(v_a_1965_, 2);
v_localInstances_2042_ = lean_ctor_get(v_a_1965_, 3);
v_defEqCtx_x3f_2043_ = lean_ctor_get(v_a_1965_, 4);
v_synthPendingDepth_2044_ = lean_ctor_get(v_a_1965_, 5);
v_customCanUnfoldPredicate_x3f_2045_ = lean_ctor_get(v_a_1965_, 6);
v_univApprox_2046_ = lean_ctor_get_uint8(v_a_1965_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2047_ = lean_ctor_get_uint8(v_a_1965_, sizeof(void*)*7 + 2);
v_cacheInferType_2048_ = lean_ctor_get_uint8(v_a_1965_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2038_);
v___x_2049_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2036_, v_keyedConfig_2038_);
lean_inc(v_customCanUnfoldPredicate_x3f_2045_);
lean_inc(v_synthPendingDepth_2044_);
lean_inc(v_defEqCtx_x3f_2043_);
lean_inc_ref(v_localInstances_2042_);
lean_inc_ref(v_lctx_2041_);
lean_inc(v_zetaDeltaSet_2040_);
v___x_2050_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
lean_ctor_set(v___x_2050_, 1, v_zetaDeltaSet_2040_);
lean_ctor_set(v___x_2050_, 2, v_lctx_2041_);
lean_ctor_set(v___x_2050_, 3, v_localInstances_2042_);
lean_ctor_set(v___x_2050_, 4, v_defEqCtx_x3f_2043_);
lean_ctor_set(v___x_2050_, 5, v_synthPendingDepth_2044_);
lean_ctor_set(v___x_2050_, 6, v_customCanUnfoldPredicate_x3f_2045_);
lean_ctor_set_uint8(v___x_2050_, sizeof(void*)*7, v_trackZetaDelta_2039_);
lean_ctor_set_uint8(v___x_2050_, sizeof(void*)*7 + 1, v_univApprox_2046_);
lean_ctor_set_uint8(v___x_2050_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2047_);
lean_ctor_set_uint8(v___x_2050_, sizeof(void*)*7 + 3, v_cacheInferType_2048_);
lean_inc_ref(v_binderType_1970_);
v___x_2051_ = l_Lean_Meta_getLevel(v_binderType_1970_, v___x_2050_, v_a_1966_, v_a_1967_, v_a_1968_);
lean_dec_ref_known(v___x_2050_, 7);
v___y_2005_ = v___x_2051_;
goto v___jp_2004_;
}
else
{
lean_object* v___x_2052_; 
lean_inc_ref(v_binderType_1970_);
v___x_2052_ = l_Lean_Meta_getLevel(v_binderType_1970_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
v___y_2005_ = v___x_2052_;
goto v___jp_2004_;
}
v___jp_1974_:
{
if (lean_obj_tag(v___y_1976_) == 0)
{
lean_object* v_a_1977_; uint8_t v___x_1978_; lean_object* v___x_1979_; 
v_a_1977_ = lean_ctor_get(v___y_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___y_1976_, 1);
v___x_1978_ = 0;
lean_inc_ref(v_binderType_1972_);
lean_inc_ref(v_binderType_1970_);
v___x_1979_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_binderType_1970_, v_binderType_1972_, v___x_1978_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1981_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___x_1979_, 1);
lean_inc_ref(v_body_1973_);
lean_inc_ref(v_body_1971_);
v___x_1981_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_body_1971_, v_body_1973_, v___x_1978_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1995_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_1995_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1995_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1986_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__1));
v___x_1987_ = lean_box(0);
v___x_1988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1988_, 0, v_a_1977_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___y_1975_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = l_Lean_mkConst(v___x_1986_, v___x_1989_);
v___x_1991_ = l_Lean_mkApp6(v___x_1990_, v_binderType_1970_, v_binderType_1972_, v_body_1971_, v_body_1973_, v_a_1980_, v_a_1982_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1991_);
v___x_1993_ = v___x_1984_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
else
{
lean_dec(v_a_1980_);
lean_dec(v_a_1977_);
lean_dec(v___y_1975_);
lean_dec_ref(v_body_1973_);
lean_dec_ref(v_binderType_1972_);
lean_dec_ref(v_body_1971_);
lean_dec_ref(v_binderType_1970_);
return v___x_1981_;
}
}
else
{
lean_dec(v_a_1977_);
lean_dec(v___y_1975_);
lean_dec_ref(v_body_1973_);
lean_dec_ref(v_binderType_1972_);
lean_dec_ref(v_body_1971_);
lean_dec_ref(v_binderType_1970_);
return v___x_1979_;
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec(v___y_1975_);
lean_dec_ref(v_body_1973_);
lean_dec_ref(v_binderType_1972_);
lean_dec_ref(v_body_1971_);
lean_dec_ref(v_binderType_1970_);
v_a_1996_ = lean_ctor_get(v___y_1976_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___y_1976_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___y_1976_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___y_1976_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
v___jp_2004_:
{
if (lean_obj_tag(v___y_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v___x_2007_; uint8_t v_transparency_2008_; uint8_t v___x_2009_; uint8_t v___x_2010_; 
v_a_2006_ = lean_ctor_get(v___y_2005_, 0);
lean_inc(v_a_2006_);
lean_dec_ref_known(v___y_2005_, 1);
v___x_2007_ = l_Lean_Meta_Context_config(v_a_1965_);
v_transparency_2008_ = lean_ctor_get_uint8(v___x_2007_, 9);
lean_dec_ref(v___x_2007_);
v___x_2009_ = 1;
v___x_2010_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2008_, v___x_2009_);
if (v___x_2010_ == 0)
{
lean_object* v_keyedConfig_2011_; uint8_t v_trackZetaDelta_2012_; lean_object* v_zetaDeltaSet_2013_; lean_object* v_lctx_2014_; lean_object* v_localInstances_2015_; lean_object* v_defEqCtx_x3f_2016_; lean_object* v_synthPendingDepth_2017_; lean_object* v_customCanUnfoldPredicate_x3f_2018_; uint8_t v_univApprox_2019_; uint8_t v_inTypeClassResolution_2020_; uint8_t v_cacheInferType_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v_keyedConfig_2011_ = lean_ctor_get(v_a_1965_, 0);
v_trackZetaDelta_2012_ = lean_ctor_get_uint8(v_a_1965_, sizeof(void*)*7);
v_zetaDeltaSet_2013_ = lean_ctor_get(v_a_1965_, 1);
v_lctx_2014_ = lean_ctor_get(v_a_1965_, 2);
v_localInstances_2015_ = lean_ctor_get(v_a_1965_, 3);
v_defEqCtx_x3f_2016_ = lean_ctor_get(v_a_1965_, 4);
v_synthPendingDepth_2017_ = lean_ctor_get(v_a_1965_, 5);
v_customCanUnfoldPredicate_x3f_2018_ = lean_ctor_get(v_a_1965_, 6);
v_univApprox_2019_ = lean_ctor_get_uint8(v_a_1965_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2020_ = lean_ctor_get_uint8(v_a_1965_, sizeof(void*)*7 + 2);
v_cacheInferType_2021_ = lean_ctor_get_uint8(v_a_1965_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2011_);
v___x_2022_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2009_, v_keyedConfig_2011_);
lean_inc(v_customCanUnfoldPredicate_x3f_2018_);
lean_inc(v_synthPendingDepth_2017_);
lean_inc(v_defEqCtx_x3f_2016_);
lean_inc_ref(v_localInstances_2015_);
lean_inc_ref(v_lctx_2014_);
lean_inc(v_zetaDeltaSet_2013_);
v___x_2023_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
lean_ctor_set(v___x_2023_, 1, v_zetaDeltaSet_2013_);
lean_ctor_set(v___x_2023_, 2, v_lctx_2014_);
lean_ctor_set(v___x_2023_, 3, v_localInstances_2015_);
lean_ctor_set(v___x_2023_, 4, v_defEqCtx_x3f_2016_);
lean_ctor_set(v___x_2023_, 5, v_synthPendingDepth_2017_);
lean_ctor_set(v___x_2023_, 6, v_customCanUnfoldPredicate_x3f_2018_);
lean_ctor_set_uint8(v___x_2023_, sizeof(void*)*7, v_trackZetaDelta_2012_);
lean_ctor_set_uint8(v___x_2023_, sizeof(void*)*7 + 1, v_univApprox_2019_);
lean_ctor_set_uint8(v___x_2023_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2020_);
lean_ctor_set_uint8(v___x_2023_, sizeof(void*)*7 + 3, v_cacheInferType_2021_);
lean_inc_ref(v_body_1971_);
v___x_2024_ = l_Lean_Meta_getLevel(v_body_1971_, v___x_2023_, v_a_1966_, v_a_1967_, v_a_1968_);
lean_dec_ref_known(v___x_2023_, 7);
v___y_1975_ = v_a_2006_;
v___y_1976_ = v___x_2024_;
goto v___jp_1974_;
}
else
{
lean_object* v___x_2025_; 
lean_inc_ref(v_body_1971_);
v___x_2025_ = l_Lean_Meta_getLevel(v_body_1971_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
v___y_1975_ = v_a_2006_;
v___y_1976_ = v___x_2025_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec_ref(v_body_1973_);
lean_dec_ref(v_binderType_1972_);
lean_dec_ref(v_body_1971_);
lean_dec_ref(v_binderType_1970_);
v_a_2026_ = lean_ctor_get(v___y_2005_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___y_2005_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___y_2005_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___y_2005_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
lean_dec_ref_known(v_lhs_1956_, 3);
lean_dec_ref(v_rhs_1957_);
v___x_2053_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3);
v___x_2054_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2053_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
return v___x_2054_;
}
}
else
{
lean_object* v___x_2055_; 
lean_inc_ref(v_lhs_1956_);
v___x_2055_ = l_Lean_Meta_Grind_useFunCC___redArg(v_lhs_1956_, v_a_1959_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; uint8_t v___x_2057_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2055_, 1);
v___x_2057_ = lean_unbox(v_a_2056_);
lean_dec(v_a_2056_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2058_ = l_Lean_Expr_getAppNumArgs(v_lhs_1956_);
v___x_2059_ = l_Lean_Expr_getAppNumArgs(v_rhs_1957_);
v___x_2060_ = lean_nat_dec_eq(v___x_2059_, v___x_2058_);
lean_dec(v___x_2059_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
lean_dec(v___x_2058_);
lean_dec_ref(v_rhs_1957_);
lean_dec_ref(v_lhs_1956_);
v___x_2061_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5);
v___x_2062_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2061_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
return v___x_2062_;
}
else
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2063_ = l_Lean_Expr_getAppFn(v_lhs_1956_);
v___x_2064_ = l_Lean_Expr_getAppFn(v_rhs_1957_);
v___x_2088_ = lean_unsigned_to_nat(2u);
v___x_2089_ = lean_nat_dec_eq(v___x_2058_, v___x_2088_);
if (v___x_2089_ == 0)
{
goto v___jp_2090_;
}
else
{
lean_object* v___x_2095_; uint8_t v___x_2096_; 
v___x_2095_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9));
v___x_2096_ = l_Lean_Expr_isConstOf(v___x_2063_, v___x_2095_);
if (v___x_2096_ == 0)
{
goto v___jp_2090_;
}
else
{
uint8_t v___x_2097_; 
v___x_2097_ = l_Lean_Expr_isConstOf(v___x_2064_, v___x_2095_);
if (v___x_2097_ == 0)
{
goto v___jp_2090_;
}
else
{
lean_object* v___x_2098_; 
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___x_2063_);
lean_dec(v___x_2058_);
v___x_2098_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_1956_, v_rhs_1957_, v_heq_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
lean_dec_ref(v_rhs_1957_);
lean_dec_ref(v_lhs_1956_);
return v___x_2098_;
}
}
}
v___jp_2065_:
{
lean_object* v___x_2066_; 
lean_inc_ref(v_rhs_1957_);
lean_inc_ref(v_lhs_1956_);
v___x_2066_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(v_lhs_1956_, v_rhs_1957_, v___x_2063_, v___x_2064_, v___x_2058_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
lean_dec_ref(v___x_2064_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; uint8_t v___x_2068_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2067_);
lean_dec_ref_known(v___x_2066_, 1);
v___x_2068_ = lean_unbox(v_a_2067_);
lean_dec(v_a_2067_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; 
v___x_2069_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_1956_, v_rhs_1957_, v_heq_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
return v___x_2069_;
}
else
{
lean_object* v___x_2070_; 
v___x_2070_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_1956_, v_rhs_1957_, v_heq_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
lean_dec_ref(v_rhs_1957_);
lean_dec_ref(v_lhs_1956_);
return v___x_2070_;
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec_ref(v_rhs_1957_);
lean_dec_ref(v_lhs_1956_);
v_a_2071_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2066_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2066_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
v___jp_2079_:
{
lean_object* v___x_2080_; uint8_t v___x_2081_; 
v___x_2080_ = lean_unsigned_to_nat(3u);
v___x_2081_ = lean_nat_dec_eq(v___x_2058_, v___x_2080_);
if (v___x_2081_ == 0)
{
goto v___jp_2065_;
}
else
{
lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2082_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_2083_ = l_Lean_Expr_isConstOf(v___x_2063_, v___x_2082_);
if (v___x_2083_ == 0)
{
goto v___jp_2065_;
}
else
{
uint8_t v___x_2084_; 
v___x_2084_ = l_Lean_Expr_isConstOf(v___x_2064_, v___x_2082_);
if (v___x_2084_ == 0)
{
goto v___jp_2065_;
}
else
{
lean_object* v___x_2085_; 
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___x_2063_);
lean_dec(v___x_2058_);
v___x_2085_ = l_Lean_Meta_Grind_mkEqCongrProof(v_lhs_1956_, v_rhs_1957_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
if (lean_obj_tag(v___x_2085_) == 0)
{
if (v_heq_1958_ == 0)
{
return v___x_2085_;
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2087_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2085_, 1);
v___x_2087_ = l_Lean_Meta_mkHEqOfEq(v_a_2086_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
return v___x_2087_;
}
}
else
{
return v___x_2085_;
}
}
}
}
}
v___jp_2090_:
{
if (v___x_2089_ == 0)
{
goto v___jp_2079_;
}
else
{
lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2091_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7));
v___x_2092_ = l_Lean_Expr_isConstOf(v___x_2063_, v___x_2091_);
if (v___x_2092_ == 0)
{
goto v___jp_2079_;
}
else
{
uint8_t v___x_2093_; 
v___x_2093_ = l_Lean_Expr_isConstOf(v___x_2064_, v___x_2091_);
if (v___x_2093_ == 0)
{
goto v___jp_2079_;
}
else
{
lean_object* v___x_2094_; 
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___x_2063_);
lean_dec(v___x_2058_);
v___x_2094_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_1956_, v_rhs_1957_, v_heq_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
lean_dec_ref(v_rhs_1957_);
lean_dec_ref(v_lhs_1956_);
return v___x_2094_;
}
}
}
}
}
}
else
{
lean_object* v___x_2099_; 
v___x_2099_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_1956_, v_rhs_1957_, v_heq_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
return v___x_2099_;
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec_ref(v_rhs_1957_);
lean_dec_ref(v_lhs_1956_);
v_a_2100_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2055_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2055_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_1956_ = stack[0].m_obj;
lean_object* v_rhs_1957_ = stack[1].m_obj;
uint8_t v_heq_1958_ = stack[2].m_num;
lean_object* v_a_1959_ = stack[3].m_obj;
lean_object* v_a_1960_ = stack[4].m_obj;
lean_object* v_a_1961_ = stack[5].m_obj;
lean_object* v_a_1962_ = stack[6].m_obj;
lean_object* v_a_1963_ = stack[7].m_obj;
lean_object* v_a_1964_ = stack[8].m_obj;
lean_object* v_a_1965_ = stack[9].m_obj;
lean_object* v_a_1966_ = stack[10].m_obj;
lean_object* v_a_1967_ = stack[11].m_obj;
lean_object* v_a_1968_ = stack[12].m_obj;
lean_object* v_res_2108_;
v_res_2108_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(v_lhs_1956_, v_rhs_1957_, v_heq_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
stack->m_obj
 = v_res_2108_;
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(lean_object* v_lhs_2109_, lean_object* v_rhs_2110_, lean_object* v_h_2111_, uint8_t v_flipped_2112_, uint8_t v_heq_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_){
_start:
{
lean_object* v___x_2125_; uint8_t v___x_2126_; 
v___x_2125_ = l_Lean_Meta_Grind_congrPlaceholderProof;
v___x_2126_ = lean_expr_eqv(v_h_2111_, v___x_2125_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; uint8_t v___x_2128_; 
v___x_2127_ = l_Lean_Meta_Grind_eqCongrSymmPlaceholderProof;
v___x_2128_ = lean_expr_eqv(v_h_2111_, v___x_2127_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2129_; 
lean_dec_ref(v_rhs_2110_);
lean_dec_ref(v_lhs_2109_);
v___x_2129_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(v_h_2111_, v_flipped_2112_, v_heq_2113_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
return v___x_2129_;
}
else
{
lean_object* v___x_2130_; 
lean_dec_ref(v_h_2111_);
v___x_2130_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(v_lhs_2109_, v_rhs_2110_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
if (lean_obj_tag(v___x_2130_) == 0)
{
if (v_heq_2113_ == 0)
{
return v___x_2130_;
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2132_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = l_Lean_Meta_mkHEqOfEq(v_a_2131_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
return v___x_2132_;
}
}
else
{
return v___x_2130_;
}
}
}
else
{
lean_object* v___x_2133_; 
lean_dec_ref(v_h_2111_);
v___x_2133_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(v_lhs_2109_, v_rhs_2110_, v_heq_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
return v___x_2133_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_2109_ = stack[0].m_obj;
lean_object* v_rhs_2110_ = stack[1].m_obj;
lean_object* v_h_2111_ = stack[2].m_obj;
uint8_t v_flipped_2112_ = stack[3].m_num;
uint8_t v_heq_2113_ = stack[4].m_num;
lean_object* v_a_2114_ = stack[5].m_obj;
lean_object* v_a_2115_ = stack[6].m_obj;
lean_object* v_a_2116_ = stack[7].m_obj;
lean_object* v_a_2117_ = stack[8].m_obj;
lean_object* v_a_2118_ = stack[9].m_obj;
lean_object* v_a_2119_ = stack[10].m_obj;
lean_object* v_a_2120_ = stack[11].m_obj;
lean_object* v_a_2121_ = stack[12].m_obj;
lean_object* v_a_2122_ = stack[13].m_obj;
lean_object* v_a_2123_ = stack[14].m_obj;
lean_object* v_res_2134_;
v_res_2134_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_lhs_2109_, v_rhs_2110_, v_h_2111_, v_flipped_2112_, v_heq_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
stack->m_obj
 = v_res_2134_;
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1(void){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2136_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2137_ = lean_unsigned_to_nat(29u);
v___x_2138_ = lean_unsigned_to_nat(288u);
v___x_2139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0));
v___x_2140_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2141_ = l_mkPanicMessageWithDecl(v___x_2140_, v___x_2139_, v___x_2138_, v___x_2137_, v___x_2136_);
return v___x_2141_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2(void){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2142_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2143_ = lean_unsigned_to_nat(35u);
v___x_2144_ = lean_unsigned_to_nat(287u);
v___x_2145_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0));
v___x_2146_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2147_ = l_mkPanicMessageWithDecl(v___x_2146_, v___x_2145_, v___x_2144_, v___x_2143_, v___x_2142_);
return v___x_2147_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(lean_object* v_lhs_2148_, lean_object* v_common_2149_, lean_object* v_acc_2150_, uint8_t v_heq_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_){
_start:
{
size_t v___x_2163_; size_t v___x_2164_; uint8_t v___x_2165_; 
v___x_2163_ = lean_ptr_addr(v_lhs_2148_);
v___x_2164_ = lean_ptr_addr(v_common_2149_);
v___x_2165_ = lean_usize_dec_eq(v___x_2163_, v___x_2164_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = lean_st_ref_get(v_a_2152_);
lean_inc_ref(v_lhs_2148_);
v___x_2167_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2166_, v_lhs_2148_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
lean_dec(v___x_2166_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v_target_x3f_2169_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2167_, 1);
v_target_x3f_2169_ = lean_ctor_get(v_a_2168_, 4);
lean_inc(v_target_x3f_2169_);
if (lean_obj_tag(v_target_x3f_2169_) == 1)
{
lean_object* v_proof_x3f_2170_; 
v_proof_x3f_2170_ = lean_ctor_get(v_a_2168_, 5);
lean_inc(v_proof_x3f_2170_);
if (lean_obj_tag(v_proof_x3f_2170_) == 1)
{
uint8_t v_flipped_2171_; lean_object* v_val_2172_; lean_object* v_val_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2201_; 
v_flipped_2171_ = lean_ctor_get_uint8(v_a_2168_, sizeof(void*)*12);
lean_dec(v_a_2168_);
v_val_2172_ = lean_ctor_get(v_target_x3f_2169_, 0);
lean_inc(v_val_2172_);
lean_dec_ref_known(v_target_x3f_2169_, 1);
v_val_2173_ = lean_ctor_get(v_proof_x3f_2170_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_proof_x3f_2170_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2175_ = v_proof_x3f_2170_;
v_isShared_2176_ = v_isSharedCheck_2201_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_val_2173_);
lean_dec(v_proof_x3f_2170_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2201_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; 
lean_inc(v_val_2172_);
v___x_2177_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_lhs_2148_, v_val_2172_, v_val_2173_, v_flipped_2171_, v_heq_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2179_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
v___x_2179_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_acc_2150_, v_a_2178_, v_heq_2151_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2182_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref_known(v___x_2179_, 1);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v_a_2180_);
v___x_2182_ = v___x_2175_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2180_);
v___x_2182_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
v_lhs_2148_ = v_val_2172_;
v_acc_2150_ = v___x_2182_;
goto _start;
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_del_object(v___x_2175_);
lean_dec(v_val_2172_);
v_a_2185_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2179_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2179_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_del_object(v___x_2175_);
lean_dec(v_val_2172_);
lean_dec(v_acc_2150_);
v_a_2193_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2177_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2177_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
}
else
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
lean_dec(v_proof_x3f_2170_);
lean_dec_ref_known(v_target_x3f_2169_, 1);
lean_dec(v_a_2168_);
lean_dec(v_acc_2150_);
lean_dec_ref(v_lhs_2148_);
v___x_2202_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1);
v___x_2203_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2202_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
return v___x_2203_;
}
}
else
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
lean_dec(v_target_x3f_2169_);
lean_dec(v_a_2168_);
lean_dec(v_acc_2150_);
lean_dec_ref(v_lhs_2148_);
v___x_2204_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2);
v___x_2205_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2204_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
return v___x_2205_;
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec(v_acc_2150_);
lean_dec_ref(v_lhs_2148_);
v_a_2206_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2167_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2167_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
else
{
lean_object* v___x_2214_; 
lean_dec_ref(v_lhs_2148_);
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v_acc_2150_);
return v___x_2214_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_2148_ = stack[0].m_obj;
lean_object* v_common_2149_ = stack[1].m_obj;
lean_object* v_acc_2150_ = stack[2].m_obj;
uint8_t v_heq_2151_ = stack[3].m_num;
lean_object* v_a_2152_ = stack[4].m_obj;
lean_object* v_a_2153_ = stack[5].m_obj;
lean_object* v_a_2154_ = stack[6].m_obj;
lean_object* v_a_2155_ = stack[7].m_obj;
lean_object* v_a_2156_ = stack[8].m_obj;
lean_object* v_a_2157_ = stack[9].m_obj;
lean_object* v_a_2158_ = stack[10].m_obj;
lean_object* v_a_2159_ = stack[11].m_obj;
lean_object* v_a_2160_ = stack[12].m_obj;
lean_object* v_a_2161_ = stack[13].m_obj;
lean_object* v_res_2215_;
v_res_2215_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_2148_, v_common_2149_, v_acc_2150_, v_heq_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
stack->m_obj
 = v_res_2215_;
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2217_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2218_ = lean_unsigned_to_nat(29u);
v___x_2219_ = lean_unsigned_to_nat(300u);
v___x_2220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0));
v___x_2221_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2222_ = l_mkPanicMessageWithDecl(v___x_2221_, v___x_2220_, v___x_2219_, v___x_2218_, v___x_2217_);
return v___x_2222_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2223_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2224_ = lean_unsigned_to_nat(35u);
v___x_2225_ = lean_unsigned_to_nat(299u);
v___x_2226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0));
v___x_2227_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2228_ = l_mkPanicMessageWithDecl(v___x_2227_, v___x_2226_, v___x_2225_, v___x_2224_, v___x_2223_);
return v___x_2228_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(lean_object* v_rhs_2229_, lean_object* v_common_2230_, lean_object* v_lhsEqCommon_x3f_2231_, uint8_t v_heq_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_){
_start:
{
size_t v___x_2244_; size_t v___x_2245_; uint8_t v___x_2246_; 
v___x_2244_ = lean_ptr_addr(v_rhs_2229_);
v___x_2245_ = lean_ptr_addr(v_common_2230_);
v___x_2246_ = lean_usize_dec_eq(v___x_2244_, v___x_2245_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = lean_st_ref_get(v_a_2233_);
lean_inc_ref(v_rhs_2229_);
v___x_2248_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2247_, v_rhs_2229_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
lean_dec(v___x_2247_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v_target_x3f_2250_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_a_2249_);
lean_dec_ref_known(v___x_2248_, 1);
v_target_x3f_2250_ = lean_ctor_get(v_a_2249_, 4);
lean_inc(v_target_x3f_2250_);
if (lean_obj_tag(v_target_x3f_2250_) == 1)
{
lean_object* v_proof_x3f_2251_; 
v_proof_x3f_2251_ = lean_ctor_get(v_a_2249_, 5);
lean_inc(v_proof_x3f_2251_);
if (lean_obj_tag(v_proof_x3f_2251_) == 1)
{
uint8_t v_flipped_2252_; lean_object* v_val_2253_; lean_object* v_val_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2293_; 
v_flipped_2252_ = lean_ctor_get_uint8(v_a_2249_, sizeof(void*)*12);
lean_dec(v_a_2249_);
v_val_2253_ = lean_ctor_get(v_target_x3f_2250_, 0);
lean_inc(v_val_2253_);
lean_dec_ref_known(v_target_x3f_2250_, 1);
v_val_2254_ = lean_ctor_get(v_proof_x3f_2251_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_proof_x3f_2251_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2256_ = v_proof_x3f_2251_;
v_isShared_2257_ = v_isSharedCheck_2293_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_val_2254_);
lean_dec(v_proof_x3f_2251_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2293_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
uint8_t v___y_2259_; 
if (v_flipped_2252_ == 0)
{
uint8_t v___x_2292_; 
v___x_2292_ = 1;
v___y_2259_ = v___x_2292_;
goto v___jp_2258_;
}
else
{
v___y_2259_ = v___x_2246_;
goto v___jp_2258_;
}
v___jp_2258_:
{
lean_object* v___x_2260_; 
lean_inc(v_val_2253_);
v___x_2260_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_val_2253_, v_rhs_2229_, v_val_2254_, v___y_2259_, v_heq_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2262_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref_known(v___x_2260_, 1);
v___x_2262_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_val_2253_, v_common_2230_, v_lhsEqCommon_x3f_2231_, v_heq_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2264_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
lean_dec_ref_known(v___x_2262_, 1);
v___x_2264_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_a_2263_, v_a_2261_, v_heq_2232_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2275_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2267_ = v___x_2264_;
v_isShared_2268_ = v_isSharedCheck_2275_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2264_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2275_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 0, v_a_2265_);
v___x_2270_ = v___x_2256_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2272_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 0, v___x_2270_);
v___x_2272_ = v___x_2267_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_del_object(v___x_2256_);
v_a_2276_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2264_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2264_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
else
{
lean_dec(v_a_2261_);
lean_del_object(v___x_2256_);
return v___x_2262_;
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_del_object(v___x_2256_);
lean_dec(v_val_2253_);
lean_dec(v_lhsEqCommon_x3f_2231_);
v_a_2284_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2260_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2260_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
}
}
else
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
lean_dec(v_proof_x3f_2251_);
lean_dec_ref_known(v_target_x3f_2250_, 1);
lean_dec(v_a_2249_);
lean_dec(v_lhsEqCommon_x3f_2231_);
lean_dec_ref(v_rhs_2229_);
v___x_2294_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1);
v___x_2295_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2294_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
return v___x_2295_;
}
}
else
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
lean_dec(v_target_x3f_2250_);
lean_dec(v_a_2249_);
lean_dec(v_lhsEqCommon_x3f_2231_);
lean_dec_ref(v_rhs_2229_);
v___x_2296_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2);
v___x_2297_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2296_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
return v___x_2297_;
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec(v_lhsEqCommon_x3f_2231_);
lean_dec_ref(v_rhs_2229_);
v_a_2298_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2248_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2248_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
else
{
lean_object* v___x_2306_; 
lean_dec_ref(v_rhs_2229_);
v___x_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2306_, 0, v_lhsEqCommon_x3f_2231_);
return v___x_2306_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_0interp(lean_interpreter_value* stack)
{
lean_object* v_rhs_2229_ = stack[0].m_obj;
lean_object* v_common_2230_ = stack[1].m_obj;
lean_object* v_lhsEqCommon_x3f_2231_ = stack[2].m_obj;
uint8_t v_heq_2232_ = stack[3].m_num;
lean_object* v_a_2233_ = stack[4].m_obj;
lean_object* v_a_2234_ = stack[5].m_obj;
lean_object* v_a_2235_ = stack[6].m_obj;
lean_object* v_a_2236_ = stack[7].m_obj;
lean_object* v_a_2237_ = stack[8].m_obj;
lean_object* v_a_2238_ = stack[9].m_obj;
lean_object* v_a_2239_ = stack[10].m_obj;
lean_object* v_a_2240_ = stack[11].m_obj;
lean_object* v_a_2241_ = stack[12].m_obj;
lean_object* v_a_2242_ = stack[13].m_obj;
lean_object* v_res_2307_;
v_res_2307_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_2229_, v_common_2230_, v_lhsEqCommon_x3f_2231_, v_heq_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
stack->m_obj
 = v_res_2307_;
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3(void){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2308_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2309_ = lean_unsigned_to_nat(72u);
v___x_2310_ = lean_unsigned_to_nat(321u);
v___x_2311_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0));
v___x_2312_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2313_ = l_mkPanicMessageWithDecl(v___x_2312_, v___x_2311_, v___x_2310_, v___x_2309_, v___x_2308_);
return v___x_2313_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(lean_object* v_lhs_2314_, lean_object* v_rhs_2315_, uint8_t v_heq_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_){
_start:
{
size_t v___x_2328_; size_t v___x_2329_; uint8_t v___x_2330_; 
v___x_2328_ = lean_ptr_addr(v_lhs_2314_);
v___x_2329_ = lean_ptr_addr(v_rhs_2315_);
v___x_2330_ = lean_usize_dec_eq(v___x_2328_, v___x_2329_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; 
lean_inc_ref(v_lhs_2314_);
v___x_2331_ = l_Lean_Meta_Grind_getRootENode___redArg(v_lhs_2314_, v_a_2317_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; uint8_t v_heqProofs_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2331_, 1);
v_heqProofs_2333_ = lean_ctor_get_uint8(v_a_2332_, sizeof(void*)*12 + 4);
lean_dec(v_a_2332_);
v___x_2334_ = lean_st_ref_get(v_a_2317_);
lean_inc_ref(v_lhs_2314_);
v___x_2335_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2334_, v_lhs_2314_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
lean_dec(v___x_2334_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref_known(v___x_2335_, 1);
v___x_2337_ = lean_st_ref_get(v_a_2317_);
lean_inc_ref(v_rhs_2315_);
v___x_2338_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2337_, v_rhs_2315_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
lean_dec(v___x_2337_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v_root_2340_; lean_object* v_root_2341_; size_t v___x_2342_; size_t v___x_2343_; uint8_t v___x_2344_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2338_, 1);
v_root_2340_ = lean_ctor_get(v_a_2336_, 2);
lean_inc_ref(v_root_2340_);
lean_dec(v_a_2336_);
v_root_2341_ = lean_ctor_get(v_a_2339_, 2);
lean_inc_ref(v_root_2341_);
lean_dec(v_a_2339_);
v___x_2342_ = lean_ptr_addr(v_root_2340_);
lean_dec_ref(v_root_2340_);
v___x_2343_ = lean_ptr_addr(v_root_2341_);
lean_dec_ref(v_root_2341_);
v___x_2344_ = lean_usize_dec_eq(v___x_2342_, v___x_2343_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
lean_dec_ref(v_rhs_2315_);
lean_dec_ref(v_lhs_2314_);
v___x_2345_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2);
v___x_2346_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2345_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
return v___x_2346_;
}
else
{
lean_object* v___x_2347_; 
lean_inc_ref(v_rhs_2315_);
lean_inc_ref(v_lhs_2314_);
v___x_2347_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(v_lhs_2314_, v_rhs_2315_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
lean_dec_ref_known(v___x_2347_, 1);
v___x_2349_ = lean_box(0);
v___x_2350_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_2314_, v_a_2348_, v___x_2349_, v_heqProofs_2333_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2352_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref_known(v___x_2350_, 1);
v___x_2352_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_2315_, v_a_2348_, v_a_2351_, v_heqProofs_2333_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
lean_dec(v_a_2348_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2368_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2368_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2368_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
if (lean_obj_tag(v_a_2353_) == 1)
{
lean_object* v_val_2357_; uint8_t v___y_2362_; 
v_val_2357_ = lean_ctor_get(v_a_2353_, 0);
lean_inc(v_val_2357_);
lean_dec_ref_known(v_a_2353_, 1);
if (v_heqProofs_2333_ == 0)
{
if (v_heq_2316_ == 0)
{
v___y_2362_ = v___x_2344_;
goto v___jp_2361_;
}
else
{
lean_del_object(v___x_2355_);
goto v___jp_2358_;
}
}
else
{
v___y_2362_ = v_heq_2316_;
goto v___jp_2361_;
}
v___jp_2358_:
{
if (v_heq_2316_ == 0)
{
lean_object* v___x_2359_; 
v___x_2359_ = l_Lean_Meta_mkEqOfHEq(v_val_2357_, v_heq_2316_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
return v___x_2359_;
}
else
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Lean_Meta_mkHEqOfEq(v_val_2357_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
return v___x_2360_;
}
}
v___jp_2361_:
{
if (v___y_2362_ == 0)
{
lean_del_object(v___x_2355_);
goto v___jp_2358_;
}
else
{
lean_object* v___x_2364_; 
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v_val_2357_);
v___x_2364_ = v___x_2355_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_val_2357_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
lean_del_object(v___x_2355_);
lean_dec(v_a_2353_);
v___x_2366_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3);
v___x_2367_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2366_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
return v___x_2367_;
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
v_a_2369_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2352_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2352_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec(v_a_2348_);
lean_dec_ref(v_rhs_2315_);
v_a_2377_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2350_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2350_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
else
{
lean_dec_ref(v_rhs_2315_);
lean_dec_ref(v_lhs_2314_);
return v___x_2347_;
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_dec(v_a_2336_);
lean_dec_ref(v_rhs_2315_);
lean_dec_ref(v_lhs_2314_);
v_a_2385_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2338_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2338_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_dec_ref(v_rhs_2315_);
lean_dec_ref(v_lhs_2314_);
v_a_2393_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2335_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2335_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
lean_dec_ref(v_rhs_2315_);
lean_dec_ref(v_lhs_2314_);
v_a_2401_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2331_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2331_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
else
{
lean_object* v___x_2409_; 
lean_dec_ref(v_rhs_2315_);
v___x_2409_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(v_lhs_2314_, v_heq_2316_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
return v___x_2409_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_2314_ = stack[0].m_obj;
lean_object* v_rhs_2315_ = stack[1].m_obj;
uint8_t v_heq_2316_ = stack[2].m_num;
lean_object* v_a_2317_ = stack[3].m_obj;
lean_object* v_a_2318_ = stack[4].m_obj;
lean_object* v_a_2319_ = stack[5].m_obj;
lean_object* v_a_2320_ = stack[6].m_obj;
lean_object* v_a_2321_ = stack[7].m_obj;
lean_object* v_a_2322_ = stack[8].m_obj;
lean_object* v_a_2323_ = stack[9].m_obj;
lean_object* v_a_2324_ = stack[10].m_obj;
lean_object* v_a_2325_ = stack[11].m_obj;
lean_object* v_a_2326_ = stack[12].m_obj;
lean_object* v_res_2410_;
v_res_2410_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_lhs_2314_, v_rhs_2315_, v_heq_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
stack->m_obj
 = v_res_2410_;
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(lean_object* v_thm_2411_, lean_object* v_lhs_2412_, lean_object* v_rhs_2413_, lean_object* v_i_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v___x_2426_; uint8_t v___x_2427_; 
v___x_2426_ = lean_unsigned_to_nat(0u);
v___x_2427_ = lean_nat_dec_lt(v___x_2426_, v_i_2414_);
if (v___x_2427_ == 0)
{
lean_object* v_proof_2428_; lean_object* v___x_2429_; 
v_proof_2428_ = lean_ctor_get(v_thm_2411_, 1);
lean_inc_ref(v_proof_2428_);
v___x_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2429_, 0, v_proof_2428_);
return v___x_2429_;
}
else
{
uint8_t v___x_2430_; lean_object* v___x_2431_; lean_object* v_i_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2430_ = 0;
v___x_2431_ = lean_unsigned_to_nat(1u);
v_i_2432_ = lean_nat_sub(v_i_2414_, v___x_2431_);
v___x_2433_ = l_Lean_Expr_appFn_x21(v_lhs_2412_);
v___x_2434_ = l_Lean_Expr_appFn_x21(v_rhs_2413_);
v___x_2435_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_2411_, v___x_2433_, v___x_2434_, v_i_2432_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
lean_dec_ref(v___x_2434_);
lean_dec_ref(v___x_2433_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v_argKinds_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; uint8_t v___y_2441_; lean_object* v___x_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
v_argKinds_2437_ = lean_ctor_get(v_thm_2411_, 2);
v___x_2438_ = l_Lean_Expr_appArg_x21(v_lhs_2412_);
v___x_2439_ = l_Lean_Expr_appArg_x21(v_rhs_2413_);
v___x_2452_ = lean_box(v___x_2430_);
v___x_2453_ = lean_array_get(v___x_2452_, v_argKinds_2437_, v_i_2432_);
lean_dec(v_i_2432_);
lean_dec(v___x_2452_);
v___x_2454_ = lean_unbox(v___x_2453_);
lean_dec(v___x_2453_);
if (v___x_2454_ == 4)
{
v___y_2441_ = v___x_2427_;
goto v___jp_2440_;
}
else
{
uint8_t v___x_2455_; 
v___x_2455_ = 0;
v___y_2441_ = v___x_2455_;
goto v___jp_2440_;
}
v___jp_2440_:
{
lean_object* v___x_2442_; 
lean_inc_ref(v___x_2439_);
lean_inc_ref(v___x_2438_);
v___x_2442_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___x_2438_, v___x_2439_, v___y_2441_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2451_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; lean_object* v___x_2449_; 
v___x_2447_ = l_Lean_mkApp3(v_a_2436_, v___x_2438_, v___x_2439_, v_a_2443_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2447_);
v___x_2449_ = v___x_2445_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
else
{
lean_dec_ref(v___x_2439_);
lean_dec_ref(v___x_2438_);
lean_dec(v_a_2436_);
return v___x_2442_;
}
}
}
else
{
lean_dec(v_i_2432_);
return v___x_2435_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper_0interp(lean_interpreter_value* stack)
{
lean_object* v_thm_2411_ = stack[0].m_obj;
lean_object* v_lhs_2412_ = stack[1].m_obj;
lean_object* v_rhs_2413_ = stack[2].m_obj;
lean_object* v_i_2414_ = stack[3].m_obj;
lean_object* v_a_2415_ = stack[4].m_obj;
lean_object* v_a_2416_ = stack[5].m_obj;
lean_object* v_a_2417_ = stack[6].m_obj;
lean_object* v_a_2418_ = stack[7].m_obj;
lean_object* v_a_2419_ = stack[8].m_obj;
lean_object* v_a_2420_ = stack[9].m_obj;
lean_object* v_a_2421_ = stack[10].m_obj;
lean_object* v_a_2422_ = stack[11].m_obj;
lean_object* v_a_2423_ = stack[12].m_obj;
lean_object* v_a_2424_ = stack[13].m_obj;
lean_object* v_res_2456_;
v_res_2456_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_2411_, v_lhs_2412_, v_rhs_2413_, v_i_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
stack->m_obj
 = v_res_2456_;
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(lean_object* v_f_2460_, lean_object* v_g_2461_, lean_object* v_numArgs_2462_, lean_object* v_lhs_2463_, lean_object* v_rhs_2464_, uint8_t v_heq_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
lean_object* v___x_2477_; 
lean_inc(v_numArgs_2462_);
lean_inc_ref(v_f_2460_);
v___x_2477_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(v_f_2460_, v_numArgs_2462_, v_a_2469_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v_argKinds_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref_known(v___x_2477_, 1);
v_argKinds_2479_ = lean_ctor_get(v_a_2478_, 2);
v___x_2480_ = lean_array_get_size(v_argKinds_2479_);
v___x_2481_ = lean_nat_dec_eq(v___x_2480_, v_numArgs_2462_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
lean_dec(v_a_2478_);
lean_dec_ref(v_rhs_2464_);
lean_dec_ref(v_lhs_2463_);
lean_dec(v_numArgs_2462_);
lean_dec_ref(v_g_2461_);
lean_dec_ref(v_f_2460_);
v___x_2482_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2);
v___x_2483_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2482_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
return v___x_2483_;
}
else
{
lean_object* v___x_2484_; 
v___x_2484_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_2478_, v_lhs_2463_, v_rhs_2464_, v_numArgs_2462_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
lean_dec(v_a_2478_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_a_2485_; size_t v___x_2486_; size_t v___x_2487_; uint8_t v___x_2488_; 
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
lean_inc(v_a_2485_);
lean_dec_ref_known(v___x_2484_, 1);
v___x_2486_ = lean_ptr_addr(v_f_2460_);
v___x_2487_ = lean_ptr_addr(v_g_2461_);
v___x_2488_ = lean_usize_dec_eq(v___x_2486_, v___x_2487_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___f_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2489_ = lean_box(v___x_2488_);
v___x_2490_ = lean_box(v___x_2481_);
v___f_2491_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___boxed), 17, 5);
lean_closure_set(v___f_2491_, 0, v_numArgs_2462_);
lean_closure_set(v___f_2491_, 1, v_rhs_2464_);
lean_closure_set(v___f_2491_, 2, v_lhs_2463_);
lean_closure_set(v___f_2491_, 3, v___x_2489_);
lean_closure_set(v___f_2491_, 4, v___x_2490_);
v___x_2492_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__4));
v___x_2493_ = l_Lean_Core_mkFreshUserName(v___x_2492_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v___x_2495_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___x_2493_, 1);
lean_inc(v_a_2475_);
lean_inc_ref(v_a_2474_);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
lean_inc_ref(v_f_2460_);
v___x_2495_ = lean_infer_type(v_f_2460_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; lean_object* v___x_2497_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___x_2495_, 1);
v___x_2497_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_a_2494_, v_a_2496_, v___f_2491_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2499_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2497_, 1);
v___x_2499_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_f_2460_, v_g_2461_, v___x_2488_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2501_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2500_);
lean_dec_ref_known(v___x_2499_, 1);
v___x_2501_ = l_Lean_Meta_mkEqNDRec(v_a_2498_, v_a_2485_, v_a_2500_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; lean_object* v___x_2503_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2502_);
lean_dec_ref_known(v___x_2501_, 1);
v___x_2503_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_2502_, v_heq_2465_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
return v___x_2503_;
}
else
{
return v___x_2501_;
}
}
else
{
lean_dec(v_a_2498_);
lean_dec(v_a_2485_);
return v___x_2499_;
}
}
else
{
lean_dec(v_a_2485_);
lean_dec_ref(v_g_2461_);
lean_dec_ref(v_f_2460_);
return v___x_2497_;
}
}
else
{
lean_dec(v_a_2494_);
lean_dec_ref(v___f_2491_);
lean_dec(v_a_2485_);
lean_dec_ref(v_g_2461_);
lean_dec_ref(v_f_2460_);
return v___x_2495_;
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_dec_ref(v___f_2491_);
lean_dec(v_a_2485_);
lean_dec_ref(v_g_2461_);
lean_dec_ref(v_f_2460_);
v_a_2504_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2493_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2493_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
else
{
lean_object* v___x_2512_; 
lean_dec_ref(v_rhs_2464_);
lean_dec_ref(v_lhs_2463_);
lean_dec(v_numArgs_2462_);
lean_dec_ref(v_g_2461_);
lean_dec_ref(v_f_2460_);
v___x_2512_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_2485_, v_heq_2465_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
return v___x_2512_;
}
}
else
{
lean_dec_ref(v_rhs_2464_);
lean_dec_ref(v_lhs_2463_);
lean_dec(v_numArgs_2462_);
lean_dec_ref(v_g_2461_);
lean_dec_ref(v_f_2460_);
return v___x_2484_;
}
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec_ref(v_rhs_2464_);
lean_dec_ref(v_lhs_2463_);
lean_dec(v_numArgs_2462_);
lean_dec_ref(v_g_2461_);
lean_dec_ref(v_f_2460_);
v_a_2513_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2477_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2477_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2460_ = stack[0].m_obj;
lean_object* v_g_2461_ = stack[1].m_obj;
lean_object* v_numArgs_2462_ = stack[2].m_obj;
lean_object* v_lhs_2463_ = stack[3].m_obj;
lean_object* v_rhs_2464_ = stack[4].m_obj;
uint8_t v_heq_2465_ = stack[5].m_num;
lean_object* v_a_2466_ = stack[6].m_obj;
lean_object* v_a_2467_ = stack[7].m_obj;
lean_object* v_a_2468_ = stack[8].m_obj;
lean_object* v_a_2469_ = stack[9].m_obj;
lean_object* v_a_2470_ = stack[10].m_obj;
lean_object* v_a_2471_ = stack[11].m_obj;
lean_object* v_a_2472_ = stack[12].m_obj;
lean_object* v_a_2473_ = stack[13].m_obj;
lean_object* v_a_2474_ = stack[14].m_obj;
lean_object* v_a_2475_ = stack[15].m_obj;
lean_object* v_res_2521_;
v_res_2521_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_2460_, v_g_2461_, v_numArgs_2462_, v_lhs_2463_, v_rhs_2464_, v_heq_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
stack->m_obj
 = v_res_2521_;
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2523_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2524_ = lean_unsigned_to_nat(27u);
v___x_2525_ = lean_unsigned_to_nat(237u);
v___x_2526_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0));
v___x_2527_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2528_ = l_mkPanicMessageWithDecl(v___x_2527_, v___x_2526_, v___x_2525_, v___x_2524_, v___x_2523_);
return v___x_2528_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2(void){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2529_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2530_ = lean_unsigned_to_nat(27u);
v___x_2531_ = lean_unsigned_to_nat(236u);
v___x_2532_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0));
v___x_2533_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2534_ = l_mkPanicMessageWithDecl(v___x_2533_, v___x_2532_, v___x_2531_, v___x_2530_, v___x_2529_);
return v___x_2534_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(lean_object* v_lhs_2535_, lean_object* v_rhs_2536_, uint8_t v_heq_2537_, lean_object* v_e_u2081_2538_, lean_object* v_e_u2082_2539_, lean_object* v_numArgs_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_){
_start:
{
if (lean_obj_tag(v_e_u2081_2538_) == 5)
{
if (lean_obj_tag(v_e_u2082_2539_) == 5)
{
lean_object* v_fn_2552_; lean_object* v_fn_2553_; lean_object* v___x_2554_; lean_object* v_numArgs_2555_; size_t v___x_2556_; size_t v___x_2557_; uint8_t v___x_2558_; 
v_fn_2552_ = lean_ctor_get(v_e_u2081_2538_, 0);
lean_inc_ref(v_fn_2552_);
lean_dec_ref_known(v_e_u2081_2538_, 2);
v_fn_2553_ = lean_ctor_get(v_e_u2082_2539_, 0);
lean_inc_ref(v_fn_2553_);
lean_dec_ref_known(v_e_u2082_2539_, 2);
v___x_2554_ = lean_unsigned_to_nat(1u);
v_numArgs_2555_ = lean_nat_add(v_numArgs_2540_, v___x_2554_);
lean_dec(v_numArgs_2540_);
v___x_2556_ = lean_ptr_addr(v_fn_2552_);
v___x_2557_ = lean_ptr_addr(v_fn_2553_);
v___x_2558_ = lean_usize_dec_eq(v___x_2556_, v___x_2557_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2559_; 
lean_inc_ref(v_fn_2553_);
lean_inc_ref(v_fn_2552_);
v___x_2559_ = l_Lean_Meta_Grind_hasSameType(v_fn_2552_, v_fn_2553_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; uint8_t v___x_2561_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2560_);
lean_dec_ref_known(v___x_2559_, 1);
v___x_2561_ = lean_unbox(v_a_2560_);
lean_dec(v_a_2560_);
if (v___x_2561_ == 0)
{
v_e_u2081_2538_ = v_fn_2552_;
v_e_u2082_2539_ = v_fn_2553_;
v_numArgs_2540_ = v_numArgs_2555_;
goto _start;
}
else
{
lean_object* v___x_2563_; 
v___x_2563_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_2552_, v_fn_2553_, v_numArgs_2555_, v_lhs_2535_, v_rhs_2536_, v_heq_2537_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
return v___x_2563_;
}
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_dec(v_numArgs_2555_);
lean_dec_ref(v_fn_2553_);
lean_dec_ref(v_fn_2552_);
lean_dec_ref(v_rhs_2536_);
lean_dec_ref(v_lhs_2535_);
v_a_2564_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2559_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2559_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
else
{
lean_object* v___x_2572_; 
v___x_2572_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_2552_, v_fn_2553_, v_numArgs_2555_, v_lhs_2535_, v_rhs_2536_, v_heq_2537_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
return v___x_2572_;
}
}
else
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
lean_dec_ref_known(v_e_u2081_2538_, 2);
lean_dec(v_numArgs_2540_);
lean_dec_ref(v_e_u2082_2539_);
lean_dec_ref(v_rhs_2536_);
lean_dec_ref(v_lhs_2535_);
v___x_2573_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1);
v___x_2574_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2573_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
return v___x_2574_;
}
}
else
{
lean_object* v___x_2575_; lean_object* v___x_2576_; 
lean_dec(v_numArgs_2540_);
lean_dec_ref(v_e_u2082_2539_);
lean_dec_ref(v_e_u2081_2538_);
lean_dec_ref(v_rhs_2536_);
lean_dec_ref(v_lhs_2535_);
v___x_2575_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2);
v___x_2576_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2575_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
return v___x_2576_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_2535_ = stack[0].m_obj;
lean_object* v_rhs_2536_ = stack[1].m_obj;
uint8_t v_heq_2537_ = stack[2].m_num;
lean_object* v_e_u2081_2538_ = stack[3].m_obj;
lean_object* v_e_u2082_2539_ = stack[4].m_obj;
lean_object* v_numArgs_2540_ = stack[5].m_obj;
lean_object* v_a_2541_ = stack[6].m_obj;
lean_object* v_a_2542_ = stack[7].m_obj;
lean_object* v_a_2543_ = stack[8].m_obj;
lean_object* v_a_2544_ = stack[9].m_obj;
lean_object* v_a_2545_ = stack[10].m_obj;
lean_object* v_a_2546_ = stack[11].m_obj;
lean_object* v_a_2547_ = stack[12].m_obj;
lean_object* v_a_2548_ = stack[13].m_obj;
lean_object* v_a_2549_ = stack[14].m_obj;
lean_object* v_a_2550_ = stack[15].m_obj;
lean_object* v_res_2577_;
v_res_2577_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(v_lhs_2535_, v_rhs_2536_, v_heq_2537_, v_e_u2081_2538_, v_e_u2082_2539_, v_numArgs_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
stack->m_obj
 = v_res_2577_;
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(lean_object* v_lhs_2578_, lean_object* v_rhs_2579_, uint8_t v_heq_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2592_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_rhs_2579_);
lean_inc_ref(v_lhs_2578_);
v___x_2593_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(v_lhs_2578_, v_rhs_2579_, v_heq_2580_, v_lhs_2578_, v_rhs_2579_, v___x_2592_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_);
return v___x_2593_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_2578_ = stack[0].m_obj;
lean_object* v_rhs_2579_ = stack[1].m_obj;
uint8_t v_heq_2580_ = stack[2].m_num;
lean_object* v_a_2581_ = stack[3].m_obj;
lean_object* v_a_2582_ = stack[4].m_obj;
lean_object* v_a_2583_ = stack[5].m_obj;
lean_object* v_a_2584_ = stack[6].m_obj;
lean_object* v_a_2585_ = stack[7].m_obj;
lean_object* v_a_2586_ = stack[8].m_obj;
lean_object* v_a_2587_ = stack[9].m_obj;
lean_object* v_a_2588_ = stack[10].m_obj;
lean_object* v_a_2589_ = stack[11].m_obj;
lean_object* v_a_2590_ = stack[12].m_obj;
lean_object* v_res_2594_;
v_res_2594_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_2578_, v_rhs_2579_, v_heq_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_);
stack->m_obj
 = v_res_2594_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC___boxed(lean_object* v_lhs_2595_, lean_object* v_rhs_2596_, lean_object* v_heq_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_){
_start:
{
uint8_t v_heq_boxed_2609_; lean_object* v_res_2610_; 
v_heq_boxed_2609_ = lean_unbox(v_heq_2597_);
v_res_2610_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_2595_, v_rhs_2596_, v_heq_boxed_2609_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
lean_dec(v_a_2599_);
lean_dec(v_a_2598_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___boxed(lean_object* v_lhs_2611_, lean_object* v_rhs_2612_, lean_object* v_heq_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_){
_start:
{
uint8_t v_heq_boxed_2625_; lean_object* v_res_2626_; 
v_heq_boxed_2625_ = lean_unbox(v_heq_2613_);
v_res_2626_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_2611_, v_rhs_2612_, v_heq_boxed_2625_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_);
lean_dec(v_a_2623_);
lean_dec_ref(v_a_2622_);
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec(v_a_2619_);
lean_dec_ref(v_a_2618_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec(v_a_2615_);
lean_dec(v_a_2614_);
lean_dec_ref(v_rhs_2612_);
lean_dec_ref(v_lhs_2611_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___boxed(lean_object* v_lhs_2627_, lean_object* v_rhs_2628_, lean_object* v_heq_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
uint8_t v_heq_boxed_2641_; lean_object* v_res_2642_; 
v_heq_boxed_2641_ = lean_unbox(v_heq_2629_);
v_res_2642_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_2627_, v_rhs_2628_, v_heq_boxed_2641_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_);
lean_dec(v_a_2639_);
lean_dec_ref(v_a_2638_);
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_a_2635_);
lean_dec_ref(v_a_2634_);
lean_dec(v_a_2633_);
lean_dec_ref(v_a_2632_);
lean_dec(v_a_2631_);
lean_dec(v_a_2630_);
lean_dec_ref(v_rhs_2628_);
lean_dec_ref(v_lhs_2627_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof___boxed(lean_object* v_lhs_2643_, lean_object* v_rhs_2644_, lean_object* v_h_2645_, lean_object* v_flipped_2646_, lean_object* v_heq_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
uint8_t v_flipped_boxed_2659_; uint8_t v_heq_boxed_2660_; lean_object* v_res_2661_; 
v_flipped_boxed_2659_ = lean_unbox(v_flipped_2646_);
v_heq_boxed_2660_ = lean_unbox(v_heq_2647_);
v_res_2661_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_lhs_2643_, v_rhs_2644_, v_h_2645_, v_flipped_boxed_2659_, v_heq_boxed_2660_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
lean_dec(v_a_2651_);
lean_dec_ref(v_a_2650_);
lean_dec(v_a_2649_);
lean_dec(v_a_2648_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___boxed(lean_object* v_lhs_2662_, lean_object* v_rhs_2663_, lean_object* v_heq_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
uint8_t v_heq_boxed_2676_; lean_object* v_res_2677_; 
v_heq_boxed_2676_ = lean_unbox(v_heq_2664_);
v_res_2677_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_2662_, v_rhs_2663_, v_heq_boxed_2676_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
lean_dec(v_a_2674_);
lean_dec_ref(v_a_2673_);
lean_dec(v_a_2672_);
lean_dec_ref(v_a_2671_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_rhs_2663_);
lean_dec_ref(v_lhs_2662_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper___boxed(lean_object* v_thm_2678_, lean_object* v_lhs_2679_, lean_object* v_rhs_2680_, lean_object* v_i_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_2678_, v_lhs_2679_, v_rhs_2680_, v_i_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec(v_a_2682_);
lean_dec(v_i_2681_);
lean_dec_ref(v_rhs_2680_);
lean_dec_ref(v_lhs_2679_);
lean_dec_ref(v_thm_2678_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___boxed(lean_object** _args){
lean_object* v_lhs_2694_ = _args[0];
lean_object* v_rhs_2695_ = _args[1];
lean_object* v_heq_2696_ = _args[2];
lean_object* v_e_u2081_2697_ = _args[3];
lean_object* v_e_u2082_2698_ = _args[4];
lean_object* v_numArgs_2699_ = _args[5];
lean_object* v_a_2700_ = _args[6];
lean_object* v_a_2701_ = _args[7];
lean_object* v_a_2702_ = _args[8];
lean_object* v_a_2703_ = _args[9];
lean_object* v_a_2704_ = _args[10];
lean_object* v_a_2705_ = _args[11];
lean_object* v_a_2706_ = _args[12];
lean_object* v_a_2707_ = _args[13];
lean_object* v_a_2708_ = _args[14];
lean_object* v_a_2709_ = _args[15];
lean_object* v_a_2710_ = _args[16];
_start:
{
uint8_t v_heq_boxed_2711_; lean_object* v_res_2712_; 
v_heq_boxed_2711_ = lean_unbox(v_heq_2696_);
v_res_2712_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(v_lhs_2694_, v_rhs_2695_, v_heq_boxed_2711_, v_e_u2081_2697_, v_e_u2082_2698_, v_numArgs_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
lean_dec(v_a_2707_);
lean_dec_ref(v_a_2706_);
lean_dec(v_a_2705_);
lean_dec_ref(v_a_2704_);
lean_dec(v_a_2703_);
lean_dec_ref(v_a_2702_);
lean_dec(v_a_2701_);
lean_dec(v_a_2700_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___boxed(lean_object* v_lhs_2713_, lean_object* v_common_2714_, lean_object* v_acc_2715_, lean_object* v_heq_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_){
_start:
{
uint8_t v_heq_boxed_2728_; lean_object* v_res_2729_; 
v_heq_boxed_2728_ = lean_unbox(v_heq_2716_);
v_res_2729_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_2713_, v_common_2714_, v_acc_2715_, v_heq_boxed_2728_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
lean_dec(v_a_2726_);
lean_dec_ref(v_a_2725_);
lean_dec(v_a_2724_);
lean_dec_ref(v_a_2723_);
lean_dec(v_a_2722_);
lean_dec_ref(v_a_2721_);
lean_dec(v_a_2720_);
lean_dec_ref(v_a_2719_);
lean_dec(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_common_2714_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___boxed(lean_object** _args){
lean_object* v_f_2730_ = _args[0];
lean_object* v_g_2731_ = _args[1];
lean_object* v_numArgs_2732_ = _args[2];
lean_object* v_lhs_2733_ = _args[3];
lean_object* v_rhs_2734_ = _args[4];
lean_object* v_heq_2735_ = _args[5];
lean_object* v_a_2736_ = _args[6];
lean_object* v_a_2737_ = _args[7];
lean_object* v_a_2738_ = _args[8];
lean_object* v_a_2739_ = _args[9];
lean_object* v_a_2740_ = _args[10];
lean_object* v_a_2741_ = _args[11];
lean_object* v_a_2742_ = _args[12];
lean_object* v_a_2743_ = _args[13];
lean_object* v_a_2744_ = _args[14];
lean_object* v_a_2745_ = _args[15];
lean_object* v_a_2746_ = _args[16];
_start:
{
uint8_t v_heq_boxed_2747_; lean_object* v_res_2748_; 
v_heq_boxed_2747_ = lean_unbox(v_heq_2735_);
v_res_2748_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_2730_, v_g_2731_, v_numArgs_2732_, v_lhs_2733_, v_rhs_2734_, v_heq_boxed_2747_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_);
lean_dec(v_a_2745_);
lean_dec_ref(v_a_2744_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
lean_dec(v_a_2741_);
lean_dec_ref(v_a_2740_);
lean_dec(v_a_2739_);
lean_dec_ref(v_a_2738_);
lean_dec(v_a_2737_);
lean_dec(v_a_2736_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___boxed(lean_object* v_rhs_2749_, lean_object* v_common_2750_, lean_object* v_lhsEqCommon_x3f_2751_, lean_object* v_heq_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_){
_start:
{
uint8_t v_heq_boxed_2764_; lean_object* v_res_2765_; 
v_heq_boxed_2764_ = lean_unbox(v_heq_2752_);
v_res_2765_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_2749_, v_common_2750_, v_lhsEqCommon_x3f_2751_, v_heq_boxed_2764_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2761_);
lean_dec(v_a_2760_);
lean_dec_ref(v_a_2759_);
lean_dec(v_a_2758_);
lean_dec_ref(v_a_2757_);
lean_dec(v_a_2756_);
lean_dec_ref(v_a_2755_);
lean_dec(v_a_2754_);
lean_dec(v_a_2753_);
lean_dec_ref(v_common_2750_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___boxed(lean_object* v_lhs_2766_, lean_object* v_rhs_2767_, lean_object* v_heq_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
uint8_t v_heq_boxed_2780_; lean_object* v_res_2781_; 
v_heq_boxed_2780_ = lean_unbox(v_heq_2768_);
v_res_2781_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_2766_, v_rhs_2767_, v_heq_boxed_2780_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
lean_dec(v_a_2778_);
lean_dec_ref(v_a_2777_);
lean_dec(v_a_2776_);
lean_dec_ref(v_a_2775_);
lean_dec(v_a_2774_);
lean_dec_ref(v_a_2773_);
lean_dec(v_a_2772_);
lean_dec_ref(v_a_2771_);
lean_dec(v_a_2770_);
lean_dec(v_a_2769_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop___boxed(lean_object* v_lhs_2782_, lean_object* v_rhs_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_2782_, v_rhs_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
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
lean_dec_ref(v_rhs_2783_);
lean_dec_ref(v_lhs_2782_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___boxed(lean_object* v_lhs_2796_, lean_object* v_rhs_2797_, lean_object* v_heq_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_){
_start:
{
uint8_t v_heq_boxed_2810_; lean_object* v_res_2811_; 
v_heq_boxed_2810_ = lean_unbox(v_heq_2798_);
v_res_2811_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_lhs_2796_, v_rhs_2797_, v_heq_boxed_2810_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrProof___boxed(lean_object* v_lhs_2812_, lean_object* v_rhs_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_Meta_Grind_mkEqCongrProof(v_lhs_2812_, v_rhs_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
lean_dec(v_a_2823_);
lean_dec_ref(v_a_2822_);
lean_dec(v_a_2821_);
lean_dec_ref(v_a_2820_);
lean_dec(v_a_2819_);
lean_dec_ref(v_a_2818_);
lean_dec(v_a_2817_);
lean_dec_ref(v_a_2816_);
lean_dec(v_a_2815_);
lean_dec(v_a_2814_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___boxed(lean_object* v_lhs_2826_, lean_object* v_rhs_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(v_lhs_2826_, v_rhs_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
lean_dec(v_a_2829_);
lean_dec(v_a_2828_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___boxed(lean_object* v_lhs_2840_, lean_object* v_rhs_2841_, lean_object* v_heq_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_){
_start:
{
uint8_t v_heq_boxed_2854_; lean_object* v_res_2855_; 
v_heq_boxed_2854_ = lean_unbox(v_heq_2842_);
v_res_2855_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(v_lhs_2840_, v_rhs_2841_, v_heq_boxed_2854_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
lean_dec(v_a_2852_);
lean_dec_ref(v_a_2851_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
lean_dec(v_a_2846_);
lean_dec_ref(v_a_2845_);
lean_dec(v_a_2844_);
lean_dec(v_a_2843_);
return v_res_2855_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(lean_object* v_00_u03b1_2856_, lean_object* v_ref_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v___x_2869_; 
v___x_2869_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_2857_);
return v___x_2869_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2857_ = stack[1].m_obj;
lean_object* v___y_2858_ = stack[2].m_obj;
lean_object* v___y_2859_ = stack[3].m_obj;
lean_object* v___y_2860_ = stack[4].m_obj;
lean_object* v___y_2861_ = stack[5].m_obj;
lean_object* v___y_2862_ = stack[6].m_obj;
lean_object* v___y_2863_ = stack[7].m_obj;
lean_object* v___y_2864_ = stack[8].m_obj;
lean_object* v___y_2865_ = stack[9].m_obj;
lean_object* v___y_2866_ = stack[10].m_obj;
lean_object* v___y_2867_ = stack[11].m_obj;
lean_object* v_res_2870_;
v_res_2870_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(lean_box(0), v_ref_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
stack->m_obj
 = v_res_2870_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___boxed(lean_object* v_00_u03b1_2871_, lean_object* v_ref_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(v_00_u03b1_2871_, v_ref_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
return v_res_2884_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(lean_object* v_00_u03b1_2885_, lean_object* v_name_2886_, uint8_t v_bi_2887_, lean_object* v_type_2888_, lean_object* v_k_2889_, uint8_t v_kind_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_2886_, v_bi_2887_, v_type_2888_, v_k_2889_, v_kind_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
return v___x_2902_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2886_ = stack[1].m_obj;
uint8_t v_bi_2887_ = stack[2].m_num;
lean_object* v_type_2888_ = stack[3].m_obj;
lean_object* v_k_2889_ = stack[4].m_obj;
uint8_t v_kind_2890_ = stack[5].m_num;
lean_object* v___y_2891_ = stack[6].m_obj;
lean_object* v___y_2892_ = stack[7].m_obj;
lean_object* v___y_2893_ = stack[8].m_obj;
lean_object* v___y_2894_ = stack[9].m_obj;
lean_object* v___y_2895_ = stack[10].m_obj;
lean_object* v___y_2896_ = stack[11].m_obj;
lean_object* v___y_2897_ = stack[12].m_obj;
lean_object* v___y_2898_ = stack[13].m_obj;
lean_object* v___y_2899_ = stack[14].m_obj;
lean_object* v___y_2900_ = stack[15].m_obj;
lean_object* v_res_2903_;
v_res_2903_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(lean_box(0), v_name_2886_, v_bi_2887_, v_type_2888_, v_k_2889_, v_kind_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
stack->m_obj
 = v_res_2903_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___boxed(lean_object** _args){
lean_object* v_00_u03b1_2904_ = _args[0];
lean_object* v_name_2905_ = _args[1];
lean_object* v_bi_2906_ = _args[2];
lean_object* v_type_2907_ = _args[3];
lean_object* v_k_2908_ = _args[4];
lean_object* v_kind_2909_ = _args[5];
lean_object* v___y_2910_ = _args[6];
lean_object* v___y_2911_ = _args[7];
lean_object* v___y_2912_ = _args[8];
lean_object* v___y_2913_ = _args[9];
lean_object* v___y_2914_ = _args[10];
lean_object* v___y_2915_ = _args[11];
lean_object* v___y_2916_ = _args[12];
lean_object* v___y_2917_ = _args[13];
lean_object* v___y_2918_ = _args[14];
lean_object* v___y_2919_ = _args[15];
lean_object* v___y_2920_ = _args[16];
_start:
{
uint8_t v_bi_boxed_2921_; uint8_t v_kind_boxed_2922_; lean_object* v_res_2923_; 
v_bi_boxed_2921_ = lean_unbox(v_bi_2906_);
v_kind_boxed_2922_ = lean_unbox(v_kind_2909_);
v_res_2923_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(v_00_u03b1_2904_, v_name_2905_, v_bi_boxed_2921_, v_type_2907_, v_k_2908_, v_kind_boxed_2922_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec(v___y_2910_);
return v_res_2923_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(lean_object* v_00_u03b1_2924_, lean_object* v_name_2925_, lean_object* v_type_2926_, lean_object* v_k_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_name_2925_, v_type_2926_, v_k_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
return v___x_2939_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2925_ = stack[1].m_obj;
lean_object* v_type_2926_ = stack[2].m_obj;
lean_object* v_k_2927_ = stack[3].m_obj;
lean_object* v___y_2928_ = stack[4].m_obj;
lean_object* v___y_2929_ = stack[5].m_obj;
lean_object* v___y_2930_ = stack[6].m_obj;
lean_object* v___y_2931_ = stack[7].m_obj;
lean_object* v___y_2932_ = stack[8].m_obj;
lean_object* v___y_2933_ = stack[9].m_obj;
lean_object* v___y_2934_ = stack[10].m_obj;
lean_object* v___y_2935_ = stack[11].m_obj;
lean_object* v___y_2936_ = stack[12].m_obj;
lean_object* v___y_2937_ = stack[13].m_obj;
lean_object* v_res_2940_;
v_res_2940_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(lean_box(0), v_name_2925_, v_type_2926_, v_k_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
stack->m_obj
 = v_res_2940_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___boxed(lean_object* v_00_u03b1_2941_, lean_object* v_name_2942_, lean_object* v_type_2943_, lean_object* v_k_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(v_00_u03b1_2941_, v_name_2942_, v_type_2943_, v_k_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2945_);
return v_res_2956_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(lean_object* v_00_u03b1_2957_, lean_object* v_msg_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v_msg_2958_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
return v___x_2970_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2958_ = stack[1].m_obj;
lean_object* v___y_2959_ = stack[2].m_obj;
lean_object* v___y_2960_ = stack[3].m_obj;
lean_object* v___y_2961_ = stack[4].m_obj;
lean_object* v___y_2962_ = stack[5].m_obj;
lean_object* v___y_2963_ = stack[6].m_obj;
lean_object* v___y_2964_ = stack[7].m_obj;
lean_object* v___y_2965_ = stack[8].m_obj;
lean_object* v___y_2966_ = stack[9].m_obj;
lean_object* v___y_2967_ = stack[10].m_obj;
lean_object* v___y_2968_ = stack[11].m_obj;
lean_object* v_res_2971_;
v_res_2971_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(lean_box(0), v_msg_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
stack->m_obj
 = v_res_2971_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___boxed(lean_object* v_00_u03b1_2972_, lean_object* v_msg_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
lean_object* v_res_2985_; 
v_res_2985_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(v_00_u03b1_2972_, v_msg_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec(v___y_2974_);
return v_res_2985_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__1(void){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__0));
v___x_2988_ = l_Lean_stringToMessageData(v___x_2987_);
return v___x_2988_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__3(void){
_start:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__2));
v___x_2991_ = l_Lean_stringToMessageData(v___x_2990_);
return v___x_2991_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__5(void){
_start:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__4));
v___x_2994_ = l_Lean_stringToMessageData(v___x_2993_);
return v___x_2994_;
}
}
lean_object* lean_grind_mk_eq_proof(lean_object* v_a_2995_, lean_object* v_b_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_){
_start:
{
lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___x_3021_; 
lean_inc_ref(v_b_2996_);
lean_inc_ref(v_a_2995_);
v___x_3021_ = l_Lean_Meta_Grind_hasSameType(v_a_2995_, v_b_2996_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; uint8_t v___x_3023_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref_known(v___x_3021_, 1);
v___x_3023_ = lean_unbox(v_a_3022_);
lean_dec(v_a_3022_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; 
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec(v_a_3000_);
lean_dec_ref(v_a_2999_);
lean_dec(v_a_2998_);
lean_dec(v_a_2997_);
lean_inc(v_a_3006_);
lean_inc_ref(v_a_3005_);
lean_inc(v_a_3004_);
lean_inc_ref(v_a_3003_);
lean_inc_ref(v_a_2995_);
v___x_3024_ = lean_infer_type(v_a_2995_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3026_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
lean_inc(v_a_3006_);
lean_inc_ref(v_a_3005_);
lean_inc(v_a_3004_);
lean_inc_ref(v_a_3003_);
lean_inc_ref(v_b_2996_);
v___x_3026_ = lean_infer_type(v_b_2996_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v_a_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_a_3027_);
lean_dec_ref_known(v___x_3026_, 1);
v___x_3028_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__1, &l_Lean_Meta_Grind_mkEqProofImpl___closed__1_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__1);
v___x_3029_ = l_Lean_indentExpr(v_a_2995_);
v___x_3030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3028_);
lean_ctor_set(v___x_3030_, 1, v___x_3029_);
v___x_3031_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__3, &l_Lean_Meta_Grind_mkEqProofImpl___closed__3_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__3);
v___x_3032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3030_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = l_Lean_indentExpr(v_a_3025_);
v___x_3034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3032_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
v___x_3035_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__5, &l_Lean_Meta_Grind_mkEqProofImpl___closed__5_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__5);
v___x_3036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3034_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
v___x_3037_ = l_Lean_indentExpr(v_b_2996_);
v___x_3038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3036_);
lean_ctor_set(v___x_3038_, 1, v___x_3037_);
v___x_3039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
lean_ctor_set(v___x_3039_, 1, v___x_3031_);
v___x_3040_ = l_Lean_indentExpr(v_a_3027_);
v___x_3041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3039_);
lean_ctor_set(v___x_3041_, 1, v___x_3040_);
v___x_3042_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v___x_3041_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_);
lean_dec(v_a_3006_);
lean_dec_ref(v_a_3005_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3042_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3042_);
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
else
{
lean_dec(v_a_3025_);
lean_dec(v_a_3006_);
lean_dec_ref(v_a_3005_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec_ref(v_b_2996_);
lean_dec_ref(v_a_2995_);
return v___x_3026_;
}
}
else
{
lean_dec(v_a_3006_);
lean_dec_ref(v_a_3005_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec_ref(v_b_2996_);
lean_dec_ref(v_a_2995_);
return v___x_3024_;
}
}
else
{
v___y_3009_ = v_a_2997_;
v___y_3010_ = v_a_2998_;
v___y_3011_ = v_a_2999_;
v___y_3012_ = v_a_3000_;
v___y_3013_ = v_a_3001_;
v___y_3014_ = v_a_3002_;
v___y_3015_ = v_a_3003_;
v___y_3016_ = v_a_3004_;
v___y_3017_ = v_a_3005_;
v___y_3018_ = v_a_3006_;
goto v___jp_3008_;
}
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
lean_dec(v_a_3006_);
lean_dec_ref(v_a_3005_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec(v_a_3000_);
lean_dec_ref(v_a_2999_);
lean_dec(v_a_2998_);
lean_dec(v_a_2997_);
lean_dec_ref(v_b_2996_);
lean_dec_ref(v_a_2995_);
v_a_3051_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3021_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3021_);
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
v___jp_3008_:
{
uint8_t v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = 0;
v___x_3020_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_2995_, v_b_2996_, v___x_3019_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec(v___y_3009_);
return v___x_3020_;
}
}
}
LEAN_EXPORT void lean_grind_mk_eq_proof_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2995_ = stack[0].m_obj;
lean_object* v_b_2996_ = stack[1].m_obj;
lean_object* v_a_2997_ = stack[2].m_obj;
lean_object* v_a_2998_ = stack[3].m_obj;
lean_object* v_a_2999_ = stack[4].m_obj;
lean_object* v_a_3000_ = stack[5].m_obj;
lean_object* v_a_3001_ = stack[6].m_obj;
lean_object* v_a_3002_ = stack[7].m_obj;
lean_object* v_a_3003_ = stack[8].m_obj;
lean_object* v_a_3004_ = stack[9].m_obj;
lean_object* v_a_3005_ = stack[10].m_obj;
lean_object* v_a_3006_ = stack[11].m_obj;
lean_object* v_res_3059_;
v_res_3059_ = lean_grind_mk_eq_proof(v_a_2995_, v_b_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_);
stack->m_obj
 = v_res_3059_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqProofImpl___boxed(lean_object* v_a_3060_, lean_object* v_b_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = lean_grind_mk_eq_proof(v_a_3060_, v_b_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
return v_res_3073_;
}
}
lean_object* lean_grind_mk_heq_proof(lean_object* v_a_3074_, lean_object* v_b_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_){
_start:
{
uint8_t v___x_3087_; lean_object* v___x_3088_; 
v___x_3087_ = 1;
v___x_3088_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_3074_, v_b_3075_, v___x_3087_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_);
lean_dec(v_a_3085_);
lean_dec_ref(v_a_3084_);
lean_dec(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
lean_dec(v_a_3079_);
lean_dec_ref(v_a_3078_);
lean_dec(v_a_3077_);
lean_dec(v_a_3076_);
return v___x_3088_;
}
}
LEAN_EXPORT void lean_grind_mk_heq_proof_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3074_ = stack[0].m_obj;
lean_object* v_b_3075_ = stack[1].m_obj;
lean_object* v_a_3076_ = stack[2].m_obj;
lean_object* v_a_3077_ = stack[3].m_obj;
lean_object* v_a_3078_ = stack[4].m_obj;
lean_object* v_a_3079_ = stack[5].m_obj;
lean_object* v_a_3080_ = stack[6].m_obj;
lean_object* v_a_3081_ = stack[7].m_obj;
lean_object* v_a_3082_ = stack[8].m_obj;
lean_object* v_a_3083_ = stack[9].m_obj;
lean_object* v_a_3084_ = stack[10].m_obj;
lean_object* v_a_3085_ = stack[11].m_obj;
lean_object* v_res_3089_;
v_res_3089_ = lean_grind_mk_heq_proof(v_a_3074_, v_b_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_);
stack->m_obj
 = v_res_3089_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHEqProofImpl___boxed(lean_object* v_a_3090_, lean_object* v_b_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = lean_grind_mk_heq_proof(v_a_3090_, v_b_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_);
return v_res_3103_;
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
