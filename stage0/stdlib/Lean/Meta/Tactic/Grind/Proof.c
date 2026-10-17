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
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Goal_hasSameRoot(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v_k_378_ = lean_ctor_get(v_impl_374_, 1);
v_v_379_ = lean_ctor_get(v_impl_374_, 2);
v_l_380_ = lean_ctor_get(v_impl_374_, 3);
lean_inc(v_l_380_);
v_r_381_ = lean_ctor_get(v_impl_374_, 4);
v___x_382_ = lean_unsigned_to_nat(3u);
v___x_383_ = lean_nat_mul(v___x_382_, v_size_376_);
v___x_384_ = lean_nat_dec_lt(v___x_383_, v_size_377_);
lean_dec(v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
lean_dec(v_l_380_);
v___x_385_ = lean_nat_add(v___x_375_, v_size_376_);
v___x_386_ = lean_nat_add(v___x_385_, v_size_377_);
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
lean_inc(v_r_381_);
lean_inc(v_v_379_);
lean_inc(v_k_378_);
lean_inc(v_size_377_);
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
v___x_411_ = lean_nat_add(v___y_408_, v___y_410_);
lean_dec(v___y_410_);
lean_dec(v___y_408_);
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
lean_ctor_set(v___x_391_, 3, v___y_409_);
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
lean_ctor_set(v_reuseFailAlloc_416_, 3, v___y_409_);
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
v___y_408_ = v___x_423_;
v___y_409_ = v___x_422_;
v___y_410_ = v_size_424_;
goto v___jp_407_;
}
else
{
lean_object* v___x_425_; 
v___x_425_ = lean_unsigned_to_nat(0u);
v___y_408_ = v___x_423_;
v___y_409_ = v___x_422_;
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
v_k_516_ = lean_ctor_get(v_impl_512_, 1);
v_v_517_ = lean_ctor_get(v_impl_512_, 2);
v_l_518_ = lean_ctor_get(v_impl_512_, 3);
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
v___x_523_ = lean_nat_add(v___x_513_, v_size_515_);
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
lean_inc(v_l_518_);
lean_inc(v_v_517_);
lean_inc(v_k_516_);
lean_inc(v_size_515_);
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
if (lean_obj_tag(v_l_599_) == 0)
{
lean_object* v_r_600_; lean_object* v_k_601_; lean_object* v_v_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_613_; 
lean_inc_ref(v_l_599_);
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
lean_inc(v_l_599_);
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
lean_object* v___x_978_; lean_object* v___x_95924__overap_979_; lean_object* v___x_980_; 
v___x_978_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0);
v___x_95924__overap_979_ = lean_panic_fn_borrowed(v___x_978_, v_msg_966_);
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
v___x_980_ = lean_apply_11(v___x_95924__overap_979_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, lean_box(0));
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
uint8_t v___x_103658__boxed_1166_; uint8_t v___x_103659__boxed_1167_; lean_object* v_res_1168_; 
v___x_103658__boxed_1166_ = lean_unbox(v___x_1152_);
v___x_103659__boxed_1167_ = lean_unbox(v___x_1153_);
v_res_1168_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0(v_numArgs_1149_, v_rhs_1150_, v_lhs_1151_, v___x_103658__boxed_1166_, v___x_103659__boxed_1167_, v_x_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
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
lean_object* v___x_1178_; lean_object* v_env_1179_; uint8_t v___x_1180_; lean_object* v_env_1181_; lean_object* v___x_1182_; lean_object* v_toCold_1183_; lean_object* v_mctx_1184_; lean_object* v_lctx_1185_; lean_object* v_options_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1178_ = lean_st_ref_get(v___y_1176_);
v_env_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc_ref(v_env_1179_);
lean_dec(v___x_1178_);
v___x_1180_ = 0;
v_env_1181_ = l_Lean_Environment_setRecordingDeps(v_env_1179_, v___x_1180_);
v___x_1182_ = lean_st_ref_get(v___y_1174_);
v_toCold_1183_ = lean_ctor_get(v___y_1175_, 0);
v_mctx_1184_ = lean_ctor_get(v___x_1182_, 0);
lean_inc_ref(v_mctx_1184_);
lean_dec(v___x_1182_);
v_lctx_1185_ = lean_ctor_get(v___y_1173_, 2);
v_options_1186_ = lean_ctor_get(v_toCold_1183_, 2);
lean_inc_ref(v_options_1186_);
lean_inc_ref(v_lctx_1185_);
v___x_1187_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1187_, 0, v_env_1181_);
lean_ctor_set(v___x_1187_, 1, v_mctx_1184_);
lean_ctor_set(v___x_1187_, 2, v_lctx_1185_);
lean_ctor_set(v___x_1187_, 3, v_options_1186_);
v___x_1188_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
lean_ctor_set(v___x_1188_, 1, v_msgData_1172_);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16___boxed(lean_object* v_msgData_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(v_msgData_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(lean_object* v_msg_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_ref_1203_; lean_object* v___x_1204_; lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1213_; 
v_ref_1203_ = lean_ctor_get(v___y_1200_, 2);
v___x_1204_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(v_msg_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1207_ = v___x_1204_;
v_isShared_1208_ = v_isSharedCheck_1213_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1204_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1213_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; lean_object* v___x_1211_; 
lean_inc(v_ref_1203_);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v_ref_1203_);
lean_ctor_set(v___x_1209_, 1, v_a_1205_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set_tag(v___x_1207_, 1);
lean_ctor_set(v___x_1207_, 0, v___x_1209_);
v___x_1211_ = v___x_1207_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg___boxed(lean_object* v_msg_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v_msg_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
return v_res_1220_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__0));
v___x_1223_ = l_Lean_stringToMessageData(v___x_1222_);
return v___x_1223_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__2));
v___x_1226_ = l_Lean_stringToMessageData(v___x_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(lean_object* v_lhs_1227_, lean_object* v_rhs_1228_, lean_object* v_00_u03b1_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1241_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1);
v___x_1242_ = l_Lean_indentExpr(v_lhs_1227_);
v___x_1243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1241_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3);
v___x_1245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1243_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
v___x_1246_ = l_Lean_indentExpr(v_rhs_1228_);
v___x_1247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1245_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___x_1248_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v___x_1247_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___boxed(lean_object* v_lhs_1249_, lean_object* v_rhs_1250_, lean_object* v_00_u03b1_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1249_, v_rhs_1250_, v_00_u03b1_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec(v___y_1252_);
return v_res_1263_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1266_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__1));
v___x_1267_ = lean_unsigned_to_nat(4u);
v___x_1268_ = lean_unsigned_to_nat(198u);
v___x_1269_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__0));
v___x_1270_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1271_ = l_mkPanicMessageWithDecl(v___x_1270_, v___x_1269_, v___x_1268_, v___x_1267_, v___x_1266_);
return v___x_1271_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__1));
v___x_1275_ = lean_unsigned_to_nat(4u);
v___x_1276_ = lean_unsigned_to_nat(318u);
v___x_1277_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0));
v___x_1278_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1279_ = l_mkPanicMessageWithDecl(v___x_1278_, v___x_1277_, v___x_1276_, v___x_1275_, v___x_1274_);
return v___x_1279_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1281_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1282_ = lean_unsigned_to_nat(36u);
v___x_1283_ = lean_unsigned_to_nat(153u);
v___x_1284_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0));
v___x_1285_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1286_ = l_mkPanicMessageWithDecl(v___x_1285_, v___x_1284_, v___x_1283_, v___x_1282_, v___x_1281_);
return v___x_1286_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1287_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1288_ = lean_unsigned_to_nat(34u);
v___x_1289_ = lean_unsigned_to_nat(154u);
v___x_1290_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0));
v___x_1291_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1292_ = l_mkPanicMessageWithDecl(v___x_1291_, v___x_1290_, v___x_1289_, v___x_1288_, v___x_1287_);
return v___x_1292_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1294_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__3));
v___x_1295_ = lean_unsigned_to_nat(4u);
v___x_1296_ = lean_unsigned_to_nat(155u);
v___x_1297_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0));
v___x_1298_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1299_ = l_mkPanicMessageWithDecl(v___x_1298_, v___x_1297_, v___x_1296_, v___x_1295_, v___x_1294_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof(lean_object* v_lhs_1312_, lean_object* v_rhs_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1352_; lean_object* v_toCold_1355_; lean_object* v_currRecDepth_1356_; lean_object* v_ref_1357_; uint16_t v_optionFlags_1358_; uint8_t v_suppressElabErrors_1359_; uint8_t v_isRecordingDeps_1360_; lean_object* v_maxRecDepth_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v_toCold_1355_ = lean_ctor_get(v_a_1322_, 0);
v_currRecDepth_1356_ = lean_ctor_get(v_a_1322_, 1);
v_ref_1357_ = lean_ctor_get(v_a_1322_, 2);
v_optionFlags_1358_ = lean_ctor_get_uint16(v_a_1322_, sizeof(void*)*3);
v_suppressElabErrors_1359_ = lean_ctor_get_uint8(v_a_1322_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1360_ = lean_ctor_get_uint8(v_a_1322_, sizeof(void*)*3 + 3);
v_maxRecDepth_1361_ = lean_ctor_get(v_toCold_1355_, 3);
v___x_1362_ = l_Lean_Expr_cleanupAnnotations(v_lhs_1312_);
v___x_1363_ = l_Lean_Expr_isApp(v___x_1362_);
v___x_1426_ = lean_unsigned_to_nat(0u);
v___x_1427_ = lean_nat_dec_eq(v_maxRecDepth_1361_, v___x_1426_);
if (v___x_1427_ == 0)
{
uint8_t v___x_1428_; 
v___x_1428_ = lean_nat_dec_eq(v_currRecDepth_1356_, v_maxRecDepth_1361_);
if (v___x_1428_ == 0)
{
goto v___jp_1364_;
}
else
{
lean_object* v___x_1429_; 
lean_dec_ref(v___x_1362_);
lean_dec_ref(v_rhs_1313_);
lean_inc(v_ref_1357_);
v___x_1429_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1357_);
return v___x_1429_;
}
}
else
{
goto v___jp_1364_;
}
v___jp_1325_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1);
v___x_1337_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1336_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec_ref(v___y_1334_);
return v___x_1337_;
}
v___jp_1338_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2);
v___x_1350_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1349_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec_ref(v___y_1347_);
return v___x_1350_;
}
v___jp_1351_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4);
v___x_1354_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1353_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v___y_1352_, v_a_1323_);
lean_dec_ref(v___y_1352_);
return v___x_1354_;
}
v___jp_1364_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1365_ = lean_unsigned_to_nat(1u);
v___x_1366_ = lean_nat_add(v_currRecDepth_1356_, v___x_1365_);
lean_inc(v_ref_1357_);
lean_inc_ref(v_toCold_1355_);
v___x_1367_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1367_, 0, v_toCold_1355_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
lean_ctor_set(v___x_1367_, 2, v_ref_1357_);
lean_ctor_set_uint16(v___x_1367_, sizeof(void*)*3, v_optionFlags_1358_);
lean_ctor_set_uint8(v___x_1367_, sizeof(void*)*3 + 2, v_suppressElabErrors_1359_);
lean_ctor_set_uint8(v___x_1367_, sizeof(void*)*3 + 3, v_isRecordingDeps_1360_);
if (v___x_1363_ == 0)
{
lean_dec_ref(v___x_1362_);
lean_dec_ref(v_rhs_1313_);
v___y_1326_ = v_a_1314_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v_a_1316_;
v___y_1329_ = v_a_1317_;
v___y_1330_ = v_a_1318_;
v___y_1331_ = v_a_1319_;
v___y_1332_ = v_a_1320_;
v___y_1333_ = v_a_1321_;
v___y_1334_ = v___x_1367_;
v___y_1335_ = v_a_1323_;
goto v___jp_1325_;
}
else
{
lean_object* v_arg_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v_arg_1368_ = lean_ctor_get(v___x_1362_, 1);
lean_inc_ref(v_arg_1368_);
v___x_1369_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1362_);
v___x_1370_ = l_Lean_Expr_isApp(v___x_1369_);
if (v___x_1370_ == 0)
{
lean_dec_ref(v___x_1369_);
lean_dec_ref(v_arg_1368_);
lean_dec_ref(v_rhs_1313_);
v___y_1326_ = v_a_1314_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v_a_1316_;
v___y_1329_ = v_a_1317_;
v___y_1330_ = v_a_1318_;
v___y_1331_ = v_a_1319_;
v___y_1332_ = v_a_1320_;
v___y_1333_ = v_a_1321_;
v___y_1334_ = v___x_1367_;
v___y_1335_ = v_a_1323_;
goto v___jp_1325_;
}
else
{
lean_object* v_arg_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v_arg_1371_ = lean_ctor_get(v___x_1369_, 1);
lean_inc_ref(v_arg_1371_);
v___x_1372_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1369_);
v___x_1373_ = l_Lean_Expr_isApp(v___x_1372_);
if (v___x_1373_ == 0)
{
lean_dec_ref(v___x_1372_);
lean_dec_ref(v_arg_1371_);
lean_dec_ref(v_arg_1368_);
lean_dec_ref(v_rhs_1313_);
v___y_1326_ = v_a_1314_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v_a_1316_;
v___y_1329_ = v_a_1317_;
v___y_1330_ = v_a_1318_;
v___y_1331_ = v_a_1319_;
v___y_1332_ = v_a_1320_;
v___y_1333_ = v_a_1321_;
v___y_1334_ = v___x_1367_;
v___y_1335_ = v_a_1323_;
goto v___jp_1325_;
}
else
{
lean_object* v_arg_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v_arg_1374_ = lean_ctor_get(v___x_1372_, 1);
lean_inc_ref(v_arg_1374_);
v___x_1375_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1372_);
v___x_1376_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_1377_ = l_Lean_Expr_isConstOf(v___x_1375_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_dec_ref(v___x_1375_);
lean_dec_ref(v_arg_1374_);
lean_dec_ref(v_arg_1371_);
lean_dec_ref(v_arg_1368_);
lean_dec_ref(v_rhs_1313_);
v___y_1326_ = v_a_1314_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v_a_1316_;
v___y_1329_ = v_a_1317_;
v___y_1330_ = v_a_1318_;
v___y_1331_ = v_a_1319_;
v___y_1332_ = v_a_1320_;
v___y_1333_ = v_a_1321_;
v___y_1334_ = v___x_1367_;
v___y_1335_ = v_a_1323_;
goto v___jp_1325_;
}
else
{
lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1378_ = l_Lean_Expr_cleanupAnnotations(v_rhs_1313_);
v___x_1379_ = l_Lean_Expr_isApp(v___x_1378_);
if (v___x_1379_ == 0)
{
lean_dec_ref(v___x_1378_);
lean_dec_ref(v___x_1375_);
lean_dec_ref(v_arg_1374_);
lean_dec_ref(v_arg_1371_);
lean_dec_ref(v_arg_1368_);
v___y_1339_ = v_a_1314_;
v___y_1340_ = v_a_1315_;
v___y_1341_ = v_a_1316_;
v___y_1342_ = v_a_1317_;
v___y_1343_ = v_a_1318_;
v___y_1344_ = v_a_1319_;
v___y_1345_ = v_a_1320_;
v___y_1346_ = v_a_1321_;
v___y_1347_ = v___x_1367_;
v___y_1348_ = v_a_1323_;
goto v___jp_1338_;
}
else
{
lean_object* v_arg_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v_arg_1380_ = lean_ctor_get(v___x_1378_, 1);
lean_inc_ref(v_arg_1380_);
v___x_1381_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1378_);
v___x_1382_ = l_Lean_Expr_isApp(v___x_1381_);
if (v___x_1382_ == 0)
{
lean_dec_ref(v___x_1381_);
lean_dec_ref(v_arg_1380_);
lean_dec_ref(v___x_1375_);
lean_dec_ref(v_arg_1374_);
lean_dec_ref(v_arg_1371_);
lean_dec_ref(v_arg_1368_);
v___y_1339_ = v_a_1314_;
v___y_1340_ = v_a_1315_;
v___y_1341_ = v_a_1316_;
v___y_1342_ = v_a_1317_;
v___y_1343_ = v_a_1318_;
v___y_1344_ = v_a_1319_;
v___y_1345_ = v_a_1320_;
v___y_1346_ = v_a_1321_;
v___y_1347_ = v___x_1367_;
v___y_1348_ = v_a_1323_;
goto v___jp_1338_;
}
else
{
lean_object* v_arg_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v_arg_1383_ = lean_ctor_get(v___x_1381_, 1);
lean_inc_ref(v_arg_1383_);
v___x_1384_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1381_);
v___x_1385_ = l_Lean_Expr_isApp(v___x_1384_);
if (v___x_1385_ == 0)
{
lean_dec_ref(v___x_1384_);
lean_dec_ref(v_arg_1383_);
lean_dec_ref(v_arg_1380_);
lean_dec_ref(v___x_1375_);
lean_dec_ref(v_arg_1374_);
lean_dec_ref(v_arg_1371_);
lean_dec_ref(v_arg_1368_);
v___y_1339_ = v_a_1314_;
v___y_1340_ = v_a_1315_;
v___y_1341_ = v_a_1316_;
v___y_1342_ = v_a_1317_;
v___y_1343_ = v_a_1318_;
v___y_1344_ = v_a_1319_;
v___y_1345_ = v_a_1320_;
v___y_1346_ = v_a_1321_;
v___y_1347_ = v___x_1367_;
v___y_1348_ = v_a_1323_;
goto v___jp_1338_;
}
else
{
lean_object* v_arg_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v_arg_1386_ = lean_ctor_get(v___x_1384_, 1);
lean_inc_ref(v_arg_1386_);
v___x_1387_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1384_);
v___x_1388_ = l_Lean_Expr_isConstOf(v___x_1387_, v___x_1376_);
lean_dec_ref(v___x_1387_);
if (v___x_1388_ == 0)
{
lean_dec_ref(v_arg_1386_);
lean_dec_ref(v_arg_1383_);
lean_dec_ref(v_arg_1380_);
lean_dec_ref(v___x_1375_);
lean_dec_ref(v_arg_1374_);
lean_dec_ref(v_arg_1371_);
lean_dec_ref(v_arg_1368_);
v___y_1339_ = v_a_1314_;
v___y_1340_ = v_a_1315_;
v___y_1341_ = v_a_1316_;
v___y_1342_ = v_a_1317_;
v___y_1343_ = v_a_1318_;
v___y_1344_ = v_a_1319_;
v___y_1345_ = v_a_1320_;
v___y_1346_ = v_a_1321_;
v___y_1347_ = v___x_1367_;
v___y_1348_ = v_a_1323_;
goto v___jp_1338_;
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1389_ = lean_st_ref_get(v_a_1314_);
v___x_1390_ = lean_st_ref_get(v_a_1314_);
v___x_1391_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1389_, v_arg_1371_, v_arg_1380_);
lean_dec(v___x_1389_);
if (v___x_1391_ == 0)
{
lean_dec(v___x_1390_);
lean_dec_ref(v_arg_1386_);
lean_dec_ref(v_arg_1383_);
lean_dec_ref(v_arg_1380_);
lean_dec_ref(v___x_1375_);
lean_dec_ref(v_arg_1374_);
lean_dec_ref(v_arg_1371_);
lean_dec_ref(v_arg_1368_);
v___y_1352_ = v___x_1367_;
goto v___jp_1351_;
}
else
{
uint8_t v___x_1392_; 
v___x_1392_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1390_, v_arg_1368_, v_arg_1383_);
lean_dec(v___x_1390_);
if (v___x_1392_ == 0)
{
lean_dec_ref(v_arg_1386_);
lean_dec_ref(v_arg_1383_);
lean_dec_ref(v_arg_1380_);
lean_dec_ref(v___x_1375_);
lean_dec_ref(v_arg_1374_);
lean_dec_ref(v_arg_1371_);
lean_dec_ref(v_arg_1368_);
v___y_1352_ = v___x_1367_;
goto v___jp_1351_;
}
else
{
lean_object* v___x_1393_; size_t v___x_1394_; size_t v___x_1395_; uint8_t v___x_1396_; 
v___x_1393_ = l_Lean_Expr_constLevels_x21(v___x_1375_);
lean_dec_ref(v___x_1375_);
v___x_1394_ = lean_ptr_addr(v_arg_1374_);
v___x_1395_ = lean_ptr_addr(v_arg_1386_);
v___x_1396_ = lean_usize_dec_eq(v___x_1394_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
lean_inc_ref(v_arg_1380_);
lean_inc_ref(v_arg_1371_);
v___x_1397_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1371_, v_arg_1380_, v___x_1391_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v___x_1367_, v_a_1323_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1399_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1397_, 1);
lean_inc_ref(v_arg_1383_);
lean_inc_ref(v_arg_1368_);
v___x_1399_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1368_, v_arg_1383_, v___x_1391_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v___x_1367_, v_a_1323_);
lean_dec_ref_known(v___x_1367_, 3);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1410_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1410_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1410_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1404_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6));
v___x_1405_ = l_Lean_mkConst(v___x_1404_, v___x_1393_);
v___x_1406_ = l_Lean_mkApp8(v___x_1405_, v_arg_1374_, v_arg_1386_, v_arg_1371_, v_arg_1368_, v_arg_1383_, v_arg_1380_, v_a_1398_, v_a_1400_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v___x_1406_);
v___x_1408_ = v___x_1402_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
else
{
lean_dec(v_a_1398_);
lean_dec(v___x_1393_);
lean_dec_ref(v_arg_1386_);
lean_dec_ref(v_arg_1383_);
lean_dec_ref(v_arg_1380_);
lean_dec_ref(v_arg_1374_);
lean_dec_ref(v_arg_1371_);
lean_dec_ref(v_arg_1368_);
return v___x_1399_;
}
}
else
{
lean_dec(v___x_1393_);
lean_dec_ref(v_arg_1386_);
lean_dec_ref(v_arg_1383_);
lean_dec_ref(v_arg_1380_);
lean_dec_ref(v_arg_1374_);
lean_dec_ref(v_arg_1371_);
lean_dec_ref(v_arg_1368_);
lean_dec_ref_known(v___x_1367_, 3);
return v___x_1397_;
}
}
else
{
uint8_t v___x_1411_; lean_object* v___x_1412_; 
lean_dec_ref(v_arg_1386_);
v___x_1411_ = 0;
lean_inc_ref(v_arg_1380_);
lean_inc_ref(v_arg_1371_);
v___x_1412_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1371_, v_arg_1380_, v___x_1411_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v___x_1367_, v_a_1323_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1414_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1412_, 1);
lean_inc_ref(v_arg_1383_);
lean_inc_ref(v_arg_1368_);
v___x_1414_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1368_, v_arg_1383_, v___x_1411_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v___x_1367_, v_a_1323_);
lean_dec_ref_known(v___x_1367_, 3);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1425_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1425_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1425_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1419_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8));
v___x_1420_ = l_Lean_mkConst(v___x_1419_, v___x_1393_);
v___x_1421_ = l_Lean_mkApp7(v___x_1420_, v_arg_1374_, v_arg_1371_, v_arg_1368_, v_arg_1383_, v_arg_1380_, v_a_1413_, v_a_1415_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1421_);
v___x_1423_ = v___x_1417_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
else
{
lean_dec(v_a_1413_);
lean_dec(v___x_1393_);
lean_dec_ref(v_arg_1383_);
lean_dec_ref(v_arg_1380_);
lean_dec_ref(v_arg_1374_);
lean_dec_ref(v_arg_1371_);
lean_dec_ref(v_arg_1368_);
return v___x_1414_;
}
}
else
{
lean_dec(v___x_1393_);
lean_dec_ref(v_arg_1383_);
lean_dec_ref(v_arg_1380_);
lean_dec_ref(v_arg_1374_);
lean_dec_ref(v_arg_1371_);
lean_dec_ref(v_arg_1368_);
lean_dec_ref_known(v___x_1367_, 3);
return v___x_1412_;
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
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1434_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1435_ = lean_unsigned_to_nat(38u);
v___x_1436_ = lean_unsigned_to_nat(250u);
v___x_1437_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2));
v___x_1438_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1439_ = l_mkPanicMessageWithDecl(v___x_1438_, v___x_1437_, v___x_1436_, v___x_1435_, v___x_1434_);
return v___x_1439_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5(void){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4));
v___x_1442_ = lean_unsigned_to_nat(6u);
v___x_1443_ = lean_unsigned_to_nat(260u);
v___x_1444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2));
v___x_1445_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1446_ = l_mkPanicMessageWithDecl(v___x_1445_, v___x_1444_, v___x_1443_, v___x_1442_, v___x_1441_);
return v___x_1446_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1449_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__1));
v___x_1450_ = lean_unsigned_to_nat(4u);
v___x_1451_ = lean_unsigned_to_nat(219u);
v___x_1452_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__0));
v___x_1453_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1454_ = l_mkPanicMessageWithDecl(v___x_1453_, v___x_1452_, v___x_1451_, v___x_1450_, v___x_1449_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(lean_object* v_lhs_1455_, lean_object* v_rhs_1456_, uint8_t v_heq_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_numArgs_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; 
v_numArgs_1469_ = l_Lean_Expr_getAppNumArgs(v_lhs_1455_);
v___x_1470_ = l_Lean_Expr_getAppNumArgs(v_rhs_1456_);
v___x_1471_ = lean_nat_dec_eq(v___x_1470_, v_numArgs_1469_);
lean_dec(v___x_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec(v_numArgs_1469_);
lean_dec_ref(v_rhs_1456_);
lean_dec_ref(v_lhs_1455_);
v___x_1472_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2);
v___x_1473_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1472_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
return v___x_1473_;
}
else
{
lean_object* v_f_1474_; lean_object* v_g_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v_f_1474_ = l_Lean_Expr_getAppFn(v_lhs_1455_);
v_g_1475_ = l_Lean_Expr_getAppFn(v_rhs_1456_);
v___x_1476_ = lean_box(0);
lean_inc_ref(v_f_1474_);
v___x_1477_ = l_Lean_Meta_getFunInfo(v_f_1474_, v___x_1476_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
v___x_1479_ = l_Lean_Meta_FunInfo_getArity(v_a_1478_);
lean_dec(v_a_1478_);
v___x_1480_ = lean_nat_dec_lt(v___x_1479_, v_numArgs_1469_);
lean_dec(v___x_1479_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; 
v___x_1481_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_1474_, v_g_1475_, v_numArgs_1469_, v_lhs_1455_, v_rhs_1456_, v_heq_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
return v___x_1481_;
}
else
{
lean_object* v___x_1482_; 
lean_dec_ref(v_g_1475_);
lean_dec_ref(v_f_1474_);
lean_dec(v_numArgs_1469_);
lean_inc_ref(v_lhs_1455_);
v___x_1482_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(v_lhs_1455_, v_rhs_1456_);
if (lean_obj_tag(v___x_1482_) == 1)
{
lean_object* v_val_1483_; lean_object* v_fst_1484_; lean_object* v_snd_1485_; lean_object* v_a_1487_; lean_object* v___x_1491_; 
v_val_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_val_1483_);
lean_dec_ref_known(v___x_1482_, 1);
v_fst_1484_ = lean_ctor_get(v_val_1483_, 0);
lean_inc(v_fst_1484_);
v_snd_1485_ = lean_ctor_get(v_val_1483_, 1);
lean_inc_n(v_snd_1485_, 2);
lean_dec(v_val_1483_);
v___x_1491_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(v_fst_1484_, v_snd_1485_, v_a_1461_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1491_, 1);
v_a_1487_ = v_a_1492_;
goto v___jp_1486_;
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1515_; 
v_a_1493_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1495_ = v___x_1491_;
v_isShared_1496_ = v_isSharedCheck_1515_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1491_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1515_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
uint8_t v___x_1497_; 
v___x_1497_ = l_Lean_Exception_isInterrupt(v_a_1493_);
if (v___x_1497_ == 0)
{
uint8_t v___x_1498_; 
lean_inc(v_a_1493_);
v___x_1498_ = l_Lean_Exception_isRuntime(v_a_1493_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; 
lean_del_object(v___x_1495_);
lean_dec(v_a_1493_);
lean_inc_ref(v_rhs_1456_);
lean_inc_ref(v_lhs_1455_);
v___x_1499_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1455_, v_rhs_1456_, lean_box(0), v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1499_, 1);
v_a_1487_ = v_a_1500_;
goto v___jp_1486_;
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec(v_snd_1485_);
lean_dec_ref(v_rhs_1456_);
lean_dec_ref(v_lhs_1455_);
v_a_1501_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1499_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1499_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
else
{
lean_object* v___x_1510_; 
lean_dec(v_snd_1485_);
lean_dec_ref(v_rhs_1456_);
lean_dec_ref(v_lhs_1455_);
if (v_isShared_1496_ == 0)
{
v___x_1510_ = v___x_1495_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1493_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
else
{
lean_object* v___x_1513_; 
lean_dec(v_snd_1485_);
lean_dec_ref(v_rhs_1456_);
lean_dec_ref(v_lhs_1455_);
if (v_isShared_1496_ == 0)
{
v___x_1513_ = v___x_1495_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1493_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
v___jp_1486_:
{
lean_object* v___x_1488_; 
v___x_1488_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_1487_, v_lhs_1455_, v_rhs_1456_, v_snd_1485_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
lean_dec(v_snd_1485_);
lean_dec_ref(v_rhs_1456_);
lean_dec_ref(v_lhs_1455_);
lean_dec_ref(v_a_1487_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; lean_object* v___x_1490_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v___x_1488_, 1);
v___x_1490_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_1489_, v_heq_1457_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
return v___x_1490_;
}
else
{
return v___x_1488_;
}
}
}
else
{
lean_object* v___x_1516_; 
lean_dec(v___x_1482_);
v___x_1516_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1455_, v_rhs_1456_, lean_box(0), v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
return v___x_1516_;
}
}
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
lean_dec_ref(v_g_1475_);
lean_dec_ref(v_f_1474_);
lean_dec(v_numArgs_1469_);
lean_dec_ref(v_rhs_1456_);
lean_dec_ref(v_lhs_1455_);
v_a_1517_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v___x_1477_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1477_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(lean_object* v_lhs_1525_, lean_object* v_rhs_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
uint8_t v___x_1538_; 
v___x_1538_ = l_Lean_Expr_isApp(v_lhs_1525_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_box(0);
v___x_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
return v___x_1540_;
}
else
{
lean_object* v_a_u2081_1541_; lean_object* v_a_u2082_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v_a_u2081_1541_ = l_Lean_Expr_appArg_x21(v_lhs_1525_);
v_a_u2082_1542_ = l_Lean_Expr_appArg_x21(v_rhs_1526_);
v___x_1543_ = l_Lean_Expr_appFn_x21(v_lhs_1525_);
v___x_1544_ = l_Lean_Expr_appFn_x21(v_rhs_1526_);
v___x_1545_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v___x_1543_, v___x_1544_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
lean_dec_ref(v___x_1544_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1643_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1643_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1643_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
if (lean_obj_tag(v_a_1546_) == 1)
{
lean_object* v_val_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1607_; 
lean_del_object(v___x_1548_);
lean_dec_ref(v___x_1543_);
v_val_1550_ = lean_ctor_get(v_a_1546_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_a_1546_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1552_ = v_a_1546_;
v_isShared_1553_ = v_isSharedCheck_1607_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_val_1550_);
lean_dec(v_a_1546_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1607_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
size_t v___x_1554_; size_t v___x_1555_; uint8_t v___x_1556_; 
v___x_1554_ = lean_ptr_addr(v_a_u2081_1541_);
v___x_1555_ = lean_ptr_addr(v_a_u2082_1542_);
v___x_1556_ = lean_usize_dec_eq(v___x_1554_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; 
v___x_1557_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_1541_, v_a_u2082_1542_, v___x_1556_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1559_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1557_, 1);
v___x_1559_ = l_Lean_Meta_mkCongr(v_val_1550_, v_a_1558_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1570_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1562_ = v___x_1559_;
v_isShared_1563_ = v_isSharedCheck_1570_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1559_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1570_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v_a_1560_);
v___x_1565_ = v___x_1552_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1567_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1565_);
v___x_1567_ = v___x_1562_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_del_object(v___x_1552_);
v_a_1571_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1559_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1559_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_del_object(v___x_1552_);
lean_dec(v_val_1550_);
v_a_1579_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1557_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1557_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
else
{
lean_object* v___x_1587_; 
lean_dec_ref(v_a_u2082_1542_);
v___x_1587_ = l_Lean_Meta_mkCongrFun(v_val_1550_, v_a_u2081_1541_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1598_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1598_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1598_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v_a_1588_);
v___x_1593_ = v___x_1552_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1595_; 
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1593_);
v___x_1595_ = v___x_1590_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_del_object(v___x_1552_);
v_a_1599_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1587_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1587_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
}
else
{
size_t v___x_1608_; size_t v___x_1609_; uint8_t v___x_1610_; 
lean_dec(v_a_1546_);
v___x_1608_ = lean_ptr_addr(v_a_u2081_1541_);
v___x_1609_ = lean_ptr_addr(v_a_u2082_1542_);
v___x_1610_ = lean_usize_dec_eq(v___x_1608_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; 
lean_del_object(v___x_1548_);
v___x_1611_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_1541_, v_a_u2082_1542_, v___x_1610_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1613_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1611_, 1);
v___x_1613_ = l_Lean_Meta_mkCongrArg(v___x_1543_, v_a_1612_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1622_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1622_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1622_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1618_, 0, v_a_1614_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v___x_1618_);
v___x_1620_ = v___x_1616_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
v_a_1623_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1613_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1613_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec_ref(v___x_1543_);
v_a_1631_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1611_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1611_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
lean_dec_ref(v___x_1543_);
lean_dec_ref(v_a_u2082_1542_);
lean_dec_ref(v_a_u2081_1541_);
v___x_1639_ = lean_box(0);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v___x_1639_);
v___x_1641_ = v___x_1548_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1543_);
lean_dec_ref(v_a_u2082_1542_);
lean_dec_ref(v_a_u2081_1541_);
return v___x_1545_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__2));
v___x_1648_ = lean_unsigned_to_nat(14u);
v___x_1649_ = lean_unsigned_to_nat(22u);
v___x_1650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__1));
v___x_1651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__0));
v___x_1652_ = l_mkPanicMessageWithDecl(v___x_1651_, v___x_1650_, v___x_1649_, v___x_1648_, v___x_1647_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(lean_object* v_lhs_1653_, lean_object* v_rhs_1654_, uint8_t v_heq_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_1653_, v_rhs_1654_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1681_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1681_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1681_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___y_1673_; 
if (lean_obj_tag(v_a_1668_) == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3);
v___x_1679_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_spec__13(v___x_1678_);
v___y_1673_ = v___x_1679_;
goto v___jp_1672_;
}
else
{
lean_object* v_val_1680_; 
v_val_1680_ = lean_ctor_get(v_a_1668_, 0);
lean_inc(v_val_1680_);
lean_dec_ref_known(v_a_1668_, 1);
v___y_1673_ = v_val_1680_;
goto v___jp_1672_;
}
v___jp_1672_:
{
if (v_heq_1655_ == 0)
{
lean_object* v___x_1675_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___y_1673_);
v___x_1675_ = v___x_1670_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___y_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
else
{
lean_object* v___x_1677_; 
lean_del_object(v___x_1670_);
v___x_1677_ = l_Lean_Meta_mkHEqOfEq(v___y_1673_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_);
return v___x_1677_;
}
}
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
v_a_1682_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1667_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1667_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__1(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1691_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1692_ = lean_unsigned_to_nat(36u);
v___x_1693_ = lean_unsigned_to_nat(143u);
v___x_1694_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1695_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1696_ = l_mkPanicMessageWithDecl(v___x_1695_, v___x_1694_, v___x_1693_, v___x_1692_, v___x_1691_);
return v___x_1696_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__2(void){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1697_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1698_ = lean_unsigned_to_nat(34u);
v___x_1699_ = lean_unsigned_to_nat(144u);
v___x_1700_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1701_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1702_ = l_mkPanicMessageWithDecl(v___x_1701_, v___x_1700_, v___x_1699_, v___x_1698_, v___x_1697_);
return v___x_1702_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__4(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1704_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__3));
v___x_1705_ = lean_unsigned_to_nat(4u);
v___x_1706_ = lean_unsigned_to_nat(145u);
v___x_1707_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1708_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1709_ = l_mkPanicMessageWithDecl(v___x_1708_, v___x_1707_, v___x_1706_, v___x_1705_, v___x_1704_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrProof(lean_object* v_lhs_1720_, lean_object* v_rhs_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1760_; lean_object* v_toCold_1763_; lean_object* v_currRecDepth_1764_; lean_object* v_ref_1765_; uint16_t v_optionFlags_1766_; uint8_t v_suppressElabErrors_1767_; uint8_t v_isRecordingDeps_1768_; lean_object* v_maxRecDepth_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; lean_object* v___x_1834_; uint8_t v___x_1835_; 
v_toCold_1763_ = lean_ctor_get(v_a_1730_, 0);
v_currRecDepth_1764_ = lean_ctor_get(v_a_1730_, 1);
v_ref_1765_ = lean_ctor_get(v_a_1730_, 2);
v_optionFlags_1766_ = lean_ctor_get_uint16(v_a_1730_, sizeof(void*)*3);
v_suppressElabErrors_1767_ = lean_ctor_get_uint8(v_a_1730_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1768_ = lean_ctor_get_uint8(v_a_1730_, sizeof(void*)*3 + 3);
v_maxRecDepth_1769_ = lean_ctor_get(v_toCold_1763_, 3);
v___x_1770_ = l_Lean_Expr_cleanupAnnotations(v_lhs_1720_);
v___x_1771_ = l_Lean_Expr_isApp(v___x_1770_);
v___x_1834_ = lean_unsigned_to_nat(0u);
v___x_1835_ = lean_nat_dec_eq(v_maxRecDepth_1769_, v___x_1834_);
if (v___x_1835_ == 0)
{
uint8_t v___x_1836_; 
v___x_1836_ = lean_nat_dec_eq(v_currRecDepth_1764_, v_maxRecDepth_1769_);
if (v___x_1836_ == 0)
{
goto v___jp_1772_;
}
else
{
lean_object* v___x_1837_; 
lean_dec_ref(v___x_1770_);
lean_dec_ref(v_rhs_1721_);
lean_inc(v_ref_1765_);
v___x_1837_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1765_);
return v___x_1837_;
}
}
else
{
goto v___jp_1772_;
}
v___jp_1733_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__1, &l_Lean_Meta_Grind_mkEqCongrProof___closed__1_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__1);
v___x_1745_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1744_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec_ref(v___y_1742_);
return v___x_1745_;
}
v___jp_1746_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__2, &l_Lean_Meta_Grind_mkEqCongrProof___closed__2_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__2);
v___x_1758_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1757_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
lean_dec_ref(v___y_1755_);
return v___x_1758_;
}
v___jp_1759_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__4, &l_Lean_Meta_Grind_mkEqCongrProof___closed__4_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__4);
v___x_1762_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1761_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v___y_1760_, v_a_1731_);
lean_dec_ref(v___y_1760_);
return v___x_1762_;
}
v___jp_1772_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = lean_unsigned_to_nat(1u);
v___x_1774_ = lean_nat_add(v_currRecDepth_1764_, v___x_1773_);
lean_inc(v_ref_1765_);
lean_inc_ref(v_toCold_1763_);
v___x_1775_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1775_, 0, v_toCold_1763_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
lean_ctor_set(v___x_1775_, 2, v_ref_1765_);
lean_ctor_set_uint16(v___x_1775_, sizeof(void*)*3, v_optionFlags_1766_);
lean_ctor_set_uint8(v___x_1775_, sizeof(void*)*3 + 2, v_suppressElabErrors_1767_);
lean_ctor_set_uint8(v___x_1775_, sizeof(void*)*3 + 3, v_isRecordingDeps_1768_);
if (v___x_1771_ == 0)
{
lean_dec_ref(v___x_1770_);
lean_dec_ref(v_rhs_1721_);
v___y_1734_ = v_a_1722_;
v___y_1735_ = v_a_1723_;
v___y_1736_ = v_a_1724_;
v___y_1737_ = v_a_1725_;
v___y_1738_ = v_a_1726_;
v___y_1739_ = v_a_1727_;
v___y_1740_ = v_a_1728_;
v___y_1741_ = v_a_1729_;
v___y_1742_ = v___x_1775_;
v___y_1743_ = v_a_1731_;
goto v___jp_1733_;
}
else
{
lean_object* v_arg_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; 
v_arg_1776_ = lean_ctor_get(v___x_1770_, 1);
lean_inc_ref(v_arg_1776_);
v___x_1777_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1770_);
v___x_1778_ = l_Lean_Expr_isApp(v___x_1777_);
if (v___x_1778_ == 0)
{
lean_dec_ref(v___x_1777_);
lean_dec_ref(v_arg_1776_);
lean_dec_ref(v_rhs_1721_);
v___y_1734_ = v_a_1722_;
v___y_1735_ = v_a_1723_;
v___y_1736_ = v_a_1724_;
v___y_1737_ = v_a_1725_;
v___y_1738_ = v_a_1726_;
v___y_1739_ = v_a_1727_;
v___y_1740_ = v_a_1728_;
v___y_1741_ = v_a_1729_;
v___y_1742_ = v___x_1775_;
v___y_1743_ = v_a_1731_;
goto v___jp_1733_;
}
else
{
lean_object* v_arg_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
v_arg_1779_ = lean_ctor_get(v___x_1777_, 1);
lean_inc_ref(v_arg_1779_);
v___x_1780_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1777_);
v___x_1781_ = l_Lean_Expr_isApp(v___x_1780_);
if (v___x_1781_ == 0)
{
lean_dec_ref(v___x_1780_);
lean_dec_ref(v_arg_1779_);
lean_dec_ref(v_arg_1776_);
lean_dec_ref(v_rhs_1721_);
v___y_1734_ = v_a_1722_;
v___y_1735_ = v_a_1723_;
v___y_1736_ = v_a_1724_;
v___y_1737_ = v_a_1725_;
v___y_1738_ = v_a_1726_;
v___y_1739_ = v_a_1727_;
v___y_1740_ = v_a_1728_;
v___y_1741_ = v_a_1729_;
v___y_1742_ = v___x_1775_;
v___y_1743_ = v_a_1731_;
goto v___jp_1733_;
}
else
{
lean_object* v_arg_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v_arg_1782_ = lean_ctor_get(v___x_1780_, 1);
lean_inc_ref(v_arg_1782_);
v___x_1783_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1780_);
v___x_1784_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_1785_ = l_Lean_Expr_isConstOf(v___x_1783_, v___x_1784_);
if (v___x_1785_ == 0)
{
lean_dec_ref(v___x_1783_);
lean_dec_ref(v_arg_1782_);
lean_dec_ref(v_arg_1779_);
lean_dec_ref(v_arg_1776_);
lean_dec_ref(v_rhs_1721_);
v___y_1734_ = v_a_1722_;
v___y_1735_ = v_a_1723_;
v___y_1736_ = v_a_1724_;
v___y_1737_ = v_a_1725_;
v___y_1738_ = v_a_1726_;
v___y_1739_ = v_a_1727_;
v___y_1740_ = v_a_1728_;
v___y_1741_ = v_a_1729_;
v___y_1742_ = v___x_1775_;
v___y_1743_ = v_a_1731_;
goto v___jp_1733_;
}
else
{
lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___x_1786_ = l_Lean_Expr_cleanupAnnotations(v_rhs_1721_);
v___x_1787_ = l_Lean_Expr_isApp(v___x_1786_);
if (v___x_1787_ == 0)
{
lean_dec_ref(v___x_1786_);
lean_dec_ref(v___x_1783_);
lean_dec_ref(v_arg_1782_);
lean_dec_ref(v_arg_1779_);
lean_dec_ref(v_arg_1776_);
v___y_1747_ = v_a_1722_;
v___y_1748_ = v_a_1723_;
v___y_1749_ = v_a_1724_;
v___y_1750_ = v_a_1725_;
v___y_1751_ = v_a_1726_;
v___y_1752_ = v_a_1727_;
v___y_1753_ = v_a_1728_;
v___y_1754_ = v_a_1729_;
v___y_1755_ = v___x_1775_;
v___y_1756_ = v_a_1731_;
goto v___jp_1746_;
}
else
{
lean_object* v_arg_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v_arg_1788_ = lean_ctor_get(v___x_1786_, 1);
lean_inc_ref(v_arg_1788_);
v___x_1789_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1786_);
v___x_1790_ = l_Lean_Expr_isApp(v___x_1789_);
if (v___x_1790_ == 0)
{
lean_dec_ref(v___x_1789_);
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v___x_1783_);
lean_dec_ref(v_arg_1782_);
lean_dec_ref(v_arg_1779_);
lean_dec_ref(v_arg_1776_);
v___y_1747_ = v_a_1722_;
v___y_1748_ = v_a_1723_;
v___y_1749_ = v_a_1724_;
v___y_1750_ = v_a_1725_;
v___y_1751_ = v_a_1726_;
v___y_1752_ = v_a_1727_;
v___y_1753_ = v_a_1728_;
v___y_1754_ = v_a_1729_;
v___y_1755_ = v___x_1775_;
v___y_1756_ = v_a_1731_;
goto v___jp_1746_;
}
else
{
lean_object* v_arg_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v_arg_1791_ = lean_ctor_get(v___x_1789_, 1);
lean_inc_ref(v_arg_1791_);
v___x_1792_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1789_);
v___x_1793_ = l_Lean_Expr_isApp(v___x_1792_);
if (v___x_1793_ == 0)
{
lean_dec_ref(v___x_1792_);
lean_dec_ref(v_arg_1791_);
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v___x_1783_);
lean_dec_ref(v_arg_1782_);
lean_dec_ref(v_arg_1779_);
lean_dec_ref(v_arg_1776_);
v___y_1747_ = v_a_1722_;
v___y_1748_ = v_a_1723_;
v___y_1749_ = v_a_1724_;
v___y_1750_ = v_a_1725_;
v___y_1751_ = v_a_1726_;
v___y_1752_ = v_a_1727_;
v___y_1753_ = v_a_1728_;
v___y_1754_ = v_a_1729_;
v___y_1755_ = v___x_1775_;
v___y_1756_ = v_a_1731_;
goto v___jp_1746_;
}
else
{
lean_object* v_arg_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v_arg_1794_ = lean_ctor_get(v___x_1792_, 1);
lean_inc_ref(v_arg_1794_);
v___x_1795_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1792_);
v___x_1796_ = l_Lean_Expr_isConstOf(v___x_1795_, v___x_1784_);
lean_dec_ref(v___x_1795_);
if (v___x_1796_ == 0)
{
lean_dec_ref(v_arg_1794_);
lean_dec_ref(v_arg_1791_);
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v___x_1783_);
lean_dec_ref(v_arg_1782_);
lean_dec_ref(v_arg_1779_);
lean_dec_ref(v_arg_1776_);
v___y_1747_ = v_a_1722_;
v___y_1748_ = v_a_1723_;
v___y_1749_ = v_a_1724_;
v___y_1750_ = v_a_1725_;
v___y_1751_ = v_a_1726_;
v___y_1752_ = v_a_1727_;
v___y_1753_ = v_a_1728_;
v___y_1754_ = v_a_1729_;
v___y_1755_ = v___x_1775_;
v___y_1756_ = v_a_1731_;
goto v___jp_1746_;
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v___x_1797_ = lean_st_ref_get(v_a_1722_);
v___x_1798_ = lean_st_ref_get(v_a_1722_);
v___x_1799_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1797_, v_arg_1779_, v_arg_1791_);
lean_dec(v___x_1797_);
if (v___x_1799_ == 0)
{
lean_dec(v___x_1798_);
lean_dec_ref(v_arg_1794_);
lean_dec_ref(v_arg_1791_);
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v___x_1783_);
lean_dec_ref(v_arg_1782_);
lean_dec_ref(v_arg_1779_);
lean_dec_ref(v_arg_1776_);
v___y_1760_ = v___x_1775_;
goto v___jp_1759_;
}
else
{
uint8_t v___x_1800_; 
v___x_1800_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1798_, v_arg_1776_, v_arg_1788_);
lean_dec(v___x_1798_);
if (v___x_1800_ == 0)
{
lean_dec_ref(v_arg_1794_);
lean_dec_ref(v_arg_1791_);
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v___x_1783_);
lean_dec_ref(v_arg_1782_);
lean_dec_ref(v_arg_1779_);
lean_dec_ref(v_arg_1776_);
v___y_1760_ = v___x_1775_;
goto v___jp_1759_;
}
else
{
lean_object* v___x_1801_; size_t v___x_1802_; size_t v___x_1803_; uint8_t v___x_1804_; 
v___x_1801_ = l_Lean_Expr_constLevels_x21(v___x_1783_);
lean_dec_ref(v___x_1783_);
v___x_1802_ = lean_ptr_addr(v_arg_1782_);
v___x_1803_ = lean_ptr_addr(v_arg_1794_);
v___x_1804_ = lean_usize_dec_eq(v___x_1802_, v___x_1803_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; 
lean_inc_ref(v_arg_1791_);
lean_inc_ref(v_arg_1779_);
v___x_1805_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1779_, v_arg_1791_, v___x_1799_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v___x_1775_, v_a_1731_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1807_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
lean_dec_ref_known(v___x_1805_, 1);
lean_inc_ref(v_arg_1788_);
lean_inc_ref(v_arg_1776_);
v___x_1807_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1776_, v_arg_1788_, v___x_1799_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v___x_1775_, v_a_1731_);
lean_dec_ref_known(v___x_1775_, 3);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1818_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1818_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1818_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1812_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__6));
v___x_1813_ = l_Lean_mkConst(v___x_1812_, v___x_1801_);
v___x_1814_ = l_Lean_mkApp8(v___x_1813_, v_arg_1782_, v_arg_1794_, v_arg_1779_, v_arg_1776_, v_arg_1791_, v_arg_1788_, v_a_1806_, v_a_1808_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v___x_1814_);
v___x_1816_ = v___x_1810_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
else
{
lean_dec(v_a_1806_);
lean_dec(v___x_1801_);
lean_dec_ref(v_arg_1794_);
lean_dec_ref(v_arg_1791_);
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_arg_1782_);
lean_dec_ref(v_arg_1779_);
lean_dec_ref(v_arg_1776_);
return v___x_1807_;
}
}
else
{
lean_dec(v___x_1801_);
lean_dec_ref(v_arg_1794_);
lean_dec_ref(v_arg_1791_);
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_arg_1782_);
lean_dec_ref(v_arg_1779_);
lean_dec_ref(v_arg_1776_);
lean_dec_ref_known(v___x_1775_, 3);
return v___x_1805_;
}
}
else
{
uint8_t v___x_1819_; lean_object* v___x_1820_; 
lean_dec_ref(v_arg_1794_);
v___x_1819_ = 0;
lean_inc_ref(v_arg_1791_);
lean_inc_ref(v_arg_1779_);
v___x_1820_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1779_, v_arg_1791_, v___x_1819_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v___x_1775_, v_a_1731_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1822_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1821_);
lean_dec_ref_known(v___x_1820_, 1);
lean_inc_ref(v_arg_1788_);
lean_inc_ref(v_arg_1776_);
v___x_1822_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1776_, v_arg_1788_, v___x_1819_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v___x_1775_, v_a_1731_);
lean_dec_ref_known(v___x_1775_, 3);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1833_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1825_ = v___x_1822_;
v_isShared_1826_ = v_isSharedCheck_1833_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1822_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1833_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1831_; 
v___x_1827_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__8));
v___x_1828_ = l_Lean_mkConst(v___x_1827_, v___x_1801_);
v___x_1829_ = l_Lean_mkApp7(v___x_1828_, v_arg_1782_, v_arg_1779_, v_arg_1776_, v_arg_1791_, v_arg_1788_, v_a_1821_, v_a_1823_);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1829_);
v___x_1831_ = v___x_1825_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
else
{
lean_dec(v_a_1821_);
lean_dec(v___x_1801_);
lean_dec_ref(v_arg_1791_);
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_arg_1782_);
lean_dec_ref(v_arg_1779_);
lean_dec_ref(v_arg_1776_);
return v___x_1822_;
}
}
else
{
lean_dec(v___x_1801_);
lean_dec_ref(v_arg_1791_);
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_arg_1782_);
lean_dec_ref(v_arg_1779_);
lean_dec_ref(v_arg_1776_);
lean_dec_ref_known(v___x_1775_, 3);
return v___x_1820_;
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
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = lean_box(0);
v___x_1849_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3));
v___x_1850_ = l_Lean_mkConst(v___x_1849_, v___x_1848_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(lean_object* v_lhs_1851_, lean_object* v_rhs_1852_, uint8_t v_heq_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v___x_1865_; lean_object* v_p_1866_; lean_object* v_hp_1867_; lean_object* v___x_1868_; lean_object* v_q_1869_; lean_object* v_hq_1870_; uint8_t v___x_1871_; lean_object* v___x_1872_; 
v___x_1865_ = l_Lean_Expr_appFn_x21(v_lhs_1851_);
v_p_1866_ = l_Lean_Expr_appArg_x21(v___x_1865_);
lean_dec_ref(v___x_1865_);
v_hp_1867_ = l_Lean_Expr_appArg_x21(v_lhs_1851_);
v___x_1868_ = l_Lean_Expr_appFn_x21(v_rhs_1852_);
v_q_1869_ = l_Lean_Expr_appArg_x21(v___x_1868_);
lean_dec_ref(v___x_1868_);
v_hq_1870_ = l_Lean_Expr_appArg_x21(v_rhs_1852_);
v___x_1871_ = 0;
lean_inc_ref(v_q_1869_);
lean_inc_ref(v_p_1866_);
v___x_1872_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_p_1866_, v_q_1869_, v___x_1871_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1872_, 1);
v___x_1874_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4);
v___x_1875_ = l_Lean_mkApp5(v___x_1874_, v_p_1866_, v_q_1869_, v_a_1873_, v_hp_1867_, v_hq_1870_);
v___x_1876_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v___x_1875_, v_heq_1853_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
return v___x_1876_;
}
else
{
lean_dec_ref(v_hq_1870_);
lean_dec_ref(v_q_1869_);
lean_dec_ref(v_hp_1867_);
lean_dec_ref(v_p_1866_);
return v___x_1872_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2(void){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1887_ = lean_box(0);
v___x_1888_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1));
v___x_1889_ = l_Lean_mkConst(v___x_1888_, v___x_1887_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(lean_object* v_lhs_1890_, lean_object* v_rhs_1891_, uint8_t v_heq_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_){
_start:
{
lean_object* v___x_1904_; lean_object* v_p_1905_; lean_object* v_hp_1906_; lean_object* v___x_1907_; lean_object* v_q_1908_; lean_object* v_hq_1909_; uint8_t v___x_1910_; lean_object* v___x_1911_; 
v___x_1904_ = l_Lean_Expr_appFn_x21(v_lhs_1890_);
v_p_1905_ = l_Lean_Expr_appArg_x21(v___x_1904_);
lean_dec_ref(v___x_1904_);
v_hp_1906_ = l_Lean_Expr_appArg_x21(v_lhs_1890_);
v___x_1907_ = l_Lean_Expr_appFn_x21(v_rhs_1891_);
v_q_1908_ = l_Lean_Expr_appArg_x21(v___x_1907_);
lean_dec_ref(v___x_1907_);
v_hq_1909_ = l_Lean_Expr_appArg_x21(v_rhs_1891_);
v___x_1910_ = 0;
lean_inc_ref(v_q_1908_);
lean_inc_ref(v_p_1905_);
v___x_1911_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_p_1905_, v_q_1908_, v___x_1910_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
v___x_1913_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2);
v___x_1914_ = l_Lean_mkApp5(v___x_1913_, v_p_1905_, v_q_1908_, v_a_1912_, v_hp_1906_, v_hq_1909_);
v___x_1915_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v___x_1914_, v_heq_1892_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
return v___x_1915_;
}
else
{
lean_dec_ref(v_hq_1909_);
lean_dec_ref(v_q_1908_);
lean_dec_ref(v_hp_1906_);
lean_dec_ref(v_p_1905_);
return v___x_1911_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(lean_object* v_lhs_1916_, lean_object* v_rhs_1917_, uint8_t v_heq_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_){
_start:
{
if (lean_obj_tag(v_lhs_1916_) == 7)
{
if (lean_obj_tag(v_rhs_1917_) == 7)
{
lean_object* v_binderType_1930_; lean_object* v_body_1931_; lean_object* v_binderType_1932_; lean_object* v_body_1933_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1965_; lean_object* v___x_1994_; uint8_t v_transparency_1995_; uint8_t v___x_1996_; uint8_t v___x_1997_; 
v_binderType_1930_ = lean_ctor_get(v_lhs_1916_, 1);
lean_inc_ref(v_binderType_1930_);
v_body_1931_ = lean_ctor_get(v_lhs_1916_, 2);
lean_inc_ref(v_body_1931_);
lean_dec_ref_known(v_lhs_1916_, 3);
v_binderType_1932_ = lean_ctor_get(v_rhs_1917_, 1);
lean_inc_ref(v_binderType_1932_);
v_body_1933_ = lean_ctor_get(v_rhs_1917_, 2);
lean_inc_ref(v_body_1933_);
lean_dec_ref_known(v_rhs_1917_, 3);
v___x_1994_ = l_Lean_Meta_Context_config(v_a_1925_);
v_transparency_1995_ = lean_ctor_get_uint8(v___x_1994_, 9);
lean_dec_ref(v___x_1994_);
v___x_1996_ = 1;
v___x_1997_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1995_, v___x_1996_);
if (v___x_1997_ == 0)
{
lean_object* v_keyedConfig_1998_; uint8_t v_trackZetaDelta_1999_; lean_object* v_zetaDeltaSet_2000_; lean_object* v_lctx_2001_; lean_object* v_localInstances_2002_; lean_object* v_defEqCtx_x3f_2003_; lean_object* v_synthPendingDepth_2004_; lean_object* v_customCanUnfoldPredicate_x3f_2005_; uint8_t v_univApprox_2006_; uint8_t v_inTypeClassResolution_2007_; uint8_t v_cacheInferType_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v_keyedConfig_1998_ = lean_ctor_get(v_a_1925_, 0);
v_trackZetaDelta_1999_ = lean_ctor_get_uint8(v_a_1925_, sizeof(void*)*7);
v_zetaDeltaSet_2000_ = lean_ctor_get(v_a_1925_, 1);
v_lctx_2001_ = lean_ctor_get(v_a_1925_, 2);
v_localInstances_2002_ = lean_ctor_get(v_a_1925_, 3);
v_defEqCtx_x3f_2003_ = lean_ctor_get(v_a_1925_, 4);
v_synthPendingDepth_2004_ = lean_ctor_get(v_a_1925_, 5);
v_customCanUnfoldPredicate_x3f_2005_ = lean_ctor_get(v_a_1925_, 6);
v_univApprox_2006_ = lean_ctor_get_uint8(v_a_1925_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2007_ = lean_ctor_get_uint8(v_a_1925_, sizeof(void*)*7 + 2);
v_cacheInferType_2008_ = lean_ctor_get_uint8(v_a_1925_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1998_);
v___x_2009_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1996_, v_keyedConfig_1998_);
lean_inc(v_customCanUnfoldPredicate_x3f_2005_);
lean_inc(v_synthPendingDepth_2004_);
lean_inc(v_defEqCtx_x3f_2003_);
lean_inc_ref(v_localInstances_2002_);
lean_inc_ref(v_lctx_2001_);
lean_inc(v_zetaDeltaSet_2000_);
v___x_2010_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
lean_ctor_set(v___x_2010_, 1, v_zetaDeltaSet_2000_);
lean_ctor_set(v___x_2010_, 2, v_lctx_2001_);
lean_ctor_set(v___x_2010_, 3, v_localInstances_2002_);
lean_ctor_set(v___x_2010_, 4, v_defEqCtx_x3f_2003_);
lean_ctor_set(v___x_2010_, 5, v_synthPendingDepth_2004_);
lean_ctor_set(v___x_2010_, 6, v_customCanUnfoldPredicate_x3f_2005_);
lean_ctor_set_uint8(v___x_2010_, sizeof(void*)*7, v_trackZetaDelta_1999_);
lean_ctor_set_uint8(v___x_2010_, sizeof(void*)*7 + 1, v_univApprox_2006_);
lean_ctor_set_uint8(v___x_2010_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2007_);
lean_ctor_set_uint8(v___x_2010_, sizeof(void*)*7 + 3, v_cacheInferType_2008_);
lean_inc_ref(v_binderType_1930_);
v___x_2011_ = l_Lean_Meta_getLevel(v_binderType_1930_, v___x_2010_, v_a_1926_, v_a_1927_, v_a_1928_);
lean_dec_ref_known(v___x_2010_, 7);
v___y_1965_ = v___x_2011_;
goto v___jp_1964_;
}
else
{
lean_object* v___x_2012_; 
lean_inc_ref(v_binderType_1930_);
v___x_2012_ = l_Lean_Meta_getLevel(v_binderType_1930_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
v___y_1965_ = v___x_2012_;
goto v___jp_1964_;
}
v___jp_1934_:
{
if (lean_obj_tag(v___y_1936_) == 0)
{
lean_object* v_a_1937_; uint8_t v___x_1938_; lean_object* v___x_1939_; 
v_a_1937_ = lean_ctor_get(v___y_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref_known(v___y_1936_, 1);
v___x_1938_ = 0;
lean_inc_ref(v_binderType_1932_);
lean_inc_ref(v_binderType_1930_);
v___x_1939_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_binderType_1930_, v_binderType_1932_, v___x_1938_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1941_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref_known(v___x_1939_, 1);
lean_inc_ref(v_body_1933_);
lean_inc_ref(v_body_1931_);
v___x_1941_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_body_1931_, v_body_1933_, v___x_1938_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1955_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1944_ = v___x_1941_;
v_isShared_1945_ = v_isSharedCheck_1955_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1941_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1955_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1953_; 
v___x_1946_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__1));
v___x_1947_ = lean_box(0);
v___x_1948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1948_, 0, v_a_1937_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___y_1935_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = l_Lean_mkConst(v___x_1946_, v___x_1949_);
v___x_1951_ = l_Lean_mkApp6(v___x_1950_, v_binderType_1930_, v_binderType_1932_, v_body_1931_, v_body_1933_, v_a_1940_, v_a_1942_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 0, v___x_1951_);
v___x_1953_ = v___x_1944_;
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
lean_dec(v_a_1940_);
lean_dec(v_a_1937_);
lean_dec(v___y_1935_);
lean_dec_ref(v_body_1933_);
lean_dec_ref(v_binderType_1932_);
lean_dec_ref(v_body_1931_);
lean_dec_ref(v_binderType_1930_);
return v___x_1941_;
}
}
else
{
lean_dec(v_a_1937_);
lean_dec(v___y_1935_);
lean_dec_ref(v_body_1933_);
lean_dec_ref(v_binderType_1932_);
lean_dec_ref(v_body_1931_);
lean_dec_ref(v_binderType_1930_);
return v___x_1939_;
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec(v___y_1935_);
lean_dec_ref(v_body_1933_);
lean_dec_ref(v_binderType_1932_);
lean_dec_ref(v_body_1931_);
lean_dec_ref(v_binderType_1930_);
v_a_1956_ = lean_ctor_get(v___y_1936_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___y_1936_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___y_1936_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___y_1936_);
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
v___jp_1964_:
{
if (lean_obj_tag(v___y_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1967_; uint8_t v_transparency_1968_; uint8_t v___x_1969_; uint8_t v___x_1970_; 
v_a_1966_ = lean_ctor_get(v___y_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref_known(v___y_1965_, 1);
v___x_1967_ = l_Lean_Meta_Context_config(v_a_1925_);
v_transparency_1968_ = lean_ctor_get_uint8(v___x_1967_, 9);
lean_dec_ref(v___x_1967_);
v___x_1969_ = 1;
v___x_1970_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1968_, v___x_1969_);
if (v___x_1970_ == 0)
{
lean_object* v_keyedConfig_1971_; uint8_t v_trackZetaDelta_1972_; lean_object* v_zetaDeltaSet_1973_; lean_object* v_lctx_1974_; lean_object* v_localInstances_1975_; lean_object* v_defEqCtx_x3f_1976_; lean_object* v_synthPendingDepth_1977_; lean_object* v_customCanUnfoldPredicate_x3f_1978_; uint8_t v_univApprox_1979_; uint8_t v_inTypeClassResolution_1980_; uint8_t v_cacheInferType_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v_keyedConfig_1971_ = lean_ctor_get(v_a_1925_, 0);
v_trackZetaDelta_1972_ = lean_ctor_get_uint8(v_a_1925_, sizeof(void*)*7);
v_zetaDeltaSet_1973_ = lean_ctor_get(v_a_1925_, 1);
v_lctx_1974_ = lean_ctor_get(v_a_1925_, 2);
v_localInstances_1975_ = lean_ctor_get(v_a_1925_, 3);
v_defEqCtx_x3f_1976_ = lean_ctor_get(v_a_1925_, 4);
v_synthPendingDepth_1977_ = lean_ctor_get(v_a_1925_, 5);
v_customCanUnfoldPredicate_x3f_1978_ = lean_ctor_get(v_a_1925_, 6);
v_univApprox_1979_ = lean_ctor_get_uint8(v_a_1925_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1980_ = lean_ctor_get_uint8(v_a_1925_, sizeof(void*)*7 + 2);
v_cacheInferType_1981_ = lean_ctor_get_uint8(v_a_1925_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1971_);
v___x_1982_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1969_, v_keyedConfig_1971_);
lean_inc(v_customCanUnfoldPredicate_x3f_1978_);
lean_inc(v_synthPendingDepth_1977_);
lean_inc(v_defEqCtx_x3f_1976_);
lean_inc_ref(v_localInstances_1975_);
lean_inc_ref(v_lctx_1974_);
lean_inc(v_zetaDeltaSet_1973_);
v___x_1983_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
lean_ctor_set(v___x_1983_, 1, v_zetaDeltaSet_1973_);
lean_ctor_set(v___x_1983_, 2, v_lctx_1974_);
lean_ctor_set(v___x_1983_, 3, v_localInstances_1975_);
lean_ctor_set(v___x_1983_, 4, v_defEqCtx_x3f_1976_);
lean_ctor_set(v___x_1983_, 5, v_synthPendingDepth_1977_);
lean_ctor_set(v___x_1983_, 6, v_customCanUnfoldPredicate_x3f_1978_);
lean_ctor_set_uint8(v___x_1983_, sizeof(void*)*7, v_trackZetaDelta_1972_);
lean_ctor_set_uint8(v___x_1983_, sizeof(void*)*7 + 1, v_univApprox_1979_);
lean_ctor_set_uint8(v___x_1983_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1980_);
lean_ctor_set_uint8(v___x_1983_, sizeof(void*)*7 + 3, v_cacheInferType_1981_);
lean_inc_ref(v_body_1931_);
v___x_1984_ = l_Lean_Meta_getLevel(v_body_1931_, v___x_1983_, v_a_1926_, v_a_1927_, v_a_1928_);
lean_dec_ref_known(v___x_1983_, 7);
v___y_1935_ = v_a_1966_;
v___y_1936_ = v___x_1984_;
goto v___jp_1934_;
}
else
{
lean_object* v___x_1985_; 
lean_inc_ref(v_body_1931_);
v___x_1985_ = l_Lean_Meta_getLevel(v_body_1931_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
v___y_1935_ = v_a_1966_;
v___y_1936_ = v___x_1985_;
goto v___jp_1934_;
}
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec_ref(v_body_1933_);
lean_dec_ref(v_binderType_1932_);
lean_dec_ref(v_body_1931_);
lean_dec_ref(v_binderType_1930_);
v_a_1986_ = lean_ctor_get(v___y_1965_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___y_1965_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___y_1965_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___y_1965_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
}
else
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_dec_ref_known(v_lhs_1916_, 3);
lean_dec_ref(v_rhs_1917_);
v___x_2013_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3);
v___x_2014_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2013_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
return v___x_2014_;
}
}
else
{
lean_object* v___x_2015_; 
lean_inc_ref(v_lhs_1916_);
v___x_2015_ = l_Lean_Meta_Grind_useFunCC___redArg(v_lhs_1916_, v_a_1919_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; uint8_t v___x_2017_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref_known(v___x_2015_, 1);
v___x_2017_ = lean_unbox(v_a_2016_);
lean_dec(v_a_2016_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; 
v___x_2018_ = l_Lean_Expr_getAppNumArgs(v_lhs_1916_);
v___x_2019_ = l_Lean_Expr_getAppNumArgs(v_rhs_1917_);
v___x_2020_ = lean_nat_dec_eq(v___x_2019_, v___x_2018_);
lean_dec(v___x_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_dec(v___x_2018_);
lean_dec_ref(v_rhs_1917_);
lean_dec_ref(v_lhs_1916_);
v___x_2021_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5);
v___x_2022_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2021_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
return v___x_2022_;
}
else
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v___x_2023_ = l_Lean_Expr_getAppFn(v_lhs_1916_);
v___x_2024_ = l_Lean_Expr_getAppFn(v_rhs_1917_);
v___x_2048_ = lean_unsigned_to_nat(2u);
v___x_2049_ = lean_nat_dec_eq(v___x_2018_, v___x_2048_);
if (v___x_2049_ == 0)
{
goto v___jp_2050_;
}
else
{
lean_object* v___x_2055_; uint8_t v___x_2056_; 
v___x_2055_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9));
v___x_2056_ = l_Lean_Expr_isConstOf(v___x_2023_, v___x_2055_);
if (v___x_2056_ == 0)
{
goto v___jp_2050_;
}
else
{
uint8_t v___x_2057_; 
v___x_2057_ = l_Lean_Expr_isConstOf(v___x_2024_, v___x_2055_);
if (v___x_2057_ == 0)
{
goto v___jp_2050_;
}
else
{
lean_object* v___x_2058_; 
lean_dec_ref(v___x_2024_);
lean_dec_ref(v___x_2023_);
lean_dec(v___x_2018_);
v___x_2058_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_1916_, v_rhs_1917_, v_heq_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
lean_dec_ref(v_rhs_1917_);
lean_dec_ref(v_lhs_1916_);
return v___x_2058_;
}
}
}
v___jp_2025_:
{
lean_object* v___x_2026_; 
lean_inc_ref(v_rhs_1917_);
lean_inc_ref(v_lhs_1916_);
v___x_2026_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(v_lhs_1916_, v_rhs_1917_, v___x_2023_, v___x_2024_, v___x_2018_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
lean_dec_ref(v___x_2024_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; uint8_t v___x_2028_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2026_, 1);
v___x_2028_ = lean_unbox(v_a_2027_);
lean_dec(v_a_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; 
v___x_2029_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_1916_, v_rhs_1917_, v_heq_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
return v___x_2029_;
}
else
{
lean_object* v___x_2030_; 
v___x_2030_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_1916_, v_rhs_1917_, v_heq_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
lean_dec_ref(v_rhs_1917_);
lean_dec_ref(v_lhs_1916_);
return v___x_2030_;
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec_ref(v_rhs_1917_);
lean_dec_ref(v_lhs_1916_);
v_a_2031_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2026_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2026_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
v___jp_2039_:
{
lean_object* v___x_2040_; uint8_t v___x_2041_; 
v___x_2040_ = lean_unsigned_to_nat(3u);
v___x_2041_ = lean_nat_dec_eq(v___x_2018_, v___x_2040_);
if (v___x_2041_ == 0)
{
goto v___jp_2025_;
}
else
{
lean_object* v___x_2042_; uint8_t v___x_2043_; 
v___x_2042_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_2043_ = l_Lean_Expr_isConstOf(v___x_2023_, v___x_2042_);
if (v___x_2043_ == 0)
{
goto v___jp_2025_;
}
else
{
uint8_t v___x_2044_; 
v___x_2044_ = l_Lean_Expr_isConstOf(v___x_2024_, v___x_2042_);
if (v___x_2044_ == 0)
{
goto v___jp_2025_;
}
else
{
lean_object* v___x_2045_; 
lean_dec_ref(v___x_2024_);
lean_dec_ref(v___x_2023_);
lean_dec(v___x_2018_);
v___x_2045_ = l_Lean_Meta_Grind_mkEqCongrProof(v_lhs_1916_, v_rhs_1917_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
if (lean_obj_tag(v___x_2045_) == 0)
{
if (v_heq_1918_ == 0)
{
return v___x_2045_;
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2047_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___x_2045_, 1);
v___x_2047_ = l_Lean_Meta_mkHEqOfEq(v_a_2046_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
return v___x_2047_;
}
}
else
{
return v___x_2045_;
}
}
}
}
}
v___jp_2050_:
{
if (v___x_2049_ == 0)
{
goto v___jp_2039_;
}
else
{
lean_object* v___x_2051_; uint8_t v___x_2052_; 
v___x_2051_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7));
v___x_2052_ = l_Lean_Expr_isConstOf(v___x_2023_, v___x_2051_);
if (v___x_2052_ == 0)
{
goto v___jp_2039_;
}
else
{
uint8_t v___x_2053_; 
v___x_2053_ = l_Lean_Expr_isConstOf(v___x_2024_, v___x_2051_);
if (v___x_2053_ == 0)
{
goto v___jp_2039_;
}
else
{
lean_object* v___x_2054_; 
lean_dec_ref(v___x_2024_);
lean_dec_ref(v___x_2023_);
lean_dec(v___x_2018_);
v___x_2054_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_1916_, v_rhs_1917_, v_heq_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
lean_dec_ref(v_rhs_1917_);
lean_dec_ref(v_lhs_1916_);
return v___x_2054_;
}
}
}
}
}
}
else
{
lean_object* v___x_2059_; 
v___x_2059_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_1916_, v_rhs_1917_, v_heq_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
return v___x_2059_;
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec_ref(v_rhs_1917_);
lean_dec_ref(v_lhs_1916_);
v_a_2060_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2015_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2015_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(lean_object* v_lhs_2068_, lean_object* v_rhs_2069_, lean_object* v_h_2070_, uint8_t v_flipped_2071_, uint8_t v_heq_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2084_ = l_Lean_Meta_Grind_congrPlaceholderProof;
v___x_2085_ = lean_expr_eqv(v_h_2070_, v___x_2084_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; uint8_t v___x_2087_; 
v___x_2086_ = l_Lean_Meta_Grind_eqCongrSymmPlaceholderProof;
v___x_2087_ = lean_expr_eqv(v_h_2070_, v___x_2086_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; 
lean_dec_ref(v_rhs_2069_);
lean_dec_ref(v_lhs_2068_);
v___x_2088_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(v_h_2070_, v_flipped_2071_, v_heq_2072_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
return v___x_2088_;
}
else
{
lean_object* v___x_2089_; 
lean_dec_ref(v_h_2070_);
v___x_2089_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(v_lhs_2068_, v_rhs_2069_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2089_) == 0)
{
if (v_heq_2072_ == 0)
{
return v___x_2089_;
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2091_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2089_, 1);
v___x_2091_ = l_Lean_Meta_mkHEqOfEq(v_a_2090_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
return v___x_2091_;
}
}
else
{
return v___x_2089_;
}
}
}
else
{
lean_object* v___x_2092_; 
lean_dec_ref(v_h_2070_);
v___x_2092_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(v_lhs_2068_, v_rhs_2069_, v_heq_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
return v___x_2092_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1(void){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2094_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2095_ = lean_unsigned_to_nat(29u);
v___x_2096_ = lean_unsigned_to_nat(288u);
v___x_2097_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0));
v___x_2098_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2099_ = l_mkPanicMessageWithDecl(v___x_2098_, v___x_2097_, v___x_2096_, v___x_2095_, v___x_2094_);
return v___x_2099_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2100_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2101_ = lean_unsigned_to_nat(35u);
v___x_2102_ = lean_unsigned_to_nat(287u);
v___x_2103_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0));
v___x_2104_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2105_ = l_mkPanicMessageWithDecl(v___x_2104_, v___x_2103_, v___x_2102_, v___x_2101_, v___x_2100_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(lean_object* v_lhs_2106_, lean_object* v_common_2107_, lean_object* v_acc_2108_, uint8_t v_heq_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_){
_start:
{
size_t v___x_2121_; size_t v___x_2122_; uint8_t v___x_2123_; 
v___x_2121_ = lean_ptr_addr(v_lhs_2106_);
v___x_2122_ = lean_ptr_addr(v_common_2107_);
v___x_2123_ = lean_usize_dec_eq(v___x_2121_, v___x_2122_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = lean_st_ref_get(v_a_2110_);
lean_inc_ref(v_lhs_2106_);
v___x_2125_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2124_, v_lhs_2106_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
lean_dec(v___x_2124_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v_target_x3f_2127_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
v_target_x3f_2127_ = lean_ctor_get(v_a_2126_, 4);
lean_inc(v_target_x3f_2127_);
if (lean_obj_tag(v_target_x3f_2127_) == 1)
{
lean_object* v_proof_x3f_2128_; 
v_proof_x3f_2128_ = lean_ctor_get(v_a_2126_, 5);
lean_inc(v_proof_x3f_2128_);
if (lean_obj_tag(v_proof_x3f_2128_) == 1)
{
uint8_t v_flipped_2129_; lean_object* v_val_2130_; lean_object* v_val_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2159_; 
v_flipped_2129_ = lean_ctor_get_uint8(v_a_2126_, sizeof(void*)*12);
lean_dec(v_a_2126_);
v_val_2130_ = lean_ctor_get(v_target_x3f_2127_, 0);
lean_inc(v_val_2130_);
lean_dec_ref_known(v_target_x3f_2127_, 1);
v_val_2131_ = lean_ctor_get(v_proof_x3f_2128_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_proof_x3f_2128_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2133_ = v_proof_x3f_2128_;
v_isShared_2134_ = v_isSharedCheck_2159_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_val_2131_);
lean_dec(v_proof_x3f_2128_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2159_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; 
lean_inc(v_val_2130_);
v___x_2135_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_lhs_2106_, v_val_2130_, v_val_2131_, v_flipped_2129_, v_heq_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2137_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v___x_2137_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_acc_2108_, v_a_2136_, v_heq_2109_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2140_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 0, v_a_2138_);
v___x_2140_ = v___x_2133_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2138_);
v___x_2140_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
v_lhs_2106_ = v_val_2130_;
v_acc_2108_ = v___x_2140_;
goto _start;
}
}
else
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2150_; 
lean_del_object(v___x_2133_);
lean_dec(v_val_2130_);
v_a_2143_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2145_ = v___x_2137_;
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2137_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_del_object(v___x_2133_);
lean_dec(v_val_2130_);
lean_dec(v_acc_2108_);
v_a_2151_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2135_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2135_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
else
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
lean_dec_ref_known(v_target_x3f_2127_, 1);
lean_dec(v_proof_x3f_2128_);
lean_dec(v_a_2126_);
lean_dec(v_acc_2108_);
lean_dec_ref(v_lhs_2106_);
v___x_2160_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1);
v___x_2161_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2160_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
return v___x_2161_;
}
}
else
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
lean_dec(v_target_x3f_2127_);
lean_dec(v_a_2126_);
lean_dec(v_acc_2108_);
lean_dec_ref(v_lhs_2106_);
v___x_2162_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2);
v___x_2163_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2162_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
return v___x_2163_;
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec(v_acc_2108_);
lean_dec_ref(v_lhs_2106_);
v_a_2164_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2125_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2125_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v___x_2172_; 
lean_dec_ref(v_lhs_2106_);
v___x_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2172_, 0, v_acc_2108_);
return v___x_2172_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2174_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2175_ = lean_unsigned_to_nat(29u);
v___x_2176_ = lean_unsigned_to_nat(300u);
v___x_2177_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0));
v___x_2178_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2179_ = l_mkPanicMessageWithDecl(v___x_2178_, v___x_2177_, v___x_2176_, v___x_2175_, v___x_2174_);
return v___x_2179_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2180_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2181_ = lean_unsigned_to_nat(35u);
v___x_2182_ = lean_unsigned_to_nat(299u);
v___x_2183_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0));
v___x_2184_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2185_ = l_mkPanicMessageWithDecl(v___x_2184_, v___x_2183_, v___x_2182_, v___x_2181_, v___x_2180_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(lean_object* v_rhs_2186_, lean_object* v_common_2187_, lean_object* v_lhsEqCommon_x3f_2188_, uint8_t v_heq_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
size_t v___x_2201_; size_t v___x_2202_; uint8_t v___x_2203_; 
v___x_2201_ = lean_ptr_addr(v_rhs_2186_);
v___x_2202_ = lean_ptr_addr(v_common_2187_);
v___x_2203_ = lean_usize_dec_eq(v___x_2201_, v___x_2202_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = lean_st_ref_get(v_a_2190_);
lean_inc_ref(v_rhs_2186_);
v___x_2205_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2204_, v_rhs_2186_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
lean_dec(v___x_2204_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v_target_x3f_2207_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2206_);
lean_dec_ref_known(v___x_2205_, 1);
v_target_x3f_2207_ = lean_ctor_get(v_a_2206_, 4);
lean_inc(v_target_x3f_2207_);
if (lean_obj_tag(v_target_x3f_2207_) == 1)
{
lean_object* v_proof_x3f_2208_; 
v_proof_x3f_2208_ = lean_ctor_get(v_a_2206_, 5);
lean_inc(v_proof_x3f_2208_);
if (lean_obj_tag(v_proof_x3f_2208_) == 1)
{
uint8_t v_flipped_2209_; lean_object* v_val_2210_; lean_object* v_val_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2250_; 
v_flipped_2209_ = lean_ctor_get_uint8(v_a_2206_, sizeof(void*)*12);
lean_dec(v_a_2206_);
v_val_2210_ = lean_ctor_get(v_target_x3f_2207_, 0);
lean_inc(v_val_2210_);
lean_dec_ref_known(v_target_x3f_2207_, 1);
v_val_2211_ = lean_ctor_get(v_proof_x3f_2208_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v_proof_x3f_2208_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2213_ = v_proof_x3f_2208_;
v_isShared_2214_ = v_isSharedCheck_2250_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_val_2211_);
lean_dec(v_proof_x3f_2208_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2250_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
uint8_t v___y_2216_; 
if (v_flipped_2209_ == 0)
{
uint8_t v___x_2249_; 
v___x_2249_ = 1;
v___y_2216_ = v___x_2249_;
goto v___jp_2215_;
}
else
{
v___y_2216_ = v___x_2203_;
goto v___jp_2215_;
}
v___jp_2215_:
{
lean_object* v___x_2217_; 
lean_inc(v_val_2210_);
v___x_2217_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_val_2210_, v_rhs_2186_, v_val_2211_, v___y_2216_, v_heq_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2219_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
v___x_2219_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_val_2210_, v_common_2187_, v_lhsEqCommon_x3f_2188_, v_heq_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2221_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2220_);
lean_dec_ref_known(v___x_2219_, 1);
v___x_2221_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_a_2220_, v_a_2218_, v_heq_2189_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2232_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2224_ = v___x_2221_;
v_isShared_2225_ = v_isSharedCheck_2232_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2221_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2232_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 0, v_a_2222_);
v___x_2227_ = v___x_2213_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2229_; 
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v___x_2227_);
v___x_2229_ = v___x_2224_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_del_object(v___x_2213_);
v_a_2233_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2221_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2221_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
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
else
{
lean_dec(v_a_2218_);
lean_del_object(v___x_2213_);
return v___x_2219_;
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_del_object(v___x_2213_);
lean_dec(v_val_2210_);
lean_dec(v_lhsEqCommon_x3f_2188_);
v_a_2241_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2217_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2217_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
}
}
else
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
lean_dec_ref_known(v_target_x3f_2207_, 1);
lean_dec(v_proof_x3f_2208_);
lean_dec(v_a_2206_);
lean_dec(v_lhsEqCommon_x3f_2188_);
lean_dec_ref(v_rhs_2186_);
v___x_2251_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1);
v___x_2252_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2251_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
return v___x_2252_;
}
}
else
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
lean_dec(v_target_x3f_2207_);
lean_dec(v_a_2206_);
lean_dec(v_lhsEqCommon_x3f_2188_);
lean_dec_ref(v_rhs_2186_);
v___x_2253_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2);
v___x_2254_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2253_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
return v___x_2254_;
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v_lhsEqCommon_x3f_2188_);
lean_dec_ref(v_rhs_2186_);
v_a_2255_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2205_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2205_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
else
{
lean_object* v___x_2263_; 
lean_dec_ref(v_rhs_2186_);
v___x_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2263_, 0, v_lhsEqCommon_x3f_2188_);
return v___x_2263_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2264_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2265_ = lean_unsigned_to_nat(72u);
v___x_2266_ = lean_unsigned_to_nat(321u);
v___x_2267_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0));
v___x_2268_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2269_ = l_mkPanicMessageWithDecl(v___x_2268_, v___x_2267_, v___x_2266_, v___x_2265_, v___x_2264_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(lean_object* v_lhs_2270_, lean_object* v_rhs_2271_, uint8_t v_heq_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
size_t v___x_2284_; size_t v___x_2285_; uint8_t v___x_2286_; 
v___x_2284_ = lean_ptr_addr(v_lhs_2270_);
v___x_2285_ = lean_ptr_addr(v_rhs_2271_);
v___x_2286_ = lean_usize_dec_eq(v___x_2284_, v___x_2285_);
if (v___x_2286_ == 0)
{
lean_object* v___x_2287_; 
lean_inc_ref(v_lhs_2270_);
v___x_2287_ = l_Lean_Meta_Grind_getRootENode___redArg(v_lhs_2270_, v_a_2273_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; uint8_t v_heqProofs_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v_heqProofs_2289_ = lean_ctor_get_uint8(v_a_2288_, sizeof(void*)*12 + 4);
lean_dec(v_a_2288_);
v___x_2290_ = lean_st_ref_get(v_a_2273_);
lean_inc_ref(v_lhs_2270_);
v___x_2291_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2290_, v_lhs_2270_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
lean_dec(v___x_2290_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_a_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_a_2292_);
lean_dec_ref_known(v___x_2291_, 1);
v___x_2293_ = lean_st_ref_get(v_a_2273_);
lean_inc_ref(v_rhs_2271_);
v___x_2294_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2293_, v_rhs_2271_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
lean_dec(v___x_2293_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v_root_2296_; lean_object* v_root_2297_; size_t v___x_2298_; size_t v___x_2299_; uint8_t v___x_2300_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v_root_2296_ = lean_ctor_get(v_a_2292_, 2);
lean_inc_ref(v_root_2296_);
lean_dec(v_a_2292_);
v_root_2297_ = lean_ctor_get(v_a_2295_, 2);
lean_inc_ref(v_root_2297_);
lean_dec(v_a_2295_);
v___x_2298_ = lean_ptr_addr(v_root_2296_);
lean_dec_ref(v_root_2296_);
v___x_2299_ = lean_ptr_addr(v_root_2297_);
lean_dec_ref(v_root_2297_);
v___x_2300_ = lean_usize_dec_eq(v___x_2298_, v___x_2299_);
if (v___x_2300_ == 0)
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
lean_dec_ref(v_rhs_2271_);
lean_dec_ref(v_lhs_2270_);
v___x_2301_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2);
v___x_2302_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2301_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
return v___x_2302_;
}
else
{
lean_object* v___x_2303_; 
lean_inc_ref(v_rhs_2271_);
lean_inc_ref(v_lhs_2270_);
v___x_2303_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(v_lhs_2270_, v_rhs_2271_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2303_, 1);
v___x_2305_ = lean_box(0);
v___x_2306_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_2270_, v_a_2304_, v___x_2305_, v_heqProofs_2289_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2308_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2308_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_2271_, v_a_2304_, v_a_2307_, v_heqProofs_2289_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
lean_dec(v_a_2304_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2325_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2311_ = v___x_2308_;
v_isShared_2312_ = v_isSharedCheck_2325_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2308_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2325_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
if (lean_obj_tag(v_a_2309_) == 1)
{
lean_object* v_val_2313_; 
v_val_2313_ = lean_ctor_get(v_a_2309_, 0);
lean_inc(v_val_2313_);
lean_dec_ref_known(v_a_2309_, 1);
if (v_heqProofs_2289_ == 0)
{
if (v_heq_2272_ == 0)
{
lean_object* v___x_2318_; 
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 0, v_val_2313_);
v___x_2318_ = v___x_2311_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_val_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
else
{
lean_del_object(v___x_2311_);
goto v___jp_2314_;
}
}
else
{
if (v_heq_2272_ == 0)
{
lean_del_object(v___x_2311_);
goto v___jp_2314_;
}
else
{
lean_object* v___x_2321_; 
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 0, v_val_2313_);
v___x_2321_ = v___x_2311_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_val_2313_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
v___jp_2314_:
{
if (v_heq_2272_ == 0)
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Lean_Meta_mkEqOfHEq(v_val_2313_, v_heq_2272_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
return v___x_2315_;
}
else
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Lean_Meta_mkHEqOfEq(v_val_2313_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
return v___x_2316_;
}
}
}
else
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
lean_del_object(v___x_2311_);
lean_dec(v_a_2309_);
v___x_2323_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3);
v___x_2324_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2323_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
return v___x_2324_;
}
}
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
v_a_2326_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2308_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2308_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v_a_2304_);
lean_dec_ref(v_rhs_2271_);
v_a_2334_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2306_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2306_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
else
{
lean_dec_ref(v_rhs_2271_);
lean_dec_ref(v_lhs_2270_);
return v___x_2303_;
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec(v_a_2292_);
lean_dec_ref(v_rhs_2271_);
lean_dec_ref(v_lhs_2270_);
v_a_2342_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2294_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2294_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec_ref(v_rhs_2271_);
lean_dec_ref(v_lhs_2270_);
v_a_2350_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2291_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2291_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec_ref(v_rhs_2271_);
lean_dec_ref(v_lhs_2270_);
v_a_2358_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2287_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2287_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
else
{
lean_object* v___x_2366_; 
lean_dec_ref(v_rhs_2271_);
v___x_2366_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(v_lhs_2270_, v_heq_2272_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
return v___x_2366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(lean_object* v_thm_2367_, lean_object* v_lhs_2368_, lean_object* v_rhs_2369_, lean_object* v_i_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v___x_2382_; uint8_t v___x_2383_; 
v___x_2382_ = lean_unsigned_to_nat(0u);
v___x_2383_ = lean_nat_dec_lt(v___x_2382_, v_i_2370_);
if (v___x_2383_ == 0)
{
lean_object* v_proof_2384_; lean_object* v___x_2385_; 
v_proof_2384_ = lean_ctor_get(v_thm_2367_, 1);
lean_inc_ref(v_proof_2384_);
v___x_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2385_, 0, v_proof_2384_);
return v___x_2385_;
}
else
{
uint8_t v___x_2386_; lean_object* v___x_2387_; lean_object* v_i_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2386_ = 0;
v___x_2387_ = lean_unsigned_to_nat(1u);
v_i_2388_ = lean_nat_sub(v_i_2370_, v___x_2387_);
v___x_2389_ = l_Lean_Expr_appFn_x21(v_lhs_2368_);
v___x_2390_ = l_Lean_Expr_appFn_x21(v_rhs_2369_);
v___x_2391_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_2367_, v___x_2389_, v___x_2390_, v_i_2388_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
lean_dec_ref(v___x_2390_);
lean_dec_ref(v___x_2389_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v_argKinds_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; uint8_t v___y_2397_; lean_object* v___x_2408_; lean_object* v___x_2409_; uint8_t v___x_2410_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2391_, 1);
v_argKinds_2393_ = lean_ctor_get(v_thm_2367_, 2);
v___x_2394_ = l_Lean_Expr_appArg_x21(v_lhs_2368_);
v___x_2395_ = l_Lean_Expr_appArg_x21(v_rhs_2369_);
v___x_2408_ = lean_box(v___x_2386_);
v___x_2409_ = lean_array_get(v___x_2408_, v_argKinds_2393_, v_i_2388_);
lean_dec(v_i_2388_);
lean_dec(v___x_2408_);
v___x_2410_ = lean_unbox(v___x_2409_);
lean_dec(v___x_2409_);
if (v___x_2410_ == 4)
{
v___y_2397_ = v___x_2383_;
goto v___jp_2396_;
}
else
{
uint8_t v___x_2411_; 
v___x_2411_ = 0;
v___y_2397_ = v___x_2411_;
goto v___jp_2396_;
}
v___jp_2396_:
{
lean_object* v___x_2398_; 
lean_inc_ref(v___x_2395_);
lean_inc_ref(v___x_2394_);
v___x_2398_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___x_2394_, v___x_2395_, v___y_2397_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2407_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2401_ = v___x_2398_;
v_isShared_2402_ = v_isSharedCheck_2407_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2398_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2407_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2403_ = l_Lean_mkApp3(v_a_2392_, v___x_2394_, v___x_2395_, v_a_2399_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 0, v___x_2403_);
v___x_2405_ = v___x_2401_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
else
{
lean_dec_ref(v___x_2395_);
lean_dec_ref(v___x_2394_);
lean_dec(v_a_2392_);
return v___x_2398_;
}
}
}
else
{
lean_dec(v_i_2388_);
return v___x_2391_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(lean_object* v_f_2415_, lean_object* v_g_2416_, lean_object* v_numArgs_2417_, lean_object* v_lhs_2418_, lean_object* v_rhs_2419_, uint8_t v_heq_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v___x_2432_; 
lean_inc(v_numArgs_2417_);
lean_inc_ref(v_f_2415_);
v___x_2432_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(v_f_2415_, v_numArgs_2417_, v_a_2424_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v_argKinds_2434_; lean_object* v___x_2435_; uint8_t v___x_2436_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
lean_dec_ref_known(v___x_2432_, 1);
v_argKinds_2434_ = lean_ctor_get(v_a_2433_, 2);
v___x_2435_ = lean_array_get_size(v_argKinds_2434_);
v___x_2436_ = lean_nat_dec_eq(v___x_2435_, v_numArgs_2417_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
lean_dec(v_a_2433_);
lean_dec_ref(v_rhs_2419_);
lean_dec_ref(v_lhs_2418_);
lean_dec(v_numArgs_2417_);
lean_dec_ref(v_g_2416_);
lean_dec_ref(v_f_2415_);
v___x_2437_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2);
v___x_2438_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2437_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
return v___x_2438_;
}
else
{
lean_object* v___x_2439_; 
v___x_2439_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_2433_, v_lhs_2418_, v_rhs_2419_, v_numArgs_2417_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
lean_dec(v_a_2433_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; size_t v___x_2441_; size_t v___x_2442_; uint8_t v___x_2443_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2440_);
lean_dec_ref_known(v___x_2439_, 1);
v___x_2441_ = lean_ptr_addr(v_f_2415_);
v___x_2442_ = lean_ptr_addr(v_g_2416_);
v___x_2443_ = lean_usize_dec_eq(v___x_2441_, v___x_2442_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___f_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2444_ = lean_box(v___x_2443_);
v___x_2445_ = lean_box(v___x_2436_);
v___f_2446_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___boxed), 17, 5);
lean_closure_set(v___f_2446_, 0, v_numArgs_2417_);
lean_closure_set(v___f_2446_, 1, v_rhs_2419_);
lean_closure_set(v___f_2446_, 2, v_lhs_2418_);
lean_closure_set(v___f_2446_, 3, v___x_2444_);
lean_closure_set(v___f_2446_, 4, v___x_2445_);
v___x_2447_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__4));
v___x_2448_ = l_Lean_Core_mkFreshUserName(v___x_2447_, v_a_2429_, v_a_2430_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v___x_2450_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_a_2449_);
lean_dec_ref_known(v___x_2448_, 1);
lean_inc(v_a_2430_);
lean_inc_ref(v_a_2429_);
lean_inc(v_a_2428_);
lean_inc_ref(v_a_2427_);
lean_inc_ref(v_f_2415_);
v___x_2450_ = lean_infer_type(v_f_2415_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2452_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2451_);
lean_dec_ref_known(v___x_2450_, 1);
v___x_2452_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_a_2449_, v_a_2451_, v___f_2446_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2454_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
lean_dec_ref_known(v___x_2452_, 1);
v___x_2454_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_f_2415_, v_g_2416_, v___x_2443_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2456_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
lean_dec_ref_known(v___x_2454_, 1);
v___x_2456_ = l_Lean_Meta_mkEqNDRec(v_a_2453_, v_a_2440_, v_a_2455_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2458_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
lean_dec_ref_known(v___x_2456_, 1);
v___x_2458_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_2457_, v_heq_2420_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
return v___x_2458_;
}
else
{
return v___x_2456_;
}
}
else
{
lean_dec(v_a_2453_);
lean_dec(v_a_2440_);
return v___x_2454_;
}
}
else
{
lean_dec(v_a_2440_);
lean_dec_ref(v_g_2416_);
lean_dec_ref(v_f_2415_);
return v___x_2452_;
}
}
else
{
lean_dec(v_a_2449_);
lean_dec_ref(v___f_2446_);
lean_dec(v_a_2440_);
lean_dec_ref(v_g_2416_);
lean_dec_ref(v_f_2415_);
return v___x_2450_;
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec_ref(v___f_2446_);
lean_dec(v_a_2440_);
lean_dec_ref(v_g_2416_);
lean_dec_ref(v_f_2415_);
v_a_2459_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2448_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2448_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
else
{
lean_object* v___x_2467_; 
lean_dec_ref(v_rhs_2419_);
lean_dec_ref(v_lhs_2418_);
lean_dec(v_numArgs_2417_);
lean_dec_ref(v_g_2416_);
lean_dec_ref(v_f_2415_);
v___x_2467_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_2440_, v_heq_2420_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
return v___x_2467_;
}
}
else
{
lean_dec_ref(v_rhs_2419_);
lean_dec_ref(v_lhs_2418_);
lean_dec(v_numArgs_2417_);
lean_dec_ref(v_g_2416_);
lean_dec_ref(v_f_2415_);
return v___x_2439_;
}
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec_ref(v_rhs_2419_);
lean_dec_ref(v_lhs_2418_);
lean_dec(v_numArgs_2417_);
lean_dec_ref(v_g_2416_);
lean_dec_ref(v_f_2415_);
v_a_2468_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2432_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2432_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2477_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2478_ = lean_unsigned_to_nat(27u);
v___x_2479_ = lean_unsigned_to_nat(237u);
v___x_2480_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0));
v___x_2481_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2482_ = l_mkPanicMessageWithDecl(v___x_2481_, v___x_2480_, v___x_2479_, v___x_2478_, v___x_2477_);
return v___x_2482_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2(void){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2483_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2484_ = lean_unsigned_to_nat(27u);
v___x_2485_ = lean_unsigned_to_nat(236u);
v___x_2486_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0));
v___x_2487_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2488_ = l_mkPanicMessageWithDecl(v___x_2487_, v___x_2486_, v___x_2485_, v___x_2484_, v___x_2483_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(lean_object* v_lhs_2489_, lean_object* v_rhs_2490_, uint8_t v_heq_2491_, lean_object* v_e_u2081_2492_, lean_object* v_e_u2082_2493_, lean_object* v_numArgs_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_){
_start:
{
if (lean_obj_tag(v_e_u2081_2492_) == 5)
{
if (lean_obj_tag(v_e_u2082_2493_) == 5)
{
lean_object* v_fn_2506_; lean_object* v_fn_2507_; lean_object* v___x_2508_; lean_object* v_numArgs_2509_; size_t v___x_2510_; size_t v___x_2511_; uint8_t v___x_2512_; 
v_fn_2506_ = lean_ctor_get(v_e_u2081_2492_, 0);
lean_inc_ref(v_fn_2506_);
lean_dec_ref_known(v_e_u2081_2492_, 2);
v_fn_2507_ = lean_ctor_get(v_e_u2082_2493_, 0);
lean_inc_ref(v_fn_2507_);
lean_dec_ref_known(v_e_u2082_2493_, 2);
v___x_2508_ = lean_unsigned_to_nat(1u);
v_numArgs_2509_ = lean_nat_add(v_numArgs_2494_, v___x_2508_);
lean_dec(v_numArgs_2494_);
v___x_2510_ = lean_ptr_addr(v_fn_2506_);
v___x_2511_ = lean_ptr_addr(v_fn_2507_);
v___x_2512_ = lean_usize_dec_eq(v___x_2510_, v___x_2511_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; 
lean_inc_ref(v_fn_2507_);
lean_inc_ref(v_fn_2506_);
v___x_2513_ = l_Lean_Meta_Grind_hasSameType(v_fn_2506_, v_fn_2507_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; uint8_t v___x_2515_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_a_2514_);
lean_dec_ref_known(v___x_2513_, 1);
v___x_2515_ = lean_unbox(v_a_2514_);
lean_dec(v_a_2514_);
if (v___x_2515_ == 0)
{
v_e_u2081_2492_ = v_fn_2506_;
v_e_u2082_2493_ = v_fn_2507_;
v_numArgs_2494_ = v_numArgs_2509_;
goto _start;
}
else
{
lean_object* v___x_2517_; 
v___x_2517_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_2506_, v_fn_2507_, v_numArgs_2509_, v_lhs_2489_, v_rhs_2490_, v_heq_2491_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_);
return v___x_2517_;
}
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_dec(v_numArgs_2509_);
lean_dec_ref(v_fn_2507_);
lean_dec_ref(v_fn_2506_);
lean_dec_ref(v_rhs_2490_);
lean_dec_ref(v_lhs_2489_);
v_a_2518_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2513_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2513_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
else
{
lean_object* v___x_2526_; 
v___x_2526_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_2506_, v_fn_2507_, v_numArgs_2509_, v_lhs_2489_, v_rhs_2490_, v_heq_2491_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_);
return v___x_2526_;
}
}
else
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
lean_dec_ref_known(v_e_u2081_2492_, 2);
lean_dec(v_numArgs_2494_);
lean_dec_ref(v_e_u2082_2493_);
lean_dec_ref(v_rhs_2490_);
lean_dec_ref(v_lhs_2489_);
v___x_2527_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1);
v___x_2528_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2527_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_);
return v___x_2528_;
}
}
else
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
lean_dec(v_numArgs_2494_);
lean_dec_ref(v_e_u2082_2493_);
lean_dec_ref(v_e_u2081_2492_);
lean_dec_ref(v_rhs_2490_);
lean_dec_ref(v_lhs_2489_);
v___x_2529_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2);
v___x_2530_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2529_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_);
return v___x_2530_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(lean_object* v_lhs_2531_, lean_object* v_rhs_2532_, uint8_t v_heq_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_rhs_2532_);
lean_inc_ref(v_lhs_2531_);
v___x_2546_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(v_lhs_2531_, v_rhs_2532_, v_heq_2533_, v_lhs_2531_, v_rhs_2532_, v___x_2545_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC___boxed(lean_object* v_lhs_2547_, lean_object* v_rhs_2548_, lean_object* v_heq_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
uint8_t v_heq_boxed_2561_; lean_object* v_res_2562_; 
v_heq_boxed_2561_ = lean_unbox(v_heq_2549_);
v_res_2562_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_2547_, v_rhs_2548_, v_heq_boxed_2561_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
lean_dec(v_a_2551_);
lean_dec(v_a_2550_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___boxed(lean_object* v_lhs_2563_, lean_object* v_rhs_2564_, lean_object* v_heq_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
uint8_t v_heq_boxed_2577_; lean_object* v_res_2578_; 
v_heq_boxed_2577_ = lean_unbox(v_heq_2565_);
v_res_2578_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_2563_, v_rhs_2564_, v_heq_boxed_2577_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
lean_dec(v_a_2566_);
lean_dec_ref(v_rhs_2564_);
lean_dec_ref(v_lhs_2563_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___boxed(lean_object* v_lhs_2579_, lean_object* v_rhs_2580_, lean_object* v_heq_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_){
_start:
{
uint8_t v_heq_boxed_2593_; lean_object* v_res_2594_; 
v_heq_boxed_2593_ = lean_unbox(v_heq_2581_);
v_res_2594_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_2579_, v_rhs_2580_, v_heq_boxed_2593_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_);
lean_dec(v_a_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_a_2589_);
lean_dec_ref(v_a_2588_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
lean_dec(v_a_2583_);
lean_dec(v_a_2582_);
lean_dec_ref(v_rhs_2580_);
lean_dec_ref(v_lhs_2579_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof___boxed(lean_object* v_lhs_2595_, lean_object* v_rhs_2596_, lean_object* v_h_2597_, lean_object* v_flipped_2598_, lean_object* v_heq_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
uint8_t v_flipped_boxed_2611_; uint8_t v_heq_boxed_2612_; lean_object* v_res_2613_; 
v_flipped_boxed_2611_ = lean_unbox(v_flipped_2598_);
v_heq_boxed_2612_ = lean_unbox(v_heq_2599_);
v_res_2613_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_lhs_2595_, v_rhs_2596_, v_h_2597_, v_flipped_boxed_2611_, v_heq_boxed_2612_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_);
lean_dec(v_a_2609_);
lean_dec_ref(v_a_2608_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_a_2601_);
lean_dec(v_a_2600_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___boxed(lean_object* v_lhs_2614_, lean_object* v_rhs_2615_, lean_object* v_heq_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_){
_start:
{
uint8_t v_heq_boxed_2628_; lean_object* v_res_2629_; 
v_heq_boxed_2628_ = lean_unbox(v_heq_2616_);
v_res_2629_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_2614_, v_rhs_2615_, v_heq_boxed_2628_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_);
lean_dec(v_a_2626_);
lean_dec_ref(v_a_2625_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
lean_dec(v_a_2618_);
lean_dec(v_a_2617_);
lean_dec_ref(v_rhs_2615_);
lean_dec_ref(v_lhs_2614_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper___boxed(lean_object* v_thm_2630_, lean_object* v_lhs_2631_, lean_object* v_rhs_2632_, lean_object* v_i_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_2630_, v_lhs_2631_, v_rhs_2632_, v_i_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
lean_dec(v_a_2639_);
lean_dec_ref(v_a_2638_);
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec(v_i_2633_);
lean_dec_ref(v_rhs_2632_);
lean_dec_ref(v_lhs_2631_);
lean_dec_ref(v_thm_2630_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___boxed(lean_object** _args){
lean_object* v_lhs_2646_ = _args[0];
lean_object* v_rhs_2647_ = _args[1];
lean_object* v_heq_2648_ = _args[2];
lean_object* v_e_u2081_2649_ = _args[3];
lean_object* v_e_u2082_2650_ = _args[4];
lean_object* v_numArgs_2651_ = _args[5];
lean_object* v_a_2652_ = _args[6];
lean_object* v_a_2653_ = _args[7];
lean_object* v_a_2654_ = _args[8];
lean_object* v_a_2655_ = _args[9];
lean_object* v_a_2656_ = _args[10];
lean_object* v_a_2657_ = _args[11];
lean_object* v_a_2658_ = _args[12];
lean_object* v_a_2659_ = _args[13];
lean_object* v_a_2660_ = _args[14];
lean_object* v_a_2661_ = _args[15];
lean_object* v_a_2662_ = _args[16];
_start:
{
uint8_t v_heq_boxed_2663_; lean_object* v_res_2664_; 
v_heq_boxed_2663_ = lean_unbox(v_heq_2648_);
v_res_2664_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(v_lhs_2646_, v_rhs_2647_, v_heq_boxed_2663_, v_e_u2081_2649_, v_e_u2082_2650_, v_numArgs_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec(v_a_2652_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___boxed(lean_object* v_lhs_2665_, lean_object* v_common_2666_, lean_object* v_acc_2667_, lean_object* v_heq_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_){
_start:
{
uint8_t v_heq_boxed_2680_; lean_object* v_res_2681_; 
v_heq_boxed_2680_ = lean_unbox(v_heq_2668_);
v_res_2681_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_2665_, v_common_2666_, v_acc_2667_, v_heq_boxed_2680_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
lean_dec_ref(v_a_2675_);
lean_dec(v_a_2674_);
lean_dec_ref(v_a_2673_);
lean_dec(v_a_2672_);
lean_dec_ref(v_a_2671_);
lean_dec(v_a_2670_);
lean_dec(v_a_2669_);
lean_dec_ref(v_common_2666_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___boxed(lean_object** _args){
lean_object* v_f_2682_ = _args[0];
lean_object* v_g_2683_ = _args[1];
lean_object* v_numArgs_2684_ = _args[2];
lean_object* v_lhs_2685_ = _args[3];
lean_object* v_rhs_2686_ = _args[4];
lean_object* v_heq_2687_ = _args[5];
lean_object* v_a_2688_ = _args[6];
lean_object* v_a_2689_ = _args[7];
lean_object* v_a_2690_ = _args[8];
lean_object* v_a_2691_ = _args[9];
lean_object* v_a_2692_ = _args[10];
lean_object* v_a_2693_ = _args[11];
lean_object* v_a_2694_ = _args[12];
lean_object* v_a_2695_ = _args[13];
lean_object* v_a_2696_ = _args[14];
lean_object* v_a_2697_ = _args[15];
lean_object* v_a_2698_ = _args[16];
_start:
{
uint8_t v_heq_boxed_2699_; lean_object* v_res_2700_; 
v_heq_boxed_2699_ = lean_unbox(v_heq_2687_);
v_res_2700_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_2682_, v_g_2683_, v_numArgs_2684_, v_lhs_2685_, v_rhs_2686_, v_heq_boxed_2699_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
lean_dec(v_a_2688_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___boxed(lean_object* v_rhs_2701_, lean_object* v_common_2702_, lean_object* v_lhsEqCommon_x3f_2703_, lean_object* v_heq_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_){
_start:
{
uint8_t v_heq_boxed_2716_; lean_object* v_res_2717_; 
v_heq_boxed_2716_ = lean_unbox(v_heq_2704_);
v_res_2717_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_2701_, v_common_2702_, v_lhsEqCommon_x3f_2703_, v_heq_boxed_2716_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
lean_dec(v_a_2708_);
lean_dec_ref(v_a_2707_);
lean_dec(v_a_2706_);
lean_dec(v_a_2705_);
lean_dec_ref(v_common_2702_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___boxed(lean_object* v_lhs_2718_, lean_object* v_rhs_2719_, lean_object* v_heq_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_){
_start:
{
uint8_t v_heq_boxed_2732_; lean_object* v_res_2733_; 
v_heq_boxed_2732_ = lean_unbox(v_heq_2720_);
v_res_2733_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_2718_, v_rhs_2719_, v_heq_boxed_2732_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_);
lean_dec(v_a_2730_);
lean_dec_ref(v_a_2729_);
lean_dec(v_a_2728_);
lean_dec_ref(v_a_2727_);
lean_dec(v_a_2726_);
lean_dec_ref(v_a_2725_);
lean_dec(v_a_2724_);
lean_dec_ref(v_a_2723_);
lean_dec(v_a_2722_);
lean_dec(v_a_2721_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop___boxed(lean_object* v_lhs_2734_, lean_object* v_rhs_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_2734_, v_rhs_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_);
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
lean_dec_ref(v_rhs_2735_);
lean_dec_ref(v_lhs_2734_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___boxed(lean_object* v_lhs_2748_, lean_object* v_rhs_2749_, lean_object* v_heq_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_){
_start:
{
uint8_t v_heq_boxed_2762_; lean_object* v_res_2763_; 
v_heq_boxed_2762_ = lean_unbox(v_heq_2750_);
v_res_2763_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_lhs_2748_, v_rhs_2749_, v_heq_boxed_2762_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_);
lean_dec(v_a_2760_);
lean_dec_ref(v_a_2759_);
lean_dec(v_a_2758_);
lean_dec_ref(v_a_2757_);
lean_dec(v_a_2756_);
lean_dec_ref(v_a_2755_);
lean_dec(v_a_2754_);
lean_dec_ref(v_a_2753_);
lean_dec(v_a_2752_);
lean_dec(v_a_2751_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrProof___boxed(lean_object* v_lhs_2764_, lean_object* v_rhs_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Lean_Meta_Grind_mkEqCongrProof(v_lhs_2764_, v_rhs_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec(v_a_2766_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___boxed(lean_object* v_lhs_2778_, lean_object* v_rhs_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(v_lhs_2778_, v_rhs_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
lean_dec(v_a_2787_);
lean_dec_ref(v_a_2786_);
lean_dec(v_a_2785_);
lean_dec_ref(v_a_2784_);
lean_dec(v_a_2783_);
lean_dec_ref(v_a_2782_);
lean_dec(v_a_2781_);
lean_dec(v_a_2780_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___boxed(lean_object* v_lhs_2792_, lean_object* v_rhs_2793_, lean_object* v_heq_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_){
_start:
{
uint8_t v_heq_boxed_2806_; lean_object* v_res_2807_; 
v_heq_boxed_2806_ = lean_unbox(v_heq_2794_);
v_res_2807_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(v_lhs_2792_, v_rhs_2793_, v_heq_boxed_2806_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
lean_dec(v_a_2796_);
lean_dec(v_a_2795_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(lean_object* v_00_u03b1_2808_, lean_object* v_ref_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v___x_2821_; 
v___x_2821_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_2809_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___boxed(lean_object* v_00_u03b1_2822_, lean_object* v_ref_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(v_00_u03b1_2822_, v_ref_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec(v___y_2824_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(lean_object* v_00_u03b1_2836_, lean_object* v_name_2837_, uint8_t v_bi_2838_, lean_object* v_type_2839_, lean_object* v_k_2840_, uint8_t v_kind_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_2837_, v_bi_2838_, v_type_2839_, v_k_2840_, v_kind_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___boxed(lean_object** _args){
lean_object* v_00_u03b1_2854_ = _args[0];
lean_object* v_name_2855_ = _args[1];
lean_object* v_bi_2856_ = _args[2];
lean_object* v_type_2857_ = _args[3];
lean_object* v_k_2858_ = _args[4];
lean_object* v_kind_2859_ = _args[5];
lean_object* v___y_2860_ = _args[6];
lean_object* v___y_2861_ = _args[7];
lean_object* v___y_2862_ = _args[8];
lean_object* v___y_2863_ = _args[9];
lean_object* v___y_2864_ = _args[10];
lean_object* v___y_2865_ = _args[11];
lean_object* v___y_2866_ = _args[12];
lean_object* v___y_2867_ = _args[13];
lean_object* v___y_2868_ = _args[14];
lean_object* v___y_2869_ = _args[15];
lean_object* v___y_2870_ = _args[16];
_start:
{
uint8_t v_bi_boxed_2871_; uint8_t v_kind_boxed_2872_; lean_object* v_res_2873_; 
v_bi_boxed_2871_ = lean_unbox(v_bi_2856_);
v_kind_boxed_2872_ = lean_unbox(v_kind_2859_);
v_res_2873_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(v_00_u03b1_2854_, v_name_2855_, v_bi_boxed_2871_, v_type_2857_, v_k_2858_, v_kind_boxed_2872_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec(v___y_2860_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(lean_object* v_00_u03b1_2874_, lean_object* v_name_2875_, lean_object* v_type_2876_, lean_object* v_k_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_name_2875_, v_type_2876_, v_k_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___boxed(lean_object* v_00_u03b1_2890_, lean_object* v_name_2891_, lean_object* v_type_2892_, lean_object* v_k_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(v_00_u03b1_2890_, v_name_2891_, v_type_2892_, v_k_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec(v___y_2894_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(lean_object* v_00_u03b1_2906_, lean_object* v_msg_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v___x_2919_; 
v___x_2919_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v_msg_2907_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___boxed(lean_object* v_00_u03b1_2920_, lean_object* v_msg_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(v_00_u03b1_2920_, v_msg_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec(v___y_2922_);
return v_res_2933_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__1(void){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__0));
v___x_2936_ = l_Lean_stringToMessageData(v___x_2935_);
return v___x_2936_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__3(void){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2938_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__2));
v___x_2939_ = l_Lean_stringToMessageData(v___x_2938_);
return v___x_2939_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__5(void){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__4));
v___x_2942_ = l_Lean_stringToMessageData(v___x_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* lean_grind_mk_eq_proof(lean_object* v_a_2943_, lean_object* v_b_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_){
_start:
{
lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___x_2969_; 
lean_inc_ref(v_b_2944_);
lean_inc_ref(v_a_2943_);
v___x_2969_ = l_Lean_Meta_Grind_hasSameType(v_a_2943_, v_b_2944_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; uint8_t v___x_2971_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
lean_dec_ref_known(v___x_2969_, 1);
v___x_2971_ = lean_unbox(v_a_2970_);
lean_dec(v_a_2970_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2972_; 
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
lean_dec(v_a_2946_);
lean_dec(v_a_2945_);
lean_inc(v_a_2954_);
lean_inc_ref(v_a_2953_);
lean_inc(v_a_2952_);
lean_inc_ref(v_a_2951_);
lean_inc_ref(v_a_2943_);
v___x_2972_ = lean_infer_type(v_a_2943_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v___x_2974_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_a_2973_);
lean_dec_ref_known(v___x_2972_, 1);
lean_inc(v_a_2954_);
lean_inc_ref(v_a_2953_);
lean_inc(v_a_2952_);
lean_inc_ref(v_a_2951_);
lean_inc_ref(v_b_2944_);
v___x_2974_ = lean_infer_type(v_b_2944_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2975_);
lean_dec_ref_known(v___x_2974_, 1);
v___x_2976_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__1, &l_Lean_Meta_Grind_mkEqProofImpl___closed__1_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__1);
v___x_2977_ = l_Lean_indentExpr(v_a_2943_);
v___x_2978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2976_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
v___x_2979_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__3, &l_Lean_Meta_Grind_mkEqProofImpl___closed__3_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__3);
v___x_2980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2978_);
lean_ctor_set(v___x_2980_, 1, v___x_2979_);
v___x_2981_ = l_Lean_indentExpr(v_a_2973_);
v___x_2982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2980_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
v___x_2983_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__5, &l_Lean_Meta_Grind_mkEqProofImpl___closed__5_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__5);
v___x_2984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2982_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
v___x_2985_ = l_Lean_indentExpr(v_b_2944_);
v___x_2986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2984_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
v___x_2987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
lean_ctor_set(v___x_2987_, 1, v___x_2979_);
v___x_2988_ = l_Lean_indentExpr(v_a_2975_);
v___x_2989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2987_);
lean_ctor_set(v___x_2989_, 1, v___x_2988_);
v___x_2990_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v___x_2989_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
lean_dec(v_a_2952_);
lean_dec_ref(v_a_2951_);
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2990_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2990_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
else
{
lean_dec(v_a_2973_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
lean_dec(v_a_2952_);
lean_dec_ref(v_a_2951_);
lean_dec_ref(v_b_2944_);
lean_dec_ref(v_a_2943_);
return v___x_2974_;
}
}
else
{
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
lean_dec(v_a_2952_);
lean_dec_ref(v_a_2951_);
lean_dec_ref(v_b_2944_);
lean_dec_ref(v_a_2943_);
return v___x_2972_;
}
}
else
{
v___y_2957_ = v_a_2945_;
v___y_2958_ = v_a_2946_;
v___y_2959_ = v_a_2947_;
v___y_2960_ = v_a_2948_;
v___y_2961_ = v_a_2949_;
v___y_2962_ = v_a_2950_;
v___y_2963_ = v_a_2951_;
v___y_2964_ = v_a_2952_;
v___y_2965_ = v_a_2953_;
v___y_2966_ = v_a_2954_;
goto v___jp_2956_;
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
lean_dec(v_a_2952_);
lean_dec_ref(v_a_2951_);
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
lean_dec(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_b_2944_);
lean_dec_ref(v_a_2943_);
v_a_2999_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2969_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2969_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
v___jp_2956_:
{
uint8_t v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = 0;
v___x_2968_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_2943_, v_b_2944_, v___x_2967_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec(v___y_2957_);
return v___x_2968_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqProofImpl___boxed(lean_object* v_a_3007_, lean_object* v_b_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = lean_grind_mk_eq_proof(v_a_3007_, v_b_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* lean_grind_mk_heq_proof(lean_object* v_a_3021_, lean_object* v_b_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
uint8_t v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = 1;
v___x_3035_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_3021_, v_b_3022_, v___x_3034_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
lean_dec(v_a_3028_);
lean_dec_ref(v_a_3027_);
lean_dec(v_a_3026_);
lean_dec_ref(v_a_3025_);
lean_dec(v_a_3024_);
lean_dec(v_a_3023_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHEqProofImpl___boxed(lean_object* v_a_3036_, lean_object* v_b_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = lean_grind_mk_heq_proof(v_a_3036_, v_b_3037_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
return v_res_3049_;
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
