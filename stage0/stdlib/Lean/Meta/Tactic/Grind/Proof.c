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
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
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
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0;
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
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0;
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
v___x_203_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
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
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0(void){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(lean_object* v_msg_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_13049__overap_246_; lean_object* v___x_247_; 
v___x_245_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0);
v___x_13049__overap_246_ = lean_panic_fn_borrowed(v___x_245_, v_msg_233_);
lean_inc(v___y_243_);
lean_inc_ref(v___y_242_);
lean_inc(v___y_241_);
lean_inc_ref(v___y_240_);
lean_inc(v___y_239_);
lean_inc_ref(v___y_238_);
lean_inc(v___y_237_);
lean_inc_ref(v___y_236_);
lean_inc(v___y_235_);
lean_inc(v___y_234_);
v___x_247_ = lean_apply_11(v___x_13049__overap_246_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, lean_box(0));
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___boxed(lean_object* v_msg_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v_msg_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v___y_250_);
lean_dec(v___y_249_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(lean_object* v_t_261_, lean_object* v_k_262_){
_start:
{
if (lean_obj_tag(v_t_261_) == 0)
{
lean_object* v_k_263_; lean_object* v_v_264_; lean_object* v_l_265_; lean_object* v_r_266_; uint8_t v___x_267_; 
v_k_263_ = lean_ctor_get(v_t_261_, 1);
v_v_264_ = lean_ctor_get(v_t_261_, 2);
v_l_265_ = lean_ctor_get(v_t_261_, 3);
v_r_266_ = lean_ctor_get(v_t_261_, 4);
v___x_267_ = lean_nat_dec_lt(v_k_262_, v_k_263_);
if (v___x_267_ == 0)
{
uint8_t v___x_268_; 
v___x_268_ = lean_nat_dec_eq(v_k_262_, v_k_263_);
if (v___x_268_ == 0)
{
v_t_261_ = v_r_266_;
goto _start;
}
else
{
lean_object* v___x_270_; 
lean_inc(v_v_264_);
v___x_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_270_, 0, v_v_264_);
return v___x_270_;
}
}
else
{
v_t_261_ = v_l_265_;
goto _start;
}
}
else
{
lean_object* v___x_272_; 
v___x_272_ = lean_box(0);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg___boxed(lean_object* v_t_273_, lean_object* v_k_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(v_t_273_, v_k_274_);
lean_dec(v_k_274_);
lean_dec(v_t_273_);
return v_res_275_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_279_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_280_ = lean_unsigned_to_nat(35u);
v___x_281_ = lean_unsigned_to_nat(87u);
v___x_282_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__1));
v___x_283_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_284_ = l_mkPanicMessageWithDecl(v___x_283_, v___x_282_, v___x_281_, v___x_280_, v___x_279_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(lean_object* v___x_285_, lean_object* v_a_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v___x_298_; lean_object* v_snd_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_346_; 
v___x_298_ = lean_st_ref_get(v___y_287_);
v_snd_299_ = lean_ctor_get(v_a_286_, 1);
v_isSharedCheck_346_ = !lean_is_exclusive(v_a_286_);
if (v_isSharedCheck_346_ == 0)
{
lean_object* v_unused_347_; 
v_unused_347_ = lean_ctor_get(v_a_286_, 0);
lean_dec(v_unused_347_);
v___x_301_ = v_a_286_;
v_isShared_302_ = v_isSharedCheck_346_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_snd_299_);
lean_dec(v_a_286_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_346_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; 
lean_inc(v_snd_299_);
v___x_303_ = l_Lean_Meta_Grind_Goal_getENode(v___x_298_, v_snd_299_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec(v___x_298_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_337_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_337_ == 0)
{
v___x_306_ = v___x_303_;
v_isShared_307_ = v_isSharedCheck_337_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_303_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_337_;
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
v___x_310_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(v___x_285_, v_idx_309_);
lean_dec(v_idx_309_);
if (lean_obj_tag(v___x_310_) == 1)
{
lean_object* v___x_312_; 
lean_dec(v_target_x3f_308_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_310_);
v___x_312_ = v___x_301_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_snd_299_);
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
lean_object* v___x_317_; 
lean_dec(v___x_310_);
lean_del_object(v___x_306_);
v___x_317_ = lean_box(0);
if (lean_obj_tag(v_target_x3f_308_) == 1)
{
lean_object* v_val_318_; lean_object* v___x_320_; 
lean_dec(v_snd_299_);
v_val_318_ = lean_ctor_get(v_target_x3f_308_, 0);
lean_inc(v_val_318_);
lean_dec_ref_known(v_target_x3f_308_, 1);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v_val_318_);
lean_ctor_set(v___x_301_, 0, v___x_317_);
v___x_320_ = v___x_301_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_val_318_);
v___x_320_ = v_reuseFailAlloc_322_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
v_a_286_ = v___x_320_;
goto _start;
}
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec(v_target_x3f_308_);
v___x_323_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3);
v___x_324_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3(v___x_323_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v___x_326_; 
lean_dec_ref_known(v___x_324_, 1);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_317_);
v___x_326_ = v___x_301_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_snd_299_);
v___x_326_ = v_reuseFailAlloc_328_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
v_a_286_ = v___x_326_;
goto _start;
}
}
else
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
lean_del_object(v___x_301_);
lean_dec(v_snd_299_);
v_a_329_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___x_324_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_324_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
lean_del_object(v___x_301_);
lean_dec(v_snd_299_);
v_a_338_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_303_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_303_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___boxed(lean_object* v___x_348_, lean_object* v_a_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(v___x_348_, v_a_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec(v___y_350_);
lean_dec(v___x_348_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(lean_object* v_k_362_, lean_object* v_v_363_, lean_object* v_t_364_){
_start:
{
if (lean_obj_tag(v_t_364_) == 0)
{
lean_object* v_size_365_; lean_object* v_k_366_; lean_object* v_v_367_; lean_object* v_l_368_; lean_object* v_r_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_650_; 
v_size_365_ = lean_ctor_get(v_t_364_, 0);
v_k_366_ = lean_ctor_get(v_t_364_, 1);
v_v_367_ = lean_ctor_get(v_t_364_, 2);
v_l_368_ = lean_ctor_get(v_t_364_, 3);
v_r_369_ = lean_ctor_get(v_t_364_, 4);
v_isSharedCheck_650_ = !lean_is_exclusive(v_t_364_);
if (v_isSharedCheck_650_ == 0)
{
v___x_371_ = v_t_364_;
v_isShared_372_ = v_isSharedCheck_650_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_r_369_);
lean_inc(v_l_368_);
lean_inc(v_v_367_);
lean_inc(v_k_366_);
lean_inc(v_size_365_);
lean_dec(v_t_364_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_650_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
uint8_t v___x_373_; 
v___x_373_ = lean_nat_dec_lt(v_k_362_, v_k_366_);
if (v___x_373_ == 0)
{
uint8_t v___x_374_; 
v___x_374_ = lean_nat_dec_eq(v_k_362_, v_k_366_);
if (v___x_374_ == 0)
{
lean_object* v_impl_375_; lean_object* v___x_376_; 
lean_dec(v_size_365_);
v_impl_375_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_k_362_, v_v_363_, v_r_369_);
v___x_376_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_368_) == 0)
{
lean_object* v_size_377_; lean_object* v_size_378_; lean_object* v_k_379_; lean_object* v_v_380_; lean_object* v_l_381_; lean_object* v_r_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v_size_377_ = lean_ctor_get(v_l_368_, 0);
v_size_378_ = lean_ctor_get(v_impl_375_, 0);
lean_inc(v_size_378_);
v_k_379_ = lean_ctor_get(v_impl_375_, 1);
lean_inc(v_k_379_);
v_v_380_ = lean_ctor_get(v_impl_375_, 2);
lean_inc(v_v_380_);
v_l_381_ = lean_ctor_get(v_impl_375_, 3);
lean_inc(v_l_381_);
v_r_382_ = lean_ctor_get(v_impl_375_, 4);
lean_inc(v_r_382_);
v___x_383_ = lean_unsigned_to_nat(3u);
v___x_384_ = lean_nat_mul(v___x_383_, v_size_377_);
v___x_385_ = lean_nat_dec_lt(v___x_384_, v_size_378_);
lean_dec(v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
lean_dec(v_r_382_);
lean_dec(v_l_381_);
lean_dec(v_v_380_);
lean_dec(v_k_379_);
v___x_386_ = lean_nat_add(v___x_376_, v_size_377_);
v___x_387_ = lean_nat_add(v___x_386_, v_size_378_);
lean_dec(v_size_378_);
lean_dec(v___x_386_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 4, v_impl_375_);
lean_ctor_set(v___x_371_, 0, v___x_387_);
v___x_389_ = v___x_371_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_k_366_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v_v_367_);
lean_ctor_set(v_reuseFailAlloc_390_, 3, v_l_368_);
lean_ctor_set(v_reuseFailAlloc_390_, 4, v_impl_375_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
else
{
lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_454_; 
v_isSharedCheck_454_ = !lean_is_exclusive(v_impl_375_);
if (v_isSharedCheck_454_ == 0)
{
lean_object* v_unused_455_; lean_object* v_unused_456_; lean_object* v_unused_457_; lean_object* v_unused_458_; lean_object* v_unused_459_; 
v_unused_455_ = lean_ctor_get(v_impl_375_, 4);
lean_dec(v_unused_455_);
v_unused_456_ = lean_ctor_get(v_impl_375_, 3);
lean_dec(v_unused_456_);
v_unused_457_ = lean_ctor_get(v_impl_375_, 2);
lean_dec(v_unused_457_);
v_unused_458_ = lean_ctor_get(v_impl_375_, 1);
lean_dec(v_unused_458_);
v_unused_459_ = lean_ctor_get(v_impl_375_, 0);
lean_dec(v_unused_459_);
v___x_392_ = v_impl_375_;
v_isShared_393_ = v_isSharedCheck_454_;
goto v_resetjp_391_;
}
else
{
lean_dec(v_impl_375_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_454_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v_size_394_; lean_object* v_k_395_; lean_object* v_v_396_; lean_object* v_l_397_; lean_object* v_r_398_; lean_object* v_size_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v_size_394_ = lean_ctor_get(v_l_381_, 0);
v_k_395_ = lean_ctor_get(v_l_381_, 1);
v_v_396_ = lean_ctor_get(v_l_381_, 2);
v_l_397_ = lean_ctor_get(v_l_381_, 3);
v_r_398_ = lean_ctor_get(v_l_381_, 4);
v_size_399_ = lean_ctor_get(v_r_382_, 0);
v___x_400_ = lean_unsigned_to_nat(2u);
v___x_401_ = lean_nat_mul(v___x_400_, v_size_399_);
v___x_402_ = lean_nat_dec_lt(v_size_394_, v___x_401_);
lean_dec(v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_430_; 
lean_inc(v_r_398_);
lean_inc(v_l_397_);
lean_inc(v_v_396_);
lean_inc(v_k_395_);
v_isSharedCheck_430_ = !lean_is_exclusive(v_l_381_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; lean_object* v_unused_432_; lean_object* v_unused_433_; lean_object* v_unused_434_; lean_object* v_unused_435_; 
v_unused_431_ = lean_ctor_get(v_l_381_, 4);
lean_dec(v_unused_431_);
v_unused_432_ = lean_ctor_get(v_l_381_, 3);
lean_dec(v_unused_432_);
v_unused_433_ = lean_ctor_get(v_l_381_, 2);
lean_dec(v_unused_433_);
v_unused_434_ = lean_ctor_get(v_l_381_, 1);
lean_dec(v_unused_434_);
v_unused_435_ = lean_ctor_get(v_l_381_, 0);
lean_dec(v_unused_435_);
v___x_404_ = v_l_381_;
v_isShared_405_ = v_isSharedCheck_430_;
goto v_resetjp_403_;
}
else
{
lean_dec(v_l_381_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_430_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_420_; 
v___x_406_ = lean_nat_add(v___x_376_, v_size_377_);
v___x_407_ = lean_nat_add(v___x_406_, v_size_378_);
lean_dec(v_size_378_);
if (lean_obj_tag(v_l_397_) == 0)
{
lean_object* v_size_428_; 
v_size_428_ = lean_ctor_get(v_l_397_, 0);
lean_inc(v_size_428_);
v___y_420_ = v_size_428_;
goto v___jp_419_;
}
else
{
lean_object* v___x_429_; 
v___x_429_ = lean_unsigned_to_nat(0u);
v___y_420_ = v___x_429_;
goto v___jp_419_;
}
v___jp_408_:
{
lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_412_ = lean_nat_add(v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec(v___y_410_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 4, v_r_382_);
lean_ctor_set(v___x_404_, 3, v_r_398_);
lean_ctor_set(v___x_404_, 2, v_v_380_);
lean_ctor_set(v___x_404_, 1, v_k_379_);
lean_ctor_set(v___x_404_, 0, v___x_412_);
v___x_414_ = v___x_404_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_k_379_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v_v_380_);
lean_ctor_set(v_reuseFailAlloc_418_, 3, v_r_398_);
lean_ctor_set(v_reuseFailAlloc_418_, 4, v_r_382_);
v___x_414_ = v_reuseFailAlloc_418_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_416_; 
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 4, v___x_414_);
lean_ctor_set(v___x_392_, 3, v___y_409_);
lean_ctor_set(v___x_392_, 2, v_v_396_);
lean_ctor_set(v___x_392_, 1, v_k_395_);
lean_ctor_set(v___x_392_, 0, v___x_407_);
v___x_416_ = v___x_392_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_k_395_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_v_396_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v___y_409_);
lean_ctor_set(v_reuseFailAlloc_417_, 4, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
v___jp_419_:
{
lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_421_ = lean_nat_add(v___x_406_, v___y_420_);
lean_dec(v___y_420_);
lean_dec(v___x_406_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 4, v_l_397_);
lean_ctor_set(v___x_371_, 0, v___x_421_);
v___x_423_ = v___x_371_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_421_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_k_366_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_v_367_);
lean_ctor_set(v_reuseFailAlloc_427_, 3, v_l_368_);
lean_ctor_set(v_reuseFailAlloc_427_, 4, v_l_397_);
v___x_423_ = v_reuseFailAlloc_427_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; 
v___x_424_ = lean_nat_add(v___x_376_, v_size_399_);
if (lean_obj_tag(v_r_398_) == 0)
{
lean_object* v_size_425_; 
v_size_425_ = lean_ctor_get(v_r_398_, 0);
lean_inc(v_size_425_);
v___y_409_ = v___x_423_;
v___y_410_ = v___x_424_;
v___y_411_ = v_size_425_;
goto v___jp_408_;
}
else
{
lean_object* v___x_426_; 
v___x_426_ = lean_unsigned_to_nat(0u);
v___y_409_ = v___x_423_;
v___y_410_ = v___x_424_;
v___y_411_ = v___x_426_;
goto v___jp_408_;
}
}
}
}
}
else
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
lean_del_object(v___x_371_);
v___x_436_ = lean_nat_add(v___x_376_, v_size_377_);
v___x_437_ = lean_nat_add(v___x_436_, v_size_378_);
lean_dec(v_size_378_);
v___x_438_ = lean_nat_add(v___x_436_, v_size_394_);
lean_dec(v___x_436_);
lean_inc_ref(v_l_368_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 4, v_l_381_);
lean_ctor_set(v___x_392_, 3, v_l_368_);
lean_ctor_set(v___x_392_, 2, v_v_367_);
lean_ctor_set(v___x_392_, 1, v_k_366_);
lean_ctor_set(v___x_392_, 0, v___x_438_);
v___x_440_ = v___x_392_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_k_366_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v_v_367_);
lean_ctor_set(v_reuseFailAlloc_453_, 3, v_l_368_);
lean_ctor_set(v_reuseFailAlloc_453_, 4, v_l_381_);
v___x_440_ = v_reuseFailAlloc_453_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
v_isSharedCheck_447_ = !lean_is_exclusive(v_l_368_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; lean_object* v_unused_449_; lean_object* v_unused_450_; lean_object* v_unused_451_; lean_object* v_unused_452_; 
v_unused_448_ = lean_ctor_get(v_l_368_, 4);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_l_368_, 3);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_l_368_, 2);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v_l_368_, 1);
lean_dec(v_unused_451_);
v_unused_452_ = lean_ctor_get(v_l_368_, 0);
lean_dec(v_unused_452_);
v___x_442_ = v_l_368_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_dec(v_l_368_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 4, v_r_382_);
lean_ctor_set(v___x_442_, 3, v___x_440_);
lean_ctor_set(v___x_442_, 2, v_v_380_);
lean_ctor_set(v___x_442_, 1, v_k_379_);
lean_ctor_set(v___x_442_, 0, v___x_437_);
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_k_379_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v_v_380_);
lean_ctor_set(v_reuseFailAlloc_446_, 3, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_446_, 4, v_r_382_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_460_; 
v_l_460_ = lean_ctor_get(v_impl_375_, 3);
lean_inc(v_l_460_);
if (lean_obj_tag(v_l_460_) == 0)
{
lean_object* v_r_461_; lean_object* v_k_462_; lean_object* v_v_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_486_; 
v_r_461_ = lean_ctor_get(v_impl_375_, 4);
v_k_462_ = lean_ctor_get(v_impl_375_, 1);
v_v_463_ = lean_ctor_get(v_impl_375_, 2);
v_isSharedCheck_486_ = !lean_is_exclusive(v_impl_375_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; lean_object* v_unused_488_; 
v_unused_487_ = lean_ctor_get(v_impl_375_, 3);
lean_dec(v_unused_487_);
v_unused_488_ = lean_ctor_get(v_impl_375_, 0);
lean_dec(v_unused_488_);
v___x_465_ = v_impl_375_;
v_isShared_466_ = v_isSharedCheck_486_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_r_461_);
lean_inc(v_v_463_);
lean_inc(v_k_462_);
lean_dec(v_impl_375_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_486_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v_k_467_; lean_object* v_v_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_482_; 
v_k_467_ = lean_ctor_get(v_l_460_, 1);
v_v_468_ = lean_ctor_get(v_l_460_, 2);
v_isSharedCheck_482_ = !lean_is_exclusive(v_l_460_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; lean_object* v_unused_484_; lean_object* v_unused_485_; 
v_unused_483_ = lean_ctor_get(v_l_460_, 4);
lean_dec(v_unused_483_);
v_unused_484_ = lean_ctor_get(v_l_460_, 3);
lean_dec(v_unused_484_);
v_unused_485_ = lean_ctor_get(v_l_460_, 0);
lean_dec(v_unused_485_);
v___x_470_ = v_l_460_;
v_isShared_471_ = v_isSharedCheck_482_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_v_468_);
lean_inc(v_k_467_);
lean_dec(v_l_460_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_482_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_472_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_461_, 2);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 4, v_r_461_);
lean_ctor_set(v___x_470_, 3, v_r_461_);
lean_ctor_set(v___x_470_, 2, v_v_367_);
lean_ctor_set(v___x_470_, 1, v_k_366_);
lean_ctor_set(v___x_470_, 0, v___x_376_);
v___x_474_ = v___x_470_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_k_366_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_v_367_);
lean_ctor_set(v_reuseFailAlloc_481_, 3, v_r_461_);
lean_ctor_set(v_reuseFailAlloc_481_, 4, v_r_461_);
v___x_474_ = v_reuseFailAlloc_481_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_476_; 
lean_inc(v_r_461_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 3, v_r_461_);
lean_ctor_set(v___x_465_, 0, v___x_376_);
v___x_476_ = v___x_465_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_k_462_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_v_463_);
lean_ctor_set(v_reuseFailAlloc_480_, 3, v_r_461_);
lean_ctor_set(v_reuseFailAlloc_480_, 4, v_r_461_);
v___x_476_ = v_reuseFailAlloc_480_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_478_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 4, v___x_476_);
lean_ctor_set(v___x_371_, 3, v___x_474_);
lean_ctor_set(v___x_371_, 2, v_v_468_);
lean_ctor_set(v___x_371_, 1, v_k_467_);
lean_ctor_set(v___x_371_, 0, v___x_472_);
v___x_478_ = v___x_371_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_k_467_);
lean_ctor_set(v_reuseFailAlloc_479_, 2, v_v_468_);
lean_ctor_set(v_reuseFailAlloc_479_, 3, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_479_, 4, v___x_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
}
else
{
lean_object* v_r_489_; 
v_r_489_ = lean_ctor_get(v_impl_375_, 4);
lean_inc(v_r_489_);
if (lean_obj_tag(v_r_489_) == 0)
{
lean_object* v_k_490_; lean_object* v_v_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_502_; 
v_k_490_ = lean_ctor_get(v_impl_375_, 1);
v_v_491_ = lean_ctor_get(v_impl_375_, 2);
v_isSharedCheck_502_ = !lean_is_exclusive(v_impl_375_);
if (v_isSharedCheck_502_ == 0)
{
lean_object* v_unused_503_; lean_object* v_unused_504_; lean_object* v_unused_505_; 
v_unused_503_ = lean_ctor_get(v_impl_375_, 4);
lean_dec(v_unused_503_);
v_unused_504_ = lean_ctor_get(v_impl_375_, 3);
lean_dec(v_unused_504_);
v_unused_505_ = lean_ctor_get(v_impl_375_, 0);
lean_dec(v_unused_505_);
v___x_493_ = v_impl_375_;
v_isShared_494_ = v_isSharedCheck_502_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_v_491_);
lean_inc(v_k_490_);
lean_dec(v_impl_375_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_502_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_495_ = lean_unsigned_to_nat(3u);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 4, v_l_460_);
lean_ctor_set(v___x_493_, 2, v_v_367_);
lean_ctor_set(v___x_493_, 1, v_k_366_);
lean_ctor_set(v___x_493_, 0, v___x_376_);
v___x_497_ = v___x_493_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_k_366_);
lean_ctor_set(v_reuseFailAlloc_501_, 2, v_v_367_);
lean_ctor_set(v_reuseFailAlloc_501_, 3, v_l_460_);
lean_ctor_set(v_reuseFailAlloc_501_, 4, v_l_460_);
v___x_497_ = v_reuseFailAlloc_501_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v___x_499_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 4, v_r_489_);
lean_ctor_set(v___x_371_, 3, v___x_497_);
lean_ctor_set(v___x_371_, 2, v_v_491_);
lean_ctor_set(v___x_371_, 1, v_k_490_);
lean_ctor_set(v___x_371_, 0, v___x_495_);
v___x_499_ = v___x_371_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_495_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_k_490_);
lean_ctor_set(v_reuseFailAlloc_500_, 2, v_v_491_);
lean_ctor_set(v_reuseFailAlloc_500_, 3, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_500_, 4, v_r_489_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_506_ = lean_unsigned_to_nat(2u);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 4, v_impl_375_);
lean_ctor_set(v___x_371_, 3, v_r_489_);
lean_ctor_set(v___x_371_, 0, v___x_506_);
v___x_508_ = v___x_371_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_k_366_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v_v_367_);
lean_ctor_set(v_reuseFailAlloc_509_, 3, v_r_489_);
lean_ctor_set(v_reuseFailAlloc_509_, 4, v_impl_375_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
else
{
lean_object* v___x_511_; 
lean_dec(v_v_367_);
lean_dec(v_k_366_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 2, v_v_363_);
lean_ctor_set(v___x_371_, 1, v_k_362_);
v___x_511_ = v___x_371_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_size_365_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_k_362_);
lean_ctor_set(v_reuseFailAlloc_512_, 2, v_v_363_);
lean_ctor_set(v_reuseFailAlloc_512_, 3, v_l_368_);
lean_ctor_set(v_reuseFailAlloc_512_, 4, v_r_369_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
else
{
lean_object* v_impl_513_; lean_object* v___x_514_; 
lean_dec(v_size_365_);
v_impl_513_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_k_362_, v_v_363_, v_l_368_);
v___x_514_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_369_) == 0)
{
lean_object* v_size_515_; lean_object* v_size_516_; lean_object* v_k_517_; lean_object* v_v_518_; lean_object* v_l_519_; lean_object* v_r_520_; lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v_size_515_ = lean_ctor_get(v_r_369_, 0);
v_size_516_ = lean_ctor_get(v_impl_513_, 0);
lean_inc(v_size_516_);
v_k_517_ = lean_ctor_get(v_impl_513_, 1);
lean_inc(v_k_517_);
v_v_518_ = lean_ctor_get(v_impl_513_, 2);
lean_inc(v_v_518_);
v_l_519_ = lean_ctor_get(v_impl_513_, 3);
lean_inc(v_l_519_);
v_r_520_ = lean_ctor_get(v_impl_513_, 4);
lean_inc(v_r_520_);
v___x_521_ = lean_unsigned_to_nat(3u);
v___x_522_ = lean_nat_mul(v___x_521_, v_size_515_);
v___x_523_ = lean_nat_dec_lt(v___x_522_, v_size_516_);
lean_dec(v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
lean_dec(v_r_520_);
lean_dec(v_l_519_);
lean_dec(v_v_518_);
lean_dec(v_k_517_);
v___x_524_ = lean_nat_add(v___x_514_, v_size_516_);
lean_dec(v_size_516_);
v___x_525_ = lean_nat_add(v___x_524_, v_size_515_);
lean_dec(v___x_524_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 3, v_impl_513_);
lean_ctor_set(v___x_371_, 0, v___x_525_);
v___x_527_ = v___x_371_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_k_366_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v_v_367_);
lean_ctor_set(v_reuseFailAlloc_528_, 3, v_impl_513_);
lean_ctor_set(v_reuseFailAlloc_528_, 4, v_r_369_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
else
{
lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_594_; 
v_isSharedCheck_594_ = !lean_is_exclusive(v_impl_513_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; lean_object* v_unused_596_; lean_object* v_unused_597_; lean_object* v_unused_598_; lean_object* v_unused_599_; 
v_unused_595_ = lean_ctor_get(v_impl_513_, 4);
lean_dec(v_unused_595_);
v_unused_596_ = lean_ctor_get(v_impl_513_, 3);
lean_dec(v_unused_596_);
v_unused_597_ = lean_ctor_get(v_impl_513_, 2);
lean_dec(v_unused_597_);
v_unused_598_ = lean_ctor_get(v_impl_513_, 1);
lean_dec(v_unused_598_);
v_unused_599_ = lean_ctor_get(v_impl_513_, 0);
lean_dec(v_unused_599_);
v___x_530_ = v_impl_513_;
v_isShared_531_ = v_isSharedCheck_594_;
goto v_resetjp_529_;
}
else
{
lean_dec(v_impl_513_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_594_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v_size_532_; lean_object* v_size_533_; lean_object* v_k_534_; lean_object* v_v_535_; lean_object* v_l_536_; lean_object* v_r_537_; lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v_size_532_ = lean_ctor_get(v_l_519_, 0);
v_size_533_ = lean_ctor_get(v_r_520_, 0);
v_k_534_ = lean_ctor_get(v_r_520_, 1);
v_v_535_ = lean_ctor_get(v_r_520_, 2);
v_l_536_ = lean_ctor_get(v_r_520_, 3);
v_r_537_ = lean_ctor_get(v_r_520_, 4);
v___x_538_ = lean_unsigned_to_nat(2u);
v___x_539_ = lean_nat_mul(v___x_538_, v_size_532_);
v___x_540_ = lean_nat_dec_lt(v_size_533_, v___x_539_);
lean_dec(v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_569_; 
lean_inc(v_r_537_);
lean_inc(v_l_536_);
lean_inc(v_v_535_);
lean_inc(v_k_534_);
v_isSharedCheck_569_ = !lean_is_exclusive(v_r_520_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; lean_object* v_unused_571_; lean_object* v_unused_572_; lean_object* v_unused_573_; lean_object* v_unused_574_; 
v_unused_570_ = lean_ctor_get(v_r_520_, 4);
lean_dec(v_unused_570_);
v_unused_571_ = lean_ctor_get(v_r_520_, 3);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_r_520_, 2);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_r_520_, 1);
lean_dec(v_unused_573_);
v_unused_574_ = lean_ctor_get(v_r_520_, 0);
lean_dec(v_unused_574_);
v___x_542_ = v_r_520_;
v_isShared_543_ = v_isSharedCheck_569_;
goto v_resetjp_541_;
}
else
{
lean_dec(v_r_520_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_569_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___x_557_; lean_object* v___y_559_; 
v___x_544_ = lean_nat_add(v___x_514_, v_size_516_);
lean_dec(v_size_516_);
v___x_545_ = lean_nat_add(v___x_544_, v_size_515_);
lean_dec(v___x_544_);
v___x_557_ = lean_nat_add(v___x_514_, v_size_532_);
if (lean_obj_tag(v_l_536_) == 0)
{
lean_object* v_size_567_; 
v_size_567_ = lean_ctor_get(v_l_536_, 0);
lean_inc(v_size_567_);
v___y_559_ = v_size_567_;
goto v___jp_558_;
}
else
{
lean_object* v___x_568_; 
v___x_568_ = lean_unsigned_to_nat(0u);
v___y_559_ = v___x_568_;
goto v___jp_558_;
}
v___jp_546_:
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = lean_nat_add(v___y_548_, v___y_549_);
lean_dec(v___y_549_);
lean_dec(v___y_548_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 4, v_r_369_);
lean_ctor_set(v___x_542_, 3, v_r_537_);
lean_ctor_set(v___x_542_, 2, v_v_367_);
lean_ctor_set(v___x_542_, 1, v_k_366_);
lean_ctor_set(v___x_542_, 0, v___x_550_);
v___x_552_ = v___x_542_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_k_366_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_v_367_);
lean_ctor_set(v_reuseFailAlloc_556_, 3, v_r_537_);
lean_ctor_set(v_reuseFailAlloc_556_, 4, v_r_369_);
v___x_552_ = v_reuseFailAlloc_556_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_554_; 
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 4, v___x_552_);
lean_ctor_set(v___x_530_, 3, v___y_547_);
lean_ctor_set(v___x_530_, 2, v_v_535_);
lean_ctor_set(v___x_530_, 1, v_k_534_);
lean_ctor_set(v___x_530_, 0, v___x_545_);
v___x_554_ = v___x_530_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_k_534_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_v_535_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v___y_547_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
v___jp_558_:
{
lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_560_ = lean_nat_add(v___x_557_, v___y_559_);
lean_dec(v___y_559_);
lean_dec(v___x_557_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 4, v_l_536_);
lean_ctor_set(v___x_371_, 3, v_l_519_);
lean_ctor_set(v___x_371_, 2, v_v_518_);
lean_ctor_set(v___x_371_, 1, v_k_517_);
lean_ctor_set(v___x_371_, 0, v___x_560_);
v___x_562_ = v___x_371_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_k_517_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v_v_518_);
lean_ctor_set(v_reuseFailAlloc_566_, 3, v_l_519_);
lean_ctor_set(v_reuseFailAlloc_566_, 4, v_l_536_);
v___x_562_ = v_reuseFailAlloc_566_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; 
v___x_563_ = lean_nat_add(v___x_514_, v_size_515_);
if (lean_obj_tag(v_r_537_) == 0)
{
lean_object* v_size_564_; 
v_size_564_ = lean_ctor_get(v_r_537_, 0);
lean_inc(v_size_564_);
v___y_547_ = v___x_562_;
v___y_548_ = v___x_563_;
v___y_549_ = v_size_564_;
goto v___jp_546_;
}
else
{
lean_object* v___x_565_; 
v___x_565_ = lean_unsigned_to_nat(0u);
v___y_547_ = v___x_562_;
v___y_548_ = v___x_563_;
v___y_549_ = v___x_565_;
goto v___jp_546_;
}
}
}
}
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
lean_del_object(v___x_371_);
v___x_575_ = lean_nat_add(v___x_514_, v_size_516_);
lean_dec(v_size_516_);
v___x_576_ = lean_nat_add(v___x_575_, v_size_515_);
lean_dec(v___x_575_);
v___x_577_ = lean_nat_add(v___x_514_, v_size_515_);
v___x_578_ = lean_nat_add(v___x_577_, v_size_533_);
lean_dec(v___x_577_);
lean_inc_ref(v_r_369_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 4, v_r_369_);
lean_ctor_set(v___x_530_, 3, v_r_520_);
lean_ctor_set(v___x_530_, 2, v_v_367_);
lean_ctor_set(v___x_530_, 1, v_k_366_);
lean_ctor_set(v___x_530_, 0, v___x_578_);
v___x_580_ = v___x_530_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_k_366_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_v_367_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v_r_520_);
lean_ctor_set(v_reuseFailAlloc_593_, 4, v_r_369_);
v___x_580_ = v_reuseFailAlloc_593_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
v_isSharedCheck_587_ = !lean_is_exclusive(v_r_369_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; lean_object* v_unused_589_; lean_object* v_unused_590_; lean_object* v_unused_591_; lean_object* v_unused_592_; 
v_unused_588_ = lean_ctor_get(v_r_369_, 4);
lean_dec(v_unused_588_);
v_unused_589_ = lean_ctor_get(v_r_369_, 3);
lean_dec(v_unused_589_);
v_unused_590_ = lean_ctor_get(v_r_369_, 2);
lean_dec(v_unused_590_);
v_unused_591_ = lean_ctor_get(v_r_369_, 1);
lean_dec(v_unused_591_);
v_unused_592_ = lean_ctor_get(v_r_369_, 0);
lean_dec(v_unused_592_);
v___x_582_ = v_r_369_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_dec(v_r_369_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 4, v___x_580_);
lean_ctor_set(v___x_582_, 3, v_l_519_);
lean_ctor_set(v___x_582_, 2, v_v_518_);
lean_ctor_set(v___x_582_, 1, v_k_517_);
lean_ctor_set(v___x_582_, 0, v___x_576_);
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_k_517_);
lean_ctor_set(v_reuseFailAlloc_586_, 2, v_v_518_);
lean_ctor_set(v_reuseFailAlloc_586_, 3, v_l_519_);
lean_ctor_set(v_reuseFailAlloc_586_, 4, v___x_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_600_; 
v_l_600_ = lean_ctor_get(v_impl_513_, 3);
lean_inc(v_l_600_);
if (lean_obj_tag(v_l_600_) == 0)
{
lean_object* v_r_601_; lean_object* v_k_602_; lean_object* v_v_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_614_; 
v_r_601_ = lean_ctor_get(v_impl_513_, 4);
v_k_602_ = lean_ctor_get(v_impl_513_, 1);
v_v_603_ = lean_ctor_get(v_impl_513_, 2);
v_isSharedCheck_614_ = !lean_is_exclusive(v_impl_513_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; lean_object* v_unused_616_; 
v_unused_615_ = lean_ctor_get(v_impl_513_, 3);
lean_dec(v_unused_615_);
v_unused_616_ = lean_ctor_get(v_impl_513_, 0);
lean_dec(v_unused_616_);
v___x_605_ = v_impl_513_;
v_isShared_606_ = v_isSharedCheck_614_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_r_601_);
lean_inc(v_v_603_);
lean_inc(v_k_602_);
lean_dec(v_impl_513_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_614_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_607_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_601_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 3, v_r_601_);
lean_ctor_set(v___x_605_, 2, v_v_367_);
lean_ctor_set(v___x_605_, 1, v_k_366_);
lean_ctor_set(v___x_605_, 0, v___x_514_);
v___x_609_ = v___x_605_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_k_366_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_v_367_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v_r_601_);
lean_ctor_set(v_reuseFailAlloc_613_, 4, v_r_601_);
v___x_609_ = v_reuseFailAlloc_613_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_611_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 4, v___x_609_);
lean_ctor_set(v___x_371_, 3, v_l_600_);
lean_ctor_set(v___x_371_, 2, v_v_603_);
lean_ctor_set(v___x_371_, 1, v_k_602_);
lean_ctor_set(v___x_371_, 0, v___x_607_);
v___x_611_ = v___x_371_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_k_602_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_v_603_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v_l_600_);
lean_ctor_set(v_reuseFailAlloc_612_, 4, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
else
{
lean_object* v_r_617_; 
v_r_617_ = lean_ctor_get(v_impl_513_, 4);
lean_inc(v_r_617_);
if (lean_obj_tag(v_r_617_) == 0)
{
lean_object* v_k_618_; lean_object* v_v_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_642_; 
v_k_618_ = lean_ctor_get(v_impl_513_, 1);
v_v_619_ = lean_ctor_get(v_impl_513_, 2);
v_isSharedCheck_642_ = !lean_is_exclusive(v_impl_513_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; lean_object* v_unused_644_; lean_object* v_unused_645_; 
v_unused_643_ = lean_ctor_get(v_impl_513_, 4);
lean_dec(v_unused_643_);
v_unused_644_ = lean_ctor_get(v_impl_513_, 3);
lean_dec(v_unused_644_);
v_unused_645_ = lean_ctor_get(v_impl_513_, 0);
lean_dec(v_unused_645_);
v___x_621_ = v_impl_513_;
v_isShared_622_ = v_isSharedCheck_642_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_v_619_);
lean_inc(v_k_618_);
lean_dec(v_impl_513_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_642_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v_k_623_; lean_object* v_v_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_638_; 
v_k_623_ = lean_ctor_get(v_r_617_, 1);
v_v_624_ = lean_ctor_get(v_r_617_, 2);
v_isSharedCheck_638_ = !lean_is_exclusive(v_r_617_);
if (v_isSharedCheck_638_ == 0)
{
lean_object* v_unused_639_; lean_object* v_unused_640_; lean_object* v_unused_641_; 
v_unused_639_ = lean_ctor_get(v_r_617_, 4);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v_r_617_, 3);
lean_dec(v_unused_640_);
v_unused_641_ = lean_ctor_get(v_r_617_, 0);
lean_dec(v_unused_641_);
v___x_626_ = v_r_617_;
v_isShared_627_ = v_isSharedCheck_638_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_v_624_);
lean_inc(v_k_623_);
lean_dec(v_r_617_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_638_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_628_ = lean_unsigned_to_nat(3u);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 4, v_l_600_);
lean_ctor_set(v___x_626_, 3, v_l_600_);
lean_ctor_set(v___x_626_, 2, v_v_619_);
lean_ctor_set(v___x_626_, 1, v_k_618_);
lean_ctor_set(v___x_626_, 0, v___x_514_);
v___x_630_ = v___x_626_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_k_618_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_v_619_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_l_600_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v_l_600_);
v___x_630_ = v_reuseFailAlloc_637_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_632_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 4, v_l_600_);
lean_ctor_set(v___x_621_, 2, v_v_367_);
lean_ctor_set(v___x_621_, 1, v_k_366_);
lean_ctor_set(v___x_621_, 0, v___x_514_);
v___x_632_ = v___x_621_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_k_366_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_v_367_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_l_600_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v_l_600_);
v___x_632_ = v_reuseFailAlloc_636_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_634_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 4, v___x_632_);
lean_ctor_set(v___x_371_, 3, v___x_630_);
lean_ctor_set(v___x_371_, 2, v_v_624_);
lean_ctor_set(v___x_371_, 1, v_k_623_);
lean_ctor_set(v___x_371_, 0, v___x_628_);
v___x_634_ = v___x_371_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_k_623_);
lean_ctor_set(v_reuseFailAlloc_635_, 2, v_v_624_);
lean_ctor_set(v_reuseFailAlloc_635_, 3, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_635_, 4, v___x_632_);
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
}
}
else
{
lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_646_ = lean_unsigned_to_nat(2u);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 4, v_r_617_);
lean_ctor_set(v___x_371_, 3, v_impl_513_);
lean_ctor_set(v___x_371_, 0, v___x_646_);
v___x_648_ = v___x_371_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_k_366_);
lean_ctor_set(v_reuseFailAlloc_649_, 2, v_v_367_);
lean_ctor_set(v_reuseFailAlloc_649_, 3, v_impl_513_);
lean_ctor_set(v_reuseFailAlloc_649_, 4, v_r_617_);
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
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v_k_362_);
lean_ctor_set(v___x_652_, 2, v_v_363_);
lean_ctor_set(v___x_652_, 3, v_t_364_);
lean_ctor_set(v___x_652_, 4, v_t_364_);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(lean_object* v_a_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; lean_object* v_fst_661_; lean_object* v_snd_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_695_; 
v___x_660_ = lean_st_ref_get(v___y_654_);
v_fst_661_ = lean_ctor_get(v_a_653_, 0);
v_snd_662_ = lean_ctor_get(v_a_653_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_a_653_);
if (v_isSharedCheck_695_ == 0)
{
v___x_664_ = v_a_653_;
v_isShared_665_ = v_isSharedCheck_695_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_snd_662_);
lean_inc(v_fst_661_);
lean_dec(v_a_653_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_695_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; 
lean_inc(v_snd_662_);
v___x_666_ = l_Lean_Meta_Grind_Goal_getENode(v___x_660_, v_snd_662_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___x_660_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_686_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_686_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_686_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_686_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v_self_671_; lean_object* v_target_x3f_672_; lean_object* v_idx_673_; lean_object* v___x_674_; 
v_self_671_ = lean_ctor_get(v_a_667_, 0);
lean_inc_ref(v_self_671_);
v_target_x3f_672_ = lean_ctor_get(v_a_667_, 4);
lean_inc(v_target_x3f_672_);
v_idx_673_ = lean_ctor_get(v_a_667_, 7);
lean_inc(v_idx_673_);
lean_dec(v_a_667_);
v___x_674_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_idx_673_, v_self_671_, v_fst_661_);
if (lean_obj_tag(v_target_x3f_672_) == 1)
{
lean_object* v_val_675_; lean_object* v___x_677_; 
lean_del_object(v___x_669_);
lean_dec(v_snd_662_);
v_val_675_ = lean_ctor_get(v_target_x3f_672_, 0);
lean_inc(v_val_675_);
lean_dec_ref_known(v_target_x3f_672_, 1);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 1, v_val_675_);
lean_ctor_set(v___x_664_, 0, v___x_674_);
v___x_677_ = v___x_664_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_val_675_);
v___x_677_ = v_reuseFailAlloc_679_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
v_a_653_ = v___x_677_;
goto _start;
}
}
else
{
lean_object* v___x_681_; 
lean_dec(v_target_x3f_672_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_674_);
v___x_681_ = v___x_664_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_snd_662_);
v___x_681_ = v_reuseFailAlloc_685_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_683_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_681_);
v___x_683_ = v___x_669_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_del_object(v___x_664_);
lean_dec(v_snd_662_);
lean_dec(v_fst_661_);
v_a_687_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_666_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_666_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg___boxed(lean_object* v_a_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(v_a_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
return v_res_703_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_704_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_705_ = lean_unsigned_to_nat(2u);
v___x_706_ = lean_unsigned_to_nat(89u);
v___x_707_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__1));
v___x_708_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_709_ = l_mkPanicMessageWithDecl(v___x_708_, v___x_707_, v___x_706_, v___x_705_, v___x_704_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(lean_object* v_lhs_710_, lean_object* v_rhs_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v_visited_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_visited_723_ = lean_box(1);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v_visited_723_);
lean_ctor_set(v___x_724_, 1, v_lhs_710_);
v___x_725_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(v___x_724_, v_a_712_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v_fst_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_756_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
v_fst_727_ = lean_ctor_get(v_a_726_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v_a_726_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; 
v_unused_757_ = lean_ctor_get(v_a_726_, 1);
lean_dec(v_unused_757_);
v___x_729_ = v_a_726_;
v_isShared_730_ = v_isSharedCheck_756_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_fst_727_);
lean_dec(v_a_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_756_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_731_ = lean_box(0);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v_rhs_711_);
lean_ctor_set(v___x_729_, 0, v___x_731_);
v___x_733_ = v___x_729_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_rhs_711_);
v___x_733_ = v_reuseFailAlloc_755_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; 
v___x_734_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(v_fst_727_, v___x_733_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
lean_dec(v_fst_727_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_746_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_746_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_746_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_746_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v_fst_739_; 
v_fst_739_ = lean_ctor_get(v_a_735_, 0);
lean_inc(v_fst_739_);
lean_dec(v_a_735_);
if (lean_obj_tag(v_fst_739_) == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; 
lean_del_object(v___x_737_);
v___x_740_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0);
v___x_741_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_740_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
return v___x_741_;
}
else
{
lean_object* v_val_742_; lean_object* v___x_744_; 
v_val_742_ = lean_ctor_get(v_fst_739_, 0);
lean_inc(v_val_742_);
lean_dec_ref_known(v_fst_739_, 1);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v_val_742_);
v___x_744_ = v___x_737_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_val_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
v_a_747_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_734_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_734_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec_ref(v_rhs_711_);
v_a_758_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_725_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_725_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___boxed(lean_object* v_lhs_766_, lean_object* v_rhs_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(v_lhs_766_, v_rhs_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
lean_dec(v_a_769_);
lean_dec(v_a_768_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0(lean_object* v_00_u03b2_780_, lean_object* v_k_781_, lean_object* v_v_782_, lean_object* v_t_783_, lean_object* v_hl_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_k_781_, v_v_782_, v_t_783_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1(lean_object* v_inst_786_, lean_object* v_a_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(v_a_787_, v___y_788_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___boxed(lean_object* v_inst_800_, lean_object* v_a_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1(v_inst_800_, v_a_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec(v___y_802_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2(lean_object* v_00_u03b4_814_, lean_object* v_t_815_, lean_object* v_k_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(v_t_815_, v_k_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___boxed(lean_object* v_00_u03b4_818_, lean_object* v_t_819_, lean_object* v_k_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2(v_00_u03b4_818_, v_t_819_, v_k_820_);
lean_dec(v_k_820_);
lean_dec(v_t_819_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4(lean_object* v___x_822_, lean_object* v_inst_823_, lean_object* v_a_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(v___x_822_, v_a_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___boxed(lean_object* v___x_837_, lean_object* v_inst_838_, lean_object* v_a_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4(v___x_837_, v_inst_838_, v_a_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec(v___y_840_);
lean_dec(v___x_837_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(lean_object* v_info_852_, lean_object* v_lhs_853_, lean_object* v_rhs_854_, lean_object* v_i_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
uint8_t v___x_867_; 
v___x_867_ = l_Lean_Expr_isApp(v_lhs_853_);
if (v___x_867_ == 0)
{
uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
lean_dec(v_i_855_);
lean_dec_ref(v_rhs_854_);
lean_dec_ref(v_lhs_853_);
v___x_868_ = 1;
v___x_869_ = lean_box(v___x_868_);
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
return v___x_870_;
}
else
{
lean_object* v_a_u2081_871_; lean_object* v_a_u2082_872_; lean_object* v___x_873_; lean_object* v_i_874_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; size_t v___x_889_; size_t v___x_890_; uint8_t v___x_891_; 
v_a_u2081_871_ = l_Lean_Expr_appArg_x21(v_lhs_853_);
v_a_u2082_872_ = l_Lean_Expr_appArg_x21(v_rhs_854_);
v___x_873_ = lean_unsigned_to_nat(1u);
v_i_874_ = lean_nat_sub(v_i_855_, v___x_873_);
lean_dec(v_i_855_);
v___x_889_ = lean_ptr_addr(v_a_u2081_871_);
lean_dec_ref(v_a_u2081_871_);
v___x_890_ = lean_ptr_addr(v_a_u2082_872_);
lean_dec_ref(v_a_u2082_872_);
v___x_891_ = lean_usize_dec_eq(v___x_889_, v___x_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_892_ = lean_array_get_size(v_info_852_);
v___x_893_ = lean_nat_dec_lt(v_i_874_, v___x_892_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; lean_object* v___x_895_; 
lean_dec(v_i_874_);
lean_dec_ref(v_rhs_854_);
lean_dec_ref(v_lhs_853_);
v___x_894_ = lean_box(v___x_893_);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
return v___x_895_;
}
else
{
lean_object* v___x_896_; uint8_t v_hasFwdDeps_897_; 
v___x_896_ = lean_array_fget_borrowed(v_info_852_, v_i_874_);
v_hasFwdDeps_897_ = lean_ctor_get_uint8(v___x_896_, sizeof(void*)*1 + 1);
if (v_hasFwdDeps_897_ == 0)
{
v___y_876_ = v_a_856_;
v___y_877_ = v_a_857_;
v___y_878_ = v_a_858_;
v___y_879_ = v_a_859_;
v___y_880_ = v_a_860_;
v___y_881_ = v_a_861_;
v___y_882_ = v_a_862_;
v___y_883_ = v_a_863_;
v___y_884_ = v_a_864_;
v___y_885_ = v_a_865_;
goto v___jp_875_;
}
else
{
lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec(v_i_874_);
lean_dec_ref(v_rhs_854_);
lean_dec_ref(v_lhs_853_);
v___x_898_ = lean_box(v___x_891_);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
}
else
{
v___y_876_ = v_a_856_;
v___y_877_ = v_a_857_;
v___y_878_ = v_a_858_;
v___y_879_ = v_a_859_;
v___y_880_ = v_a_860_;
v___y_881_ = v_a_861_;
v___y_882_ = v_a_862_;
v___y_883_ = v_a_863_;
v___y_884_ = v_a_864_;
v___y_885_ = v_a_865_;
goto v___jp_875_;
}
v___jp_875_:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = l_Lean_Expr_appFn_x21(v_lhs_853_);
lean_dec_ref(v_lhs_853_);
v___x_887_ = l_Lean_Expr_appFn_x21(v_rhs_854_);
lean_dec_ref(v_rhs_854_);
v_lhs_853_ = v___x_886_;
v_rhs_854_ = v___x_887_;
v_i_855_ = v_i_874_;
v_a_856_ = v___y_876_;
v_a_857_ = v___y_877_;
v_a_858_ = v___y_878_;
v_a_859_ = v___y_879_;
v_a_860_ = v___y_880_;
v_a_861_ = v___y_881_;
v_a_862_ = v___y_882_;
v_a_863_ = v___y_883_;
v_a_864_ = v___y_884_;
v_a_865_ = v___y_885_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop___boxed(lean_object* v_info_900_, lean_object* v_lhs_901_, lean_object* v_rhs_902_, lean_object* v_i_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(v_info_900_, v_lhs_901_, v_rhs_902_, v_i_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
lean_dec(v_a_904_);
lean_dec_ref(v_info_900_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(lean_object* v_lhs_916_, lean_object* v_rhs_917_, lean_object* v_f_918_, lean_object* v_g_919_, lean_object* v_numArgs_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
size_t v___x_932_; size_t v___x_933_; uint8_t v___x_934_; 
v___x_932_ = lean_ptr_addr(v_f_918_);
v___x_933_ = lean_ptr_addr(v_g_919_);
v___x_934_ = lean_usize_dec_eq(v___x_932_, v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec(v_numArgs_920_);
lean_dec_ref(v_f_918_);
lean_dec_ref(v_rhs_917_);
lean_dec_ref(v_lhs_916_);
v___x_935_ = lean_box(v___x_934_);
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
return v___x_936_;
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = lean_box(0);
v___x_938_ = l_Lean_Meta_getFunInfo(v_f_918_, v___x_937_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v_paramInfo_940_; lean_object* v___x_941_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_939_);
lean_dec_ref_known(v___x_938_, 1);
v_paramInfo_940_ = lean_ctor_get(v_a_939_, 0);
lean_inc_ref(v_paramInfo_940_);
lean_dec(v_a_939_);
v___x_941_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(v_paramInfo_940_, v_lhs_916_, v_rhs_917_, v_numArgs_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
lean_dec_ref(v_paramInfo_940_);
return v___x_941_;
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec(v_numArgs_920_);
lean_dec_ref(v_rhs_917_);
lean_dec_ref(v_lhs_916_);
v_a_942_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_938_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_938_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget___boxed(lean_object* v_lhs_950_, lean_object* v_rhs_951_, lean_object* v_f_952_, lean_object* v_g_953_, lean_object* v_numArgs_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(v_lhs_950_, v_rhs_951_, v_f_952_, v_g_953_, v_numArgs_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_g_953_);
return v_res_966_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0(void){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(lean_object* v_msg_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_980_; lean_object* v___x_95198__overap_981_; lean_object* v___x_982_; 
v___x_980_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0);
v___x_95198__overap_981_ = lean_panic_fn_borrowed(v___x_980_, v_msg_968_);
lean_inc(v___y_978_);
lean_inc_ref(v___y_977_);
lean_inc(v___y_976_);
lean_inc_ref(v___y_975_);
lean_inc(v___y_974_);
lean_inc_ref(v___y_973_);
lean_inc(v___y_972_);
lean_inc_ref(v___y_971_);
lean_inc(v___y_970_);
lean_inc(v___y_969_);
v___x_982_ = lean_apply_11(v___x_95198__overap_981_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, lean_box(0));
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___boxed(lean_object* v_msg_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v_msg_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec(v___y_984_);
return v_res_995_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = l_Lean_maxRecDepthErrorMessage;
v___x_1002_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3);
v___x_1004_ = l_Lean_MessageData_ofFormat(v___x_1003_);
return v___x_1004_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4);
v___x_1006_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__2));
v___x_1007_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___x_1005_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(lean_object* v_ref_1008_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v_ref_1008_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___boxed(lean_object* v_ref_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1013_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0(lean_object* v_k_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v_b_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; 
lean_inc(v___y_1027_);
lean_inc_ref(v___y_1026_);
lean_inc(v___y_1025_);
lean_inc_ref(v___y_1024_);
lean_inc(v___y_1022_);
lean_inc_ref(v___y_1021_);
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
lean_inc(v___y_1018_);
lean_inc(v___y_1017_);
v___x_1029_ = lean_apply_12(v_k_1016_, v_b_1023_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, lean_box(0));
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0___boxed(lean_object* v_k_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v_b_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0(v_k_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v_b_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec(v___y_1031_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(lean_object* v_name_1044_, uint8_t v_bi_1045_, lean_object* v_type_1046_, lean_object* v_k_1047_, uint8_t v_kind_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___f_1060_; lean_object* v___x_1061_; 
lean_inc(v___y_1054_);
lean_inc_ref(v___y_1053_);
lean_inc(v___y_1052_);
lean_inc_ref(v___y_1051_);
lean_inc(v___y_1050_);
lean_inc(v___y_1049_);
v___f_1060_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_1060_, 0, v_k_1047_);
lean_closure_set(v___f_1060_, 1, v___y_1049_);
lean_closure_set(v___f_1060_, 2, v___y_1050_);
lean_closure_set(v___f_1060_, 3, v___y_1051_);
lean_closure_set(v___f_1060_, 4, v___y_1052_);
lean_closure_set(v___f_1060_, 5, v___y_1053_);
lean_closure_set(v___f_1060_, 6, v___y_1054_);
v___x_1061_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1044_, v_bi_1045_, v_type_1046_, v___f_1060_, v_kind_1048_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
if (lean_obj_tag(v___x_1061_) == 0)
{
return v___x_1061_;
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___boxed(lean_object* v_name_1070_, lean_object* v_bi_1071_, lean_object* v_type_1072_, lean_object* v_k_1073_, lean_object* v_kind_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
uint8_t v_bi_boxed_1086_; uint8_t v_kind_boxed_1087_; lean_object* v_res_1088_; 
v_bi_boxed_1086_ = lean_unbox(v_bi_1071_);
v_kind_boxed_1087_ = lean_unbox(v_kind_1074_);
v_res_1088_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_1070_, v_bi_boxed_1086_, v_type_1072_, v_k_1073_, v_kind_boxed_1087_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec(v___y_1075_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(lean_object* v_name_1089_, lean_object* v_type_1090_, lean_object* v_k_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
uint8_t v___x_1103_; uint8_t v___x_1104_; lean_object* v___x_1105_; 
v___x_1103_ = 0;
v___x_1104_ = 0;
v___x_1105_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_1089_, v___x_1103_, v_type_1090_, v_k_1091_, v___x_1104_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg___boxed(lean_object* v_name_1106_, lean_object* v_type_1107_, lean_object* v_k_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_name_1106_, v_type_1107_, v_k_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec(v___y_1109_);
return v_res_1120_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1121_; lean_object* v_dummy_1122_; 
v___x_1121_ = lean_box(0);
v_dummy_1122_ = l_Lean_Expr_sort___override(v___x_1121_);
return v_dummy_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0(lean_object* v_numArgs_1123_, lean_object* v_rhs_1124_, lean_object* v_lhs_1125_, uint8_t v___x_1126_, uint8_t v___x_1127_, lean_object* v_x_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_dummy_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_dummy_1140_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0);
lean_inc(v_numArgs_1123_);
v___x_1141_ = lean_mk_array(v_numArgs_1123_, v_dummy_1140_);
v___x_1142_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_numArgs_1123_, v_rhs_1124_, v___x_1141_);
lean_inc_ref(v_x_1128_);
v___x_1143_ = l_Lean_mkAppN(v_x_1128_, v___x_1142_);
lean_dec_ref(v___x_1142_);
v___x_1144_ = l_Lean_Meta_mkHEq(v_lhs_1125_, v___x_1143_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; lean_object* v___x_1150_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1144_, 1);
v___x_1146_ = lean_unsigned_to_nat(1u);
v___x_1147_ = lean_mk_empty_array_with_capacity(v___x_1146_);
v___x_1148_ = lean_array_push(v___x_1147_, v_x_1128_);
v___x_1149_ = 1;
v___x_1150_ = l_Lean_Meta_mkLambdaFVars(v___x_1148_, v_a_1145_, v___x_1126_, v___x_1127_, v___x_1126_, v___x_1127_, v___x_1149_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
lean_dec_ref(v___x_1148_);
return v___x_1150_;
}
else
{
lean_dec_ref(v_x_1128_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___boxed(lean_object** _args){
lean_object* v_numArgs_1151_ = _args[0];
lean_object* v_rhs_1152_ = _args[1];
lean_object* v_lhs_1153_ = _args[2];
lean_object* v___x_1154_ = _args[3];
lean_object* v___x_1155_ = _args[4];
lean_object* v_x_1156_ = _args[5];
lean_object* v___y_1157_ = _args[6];
lean_object* v___y_1158_ = _args[7];
lean_object* v___y_1159_ = _args[8];
lean_object* v___y_1160_ = _args[9];
lean_object* v___y_1161_ = _args[10];
lean_object* v___y_1162_ = _args[11];
lean_object* v___y_1163_ = _args[12];
lean_object* v___y_1164_ = _args[13];
lean_object* v___y_1165_ = _args[14];
lean_object* v___y_1166_ = _args[15];
lean_object* v___y_1167_ = _args[16];
_start:
{
uint8_t v___x_102923__boxed_1168_; uint8_t v___x_102924__boxed_1169_; lean_object* v_res_1170_; 
v___x_102923__boxed_1168_ = lean_unbox(v___x_1154_);
v___x_102924__boxed_1169_ = lean_unbox(v___x_1155_);
v_res_1170_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0(v_numArgs_1151_, v_rhs_1152_, v_lhs_1153_, v___x_102923__boxed_1168_, v___x_102924__boxed_1169_, v_x_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec(v___y_1157_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_spec__13(lean_object* v_msg_1171_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = l_Lean_instInhabitedExpr;
v___x_1173_ = lean_panic_fn_borrowed(v___x_1172_, v_msg_1171_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(lean_object* v_msgData_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; lean_object* v_env_1181_; lean_object* v___x_1182_; lean_object* v_toCold_1183_; lean_object* v_mctx_1184_; lean_object* v_lctx_1185_; lean_object* v_options_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1180_ = lean_st_ref_get(v___y_1178_);
v_env_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc_ref(v_env_1181_);
lean_dec(v___x_1180_);
v___x_1182_ = lean_st_ref_get(v___y_1176_);
v_toCold_1183_ = lean_ctor_get(v___y_1177_, 0);
v_mctx_1184_ = lean_ctor_get(v___x_1182_, 0);
lean_inc_ref(v_mctx_1184_);
lean_dec(v___x_1182_);
v_lctx_1185_ = lean_ctor_get(v___y_1175_, 2);
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
lean_ctor_set(v___x_1188_, 1, v_msgData_1174_);
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
lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; uint8_t v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; uint8_t v___y_1361_; lean_object* v_toCold_1397_; lean_object* v_currRecDepth_1398_; lean_object* v_ref_1399_; uint8_t v_diag_1400_; uint8_t v_suppressElabErrors_1401_; lean_object* v_maxRecDepth_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; lean_object* v___x_1434_; uint8_t v___x_1435_; 
v_toCold_1397_ = lean_ctor_get(v_a_1322_, 0);
v_currRecDepth_1398_ = lean_ctor_get(v_a_1322_, 1);
v_ref_1399_ = lean_ctor_get(v_a_1322_, 2);
v_diag_1400_ = lean_ctor_get_uint8(v_a_1322_, sizeof(void*)*3);
v_suppressElabErrors_1401_ = lean_ctor_get_uint8(v_a_1322_, sizeof(void*)*3 + 1);
v_maxRecDepth_1402_ = lean_ctor_get(v_toCold_1397_, 3);
v___x_1403_ = l_Lean_Expr_cleanupAnnotations(v_lhs_1312_);
v___x_1404_ = l_Lean_Expr_isApp(v___x_1403_);
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = lean_nat_dec_eq(v_maxRecDepth_1402_, v___x_1434_);
if (v___x_1435_ == 0)
{
uint8_t v___x_1436_; 
v___x_1436_ = lean_nat_dec_eq(v_currRecDepth_1398_, v_maxRecDepth_1402_);
if (v___x_1436_ == 0)
{
goto v___jp_1405_;
}
else
{
lean_object* v___x_1437_; 
lean_dec_ref(v___x_1403_);
lean_dec_ref(v_rhs_1313_);
lean_inc(v_ref_1399_);
v___x_1437_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1399_);
return v___x_1437_;
}
}
else
{
goto v___jp_1405_;
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
if (v___y_1361_ == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_dec_ref(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1352_);
v___x_1362_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4);
v___x_1363_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1362_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v___y_1353_, v_a_1323_);
lean_dec_ref(v___y_1353_);
return v___x_1363_;
}
else
{
lean_object* v___x_1364_; size_t v___x_1365_; size_t v___x_1366_; uint8_t v___x_1367_; 
v___x_1364_ = l_Lean_Expr_constLevels_x21(v___y_1354_);
lean_dec_ref(v___y_1354_);
v___x_1365_ = lean_ptr_addr(v___y_1352_);
v___x_1366_ = lean_ptr_addr(v___y_1355_);
v___x_1367_ = lean_usize_dec_eq(v___x_1365_, v___x_1366_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; 
lean_inc_ref(v___y_1360_);
lean_inc_ref(v___y_1357_);
v___x_1368_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1357_, v___y_1360_, v___y_1358_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v___y_1353_, v_a_1323_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1370_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1368_, 1);
lean_inc_ref(v___y_1359_);
lean_inc_ref(v___y_1356_);
v___x_1370_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1356_, v___y_1359_, v___y_1358_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v___y_1353_, v_a_1323_);
lean_dec_ref(v___y_1353_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1381_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1373_ = v___x_1370_;
v_isShared_1374_ = v_isSharedCheck_1381_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1381_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1375_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6));
v___x_1376_ = l_Lean_mkConst(v___x_1375_, v___x_1364_);
v___x_1377_ = l_Lean_mkApp8(v___x_1376_, v___y_1352_, v___y_1355_, v___y_1357_, v___y_1356_, v___y_1359_, v___y_1360_, v_a_1369_, v_a_1371_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1377_);
v___x_1379_ = v___x_1373_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
else
{
lean_dec(v_a_1369_);
lean_dec(v___x_1364_);
lean_dec_ref(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec_ref(v___y_1352_);
return v___x_1370_;
}
}
else
{
lean_dec(v___x_1364_);
lean_dec_ref(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec_ref(v___y_1353_);
lean_dec_ref(v___y_1352_);
return v___x_1368_;
}
}
else
{
uint8_t v___x_1382_; lean_object* v___x_1383_; 
lean_dec_ref(v___y_1355_);
v___x_1382_ = 0;
lean_inc_ref(v___y_1360_);
lean_inc_ref(v___y_1357_);
v___x_1383_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1357_, v___y_1360_, v___x_1382_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v___y_1353_, v_a_1323_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1385_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1383_, 1);
lean_inc_ref(v___y_1359_);
lean_inc_ref(v___y_1356_);
v___x_1385_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1356_, v___y_1359_, v___x_1382_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v___y_1353_, v_a_1323_);
lean_dec_ref(v___y_1353_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1396_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1388_ = v___x_1385_;
v_isShared_1389_ = v_isSharedCheck_1396_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1396_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1390_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8));
v___x_1391_ = l_Lean_mkConst(v___x_1390_, v___x_1364_);
v___x_1392_ = l_Lean_mkApp7(v___x_1391_, v___y_1352_, v___y_1357_, v___y_1356_, v___y_1359_, v___y_1360_, v_a_1384_, v_a_1386_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v___x_1392_);
v___x_1394_ = v___x_1388_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
else
{
lean_dec(v_a_1384_);
lean_dec(v___x_1364_);
lean_dec_ref(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec_ref(v___y_1352_);
return v___x_1385_;
}
}
else
{
lean_dec(v___x_1364_);
lean_dec_ref(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec_ref(v___y_1353_);
lean_dec_ref(v___y_1352_);
return v___x_1383_;
}
}
}
}
v___jp_1405_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = lean_unsigned_to_nat(1u);
v___x_1407_ = lean_nat_add(v_currRecDepth_1398_, v___x_1406_);
lean_inc(v_ref_1399_);
lean_inc_ref(v_toCold_1397_);
v___x_1408_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1408_, 0, v_toCold_1397_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
lean_ctor_set(v___x_1408_, 2, v_ref_1399_);
lean_ctor_set_uint8(v___x_1408_, sizeof(void*)*3, v_diag_1400_);
lean_ctor_set_uint8(v___x_1408_, sizeof(void*)*3 + 1, v_suppressElabErrors_1401_);
if (v___x_1404_ == 0)
{
lean_dec_ref(v___x_1403_);
lean_dec_ref(v_rhs_1313_);
v___y_1326_ = v_a_1314_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v_a_1316_;
v___y_1329_ = v_a_1317_;
v___y_1330_ = v_a_1318_;
v___y_1331_ = v_a_1319_;
v___y_1332_ = v_a_1320_;
v___y_1333_ = v_a_1321_;
v___y_1334_ = v___x_1408_;
v___y_1335_ = v_a_1323_;
goto v___jp_1325_;
}
else
{
lean_object* v_arg_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; 
v_arg_1409_ = lean_ctor_get(v___x_1403_, 1);
lean_inc_ref(v_arg_1409_);
v___x_1410_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1403_);
v___x_1411_ = l_Lean_Expr_isApp(v___x_1410_);
if (v___x_1411_ == 0)
{
lean_dec_ref(v___x_1410_);
lean_dec_ref(v_arg_1409_);
lean_dec_ref(v_rhs_1313_);
v___y_1326_ = v_a_1314_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v_a_1316_;
v___y_1329_ = v_a_1317_;
v___y_1330_ = v_a_1318_;
v___y_1331_ = v_a_1319_;
v___y_1332_ = v_a_1320_;
v___y_1333_ = v_a_1321_;
v___y_1334_ = v___x_1408_;
v___y_1335_ = v_a_1323_;
goto v___jp_1325_;
}
else
{
lean_object* v_arg_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v_arg_1412_ = lean_ctor_get(v___x_1410_, 1);
lean_inc_ref(v_arg_1412_);
v___x_1413_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1410_);
v___x_1414_ = l_Lean_Expr_isApp(v___x_1413_);
if (v___x_1414_ == 0)
{
lean_dec_ref(v___x_1413_);
lean_dec_ref(v_arg_1412_);
lean_dec_ref(v_arg_1409_);
lean_dec_ref(v_rhs_1313_);
v___y_1326_ = v_a_1314_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v_a_1316_;
v___y_1329_ = v_a_1317_;
v___y_1330_ = v_a_1318_;
v___y_1331_ = v_a_1319_;
v___y_1332_ = v_a_1320_;
v___y_1333_ = v_a_1321_;
v___y_1334_ = v___x_1408_;
v___y_1335_ = v_a_1323_;
goto v___jp_1325_;
}
else
{
lean_object* v_arg_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v_arg_1415_ = lean_ctor_get(v___x_1413_, 1);
lean_inc_ref(v_arg_1415_);
v___x_1416_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1413_);
v___x_1417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_1418_ = l_Lean_Expr_isConstOf(v___x_1416_, v___x_1417_);
if (v___x_1418_ == 0)
{
lean_dec_ref(v___x_1416_);
lean_dec_ref(v_arg_1415_);
lean_dec_ref(v_arg_1412_);
lean_dec_ref(v_arg_1409_);
lean_dec_ref(v_rhs_1313_);
v___y_1326_ = v_a_1314_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v_a_1316_;
v___y_1329_ = v_a_1317_;
v___y_1330_ = v_a_1318_;
v___y_1331_ = v_a_1319_;
v___y_1332_ = v_a_1320_;
v___y_1333_ = v_a_1321_;
v___y_1334_ = v___x_1408_;
v___y_1335_ = v_a_1323_;
goto v___jp_1325_;
}
else
{
lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1419_ = l_Lean_Expr_cleanupAnnotations(v_rhs_1313_);
v___x_1420_ = l_Lean_Expr_isApp(v___x_1419_);
if (v___x_1420_ == 0)
{
lean_dec_ref(v___x_1419_);
lean_dec_ref(v___x_1416_);
lean_dec_ref(v_arg_1415_);
lean_dec_ref(v_arg_1412_);
lean_dec_ref(v_arg_1409_);
v___y_1339_ = v_a_1314_;
v___y_1340_ = v_a_1315_;
v___y_1341_ = v_a_1316_;
v___y_1342_ = v_a_1317_;
v___y_1343_ = v_a_1318_;
v___y_1344_ = v_a_1319_;
v___y_1345_ = v_a_1320_;
v___y_1346_ = v_a_1321_;
v___y_1347_ = v___x_1408_;
v___y_1348_ = v_a_1323_;
goto v___jp_1338_;
}
else
{
lean_object* v_arg_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; 
v_arg_1421_ = lean_ctor_get(v___x_1419_, 1);
lean_inc_ref(v_arg_1421_);
v___x_1422_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1419_);
v___x_1423_ = l_Lean_Expr_isApp(v___x_1422_);
if (v___x_1423_ == 0)
{
lean_dec_ref(v___x_1422_);
lean_dec_ref(v_arg_1421_);
lean_dec_ref(v___x_1416_);
lean_dec_ref(v_arg_1415_);
lean_dec_ref(v_arg_1412_);
lean_dec_ref(v_arg_1409_);
v___y_1339_ = v_a_1314_;
v___y_1340_ = v_a_1315_;
v___y_1341_ = v_a_1316_;
v___y_1342_ = v_a_1317_;
v___y_1343_ = v_a_1318_;
v___y_1344_ = v_a_1319_;
v___y_1345_ = v_a_1320_;
v___y_1346_ = v_a_1321_;
v___y_1347_ = v___x_1408_;
v___y_1348_ = v_a_1323_;
goto v___jp_1338_;
}
else
{
lean_object* v_arg_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; 
v_arg_1424_ = lean_ctor_get(v___x_1422_, 1);
lean_inc_ref(v_arg_1424_);
v___x_1425_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1422_);
v___x_1426_ = l_Lean_Expr_isApp(v___x_1425_);
if (v___x_1426_ == 0)
{
lean_dec_ref(v___x_1425_);
lean_dec_ref(v_arg_1424_);
lean_dec_ref(v_arg_1421_);
lean_dec_ref(v___x_1416_);
lean_dec_ref(v_arg_1415_);
lean_dec_ref(v_arg_1412_);
lean_dec_ref(v_arg_1409_);
v___y_1339_ = v_a_1314_;
v___y_1340_ = v_a_1315_;
v___y_1341_ = v_a_1316_;
v___y_1342_ = v_a_1317_;
v___y_1343_ = v_a_1318_;
v___y_1344_ = v_a_1319_;
v___y_1345_ = v_a_1320_;
v___y_1346_ = v_a_1321_;
v___y_1347_ = v___x_1408_;
v___y_1348_ = v_a_1323_;
goto v___jp_1338_;
}
else
{
lean_object* v_arg_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v_arg_1427_ = lean_ctor_get(v___x_1425_, 1);
lean_inc_ref(v_arg_1427_);
v___x_1428_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1425_);
v___x_1429_ = l_Lean_Expr_isConstOf(v___x_1428_, v___x_1417_);
lean_dec_ref(v___x_1428_);
if (v___x_1429_ == 0)
{
lean_dec_ref(v_arg_1427_);
lean_dec_ref(v_arg_1424_);
lean_dec_ref(v_arg_1421_);
lean_dec_ref(v___x_1416_);
lean_dec_ref(v_arg_1415_);
lean_dec_ref(v_arg_1412_);
lean_dec_ref(v_arg_1409_);
v___y_1339_ = v_a_1314_;
v___y_1340_ = v_a_1315_;
v___y_1341_ = v_a_1316_;
v___y_1342_ = v_a_1317_;
v___y_1343_ = v_a_1318_;
v___y_1344_ = v_a_1319_;
v___y_1345_ = v_a_1320_;
v___y_1346_ = v_a_1321_;
v___y_1347_ = v___x_1408_;
v___y_1348_ = v_a_1323_;
goto v___jp_1338_;
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1430_ = lean_st_ref_get(v_a_1314_);
v___x_1431_ = lean_st_ref_get(v_a_1314_);
v___x_1432_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1430_, v_arg_1412_, v_arg_1421_);
lean_dec(v___x_1430_);
if (v___x_1432_ == 0)
{
lean_dec(v___x_1431_);
v___y_1352_ = v_arg_1415_;
v___y_1353_ = v___x_1408_;
v___y_1354_ = v___x_1416_;
v___y_1355_ = v_arg_1427_;
v___y_1356_ = v_arg_1409_;
v___y_1357_ = v_arg_1412_;
v___y_1358_ = v___x_1429_;
v___y_1359_ = v_arg_1424_;
v___y_1360_ = v_arg_1421_;
v___y_1361_ = v___x_1432_;
goto v___jp_1351_;
}
else
{
uint8_t v___x_1433_; 
v___x_1433_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1431_, v_arg_1409_, v_arg_1424_);
lean_dec(v___x_1431_);
v___y_1352_ = v_arg_1415_;
v___y_1353_ = v___x_1408_;
v___y_1354_ = v___x_1416_;
v___y_1355_ = v_arg_1427_;
v___y_1356_ = v_arg_1409_;
v___y_1357_ = v_arg_1412_;
v___y_1358_ = v___x_1429_;
v___y_1359_ = v_arg_1424_;
v___y_1360_ = v_arg_1421_;
v___y_1361_ = v___x_1433_;
goto v___jp_1351_;
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
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1442_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1443_ = lean_unsigned_to_nat(38u);
v___x_1444_ = lean_unsigned_to_nat(250u);
v___x_1445_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2));
v___x_1446_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1447_ = l_mkPanicMessageWithDecl(v___x_1446_, v___x_1445_, v___x_1444_, v___x_1443_, v___x_1442_);
return v___x_1447_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1449_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4));
v___x_1450_ = lean_unsigned_to_nat(6u);
v___x_1451_ = lean_unsigned_to_nat(260u);
v___x_1452_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2));
v___x_1453_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1454_ = l_mkPanicMessageWithDecl(v___x_1453_, v___x_1452_, v___x_1451_, v___x_1450_, v___x_1449_);
return v___x_1454_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__1));
v___x_1458_ = lean_unsigned_to_nat(4u);
v___x_1459_ = lean_unsigned_to_nat(219u);
v___x_1460_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__0));
v___x_1461_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1462_ = l_mkPanicMessageWithDecl(v___x_1461_, v___x_1460_, v___x_1459_, v___x_1458_, v___x_1457_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(lean_object* v_lhs_1463_, lean_object* v_rhs_1464_, uint8_t v_heq_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v_numArgs_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v_numArgs_1477_ = l_Lean_Expr_getAppNumArgs(v_lhs_1463_);
v___x_1478_ = l_Lean_Expr_getAppNumArgs(v_rhs_1464_);
v___x_1479_ = lean_nat_dec_eq(v___x_1478_, v_numArgs_1477_);
lean_dec(v___x_1478_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_dec(v_numArgs_1477_);
lean_dec_ref(v_rhs_1464_);
lean_dec_ref(v_lhs_1463_);
v___x_1480_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2);
v___x_1481_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1480_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
return v___x_1481_;
}
else
{
lean_object* v_f_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_f_1482_ = l_Lean_Expr_getAppFn(v_lhs_1463_);
v___x_1483_ = lean_box(0);
lean_inc_ref(v_f_1482_);
v___x_1484_ = l_Lean_Meta_getFunInfo(v_f_1482_, v___x_1483_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1486_; uint8_t v___x_1487_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
lean_dec_ref_known(v___x_1484_, 1);
v___x_1486_ = l_Lean_Meta_FunInfo_getArity(v_a_1485_);
lean_dec(v_a_1485_);
v___x_1487_ = lean_nat_dec_lt(v___x_1486_, v_numArgs_1477_);
lean_dec(v___x_1486_);
if (v___x_1487_ == 0)
{
lean_object* v_g_1488_; lean_object* v___x_1489_; 
v_g_1488_ = l_Lean_Expr_getAppFn(v_rhs_1464_);
v___x_1489_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_1482_, v_g_1488_, v_numArgs_1477_, v_lhs_1463_, v_rhs_1464_, v_heq_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
return v___x_1489_;
}
else
{
lean_object* v___x_1490_; 
lean_dec_ref(v_f_1482_);
lean_dec(v_numArgs_1477_);
lean_inc_ref(v_lhs_1463_);
v___x_1490_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(v_lhs_1463_, v_rhs_1464_);
if (lean_obj_tag(v___x_1490_) == 1)
{
lean_object* v_val_1491_; lean_object* v_fst_1492_; lean_object* v_snd_1493_; lean_object* v___y_1495_; lean_object* v___x_1508_; 
v_val_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_val_1491_);
lean_dec_ref_known(v___x_1490_, 1);
v_fst_1492_ = lean_ctor_get(v_val_1491_, 0);
lean_inc(v_fst_1492_);
v_snd_1493_ = lean_ctor_get(v_val_1491_, 1);
lean_inc_n(v_snd_1493_, 2);
lean_dec(v_val_1491_);
v___x_1508_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(v_fst_1492_, v_snd_1493_, v_a_1469_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
if (lean_obj_tag(v___x_1508_) == 0)
{
v___y_1495_ = v___x_1508_;
goto v___jp_1494_;
}
else
{
lean_object* v_a_1509_; uint8_t v___y_1511_; uint8_t v___x_1513_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_a_1509_);
v___x_1513_ = l_Lean_Exception_isInterrupt(v_a_1509_);
if (v___x_1513_ == 0)
{
uint8_t v___x_1514_; 
v___x_1514_ = l_Lean_Exception_isRuntime(v_a_1509_);
v___y_1511_ = v___x_1514_;
goto v___jp_1510_;
}
else
{
lean_dec(v_a_1509_);
v___y_1511_ = v___x_1513_;
goto v___jp_1510_;
}
v___jp_1510_:
{
if (v___y_1511_ == 0)
{
lean_object* v___x_1512_; 
lean_dec_ref_known(v___x_1508_, 1);
lean_inc_ref(v_rhs_1464_);
lean_inc_ref(v_lhs_1463_);
v___x_1512_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1463_, v_rhs_1464_, lean_box(0), v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
v___y_1495_ = v___x_1512_;
goto v___jp_1494_;
}
else
{
v___y_1495_ = v___x_1508_;
goto v___jp_1494_;
}
}
}
v___jp_1494_:
{
if (lean_obj_tag(v___y_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1497_; 
v_a_1496_ = lean_ctor_get(v___y_1495_, 0);
lean_inc(v_a_1496_);
lean_dec_ref_known(v___y_1495_, 1);
v___x_1497_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_1496_, v_lhs_1463_, v_rhs_1464_, v_snd_1493_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
lean_dec(v_snd_1493_);
lean_dec_ref(v_rhs_1464_);
lean_dec_ref(v_lhs_1463_);
lean_dec(v_a_1496_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1499_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
lean_dec_ref_known(v___x_1497_, 1);
v___x_1499_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_1498_, v_heq_1465_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
return v___x_1499_;
}
else
{
return v___x_1497_;
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_snd_1493_);
lean_dec_ref(v_rhs_1464_);
lean_dec_ref(v_lhs_1463_);
v_a_1500_ = lean_ctor_get(v___y_1495_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___y_1495_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___y_1495_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___y_1495_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
else
{
lean_object* v___x_1515_; 
lean_dec(v___x_1490_);
v___x_1515_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1463_, v_rhs_1464_, lean_box(0), v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
return v___x_1515_;
}
}
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
lean_dec_ref(v_f_1482_);
lean_dec(v_numArgs_1477_);
lean_dec_ref(v_rhs_1464_);
lean_dec_ref(v_lhs_1463_);
v_a_1516_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1484_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1484_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(lean_object* v_lhs_1524_, lean_object* v_rhs_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_){
_start:
{
uint8_t v___x_1537_; 
v___x_1537_ = l_Lean_Expr_isApp(v_lhs_1524_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = lean_box(0);
v___x_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
return v___x_1539_;
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1540_ = l_Lean_Expr_appFn_x21(v_lhs_1524_);
v___x_1541_ = l_Lean_Expr_appFn_x21(v_rhs_1525_);
v___x_1542_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v___x_1540_, v___x_1541_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
lean_dec_ref(v___x_1541_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1642_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1642_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1642_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v_a_u2081_1547_; lean_object* v_a_u2082_1548_; 
v_a_u2081_1547_ = l_Lean_Expr_appArg_x21(v_lhs_1524_);
v_a_u2082_1548_ = l_Lean_Expr_appArg_x21(v_rhs_1525_);
if (lean_obj_tag(v_a_1543_) == 1)
{
lean_object* v_val_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1606_; 
lean_del_object(v___x_1545_);
lean_dec_ref(v___x_1540_);
v_val_1549_ = lean_ctor_get(v_a_1543_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_a_1543_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1551_ = v_a_1543_;
v_isShared_1552_ = v_isSharedCheck_1606_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_val_1549_);
lean_dec(v_a_1543_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1606_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
size_t v___x_1553_; size_t v___x_1554_; uint8_t v___x_1555_; 
v___x_1553_ = lean_ptr_addr(v_a_u2081_1547_);
v___x_1554_ = lean_ptr_addr(v_a_u2082_1548_);
v___x_1555_ = lean_usize_dec_eq(v___x_1553_, v___x_1554_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; 
v___x_1556_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_1547_, v_a_u2082_1548_, v___x_1555_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1558_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 1);
v___x_1558_ = l_Lean_Meta_mkCongr(v_val_1549_, v_a_1557_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1569_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1569_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1569_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v_a_1559_);
v___x_1564_ = v___x_1551_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1566_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1564_);
v___x_1566_ = v___x_1561_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_del_object(v___x_1551_);
v_a_1570_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1558_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1558_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_del_object(v___x_1551_);
lean_dec(v_val_1549_);
v_a_1578_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1556_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1556_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
else
{
lean_object* v___x_1586_; 
lean_dec_ref(v_a_u2082_1548_);
v___x_1586_ = l_Lean_Meta_mkCongrFun(v_val_1549_, v_a_u2081_1547_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1597_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1589_ = v___x_1586_;
v_isShared_1590_ = v_isSharedCheck_1597_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1586_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1597_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v_a_1587_);
v___x_1592_ = v___x_1551_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1594_; 
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v___x_1592_);
v___x_1594_ = v___x_1589_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_del_object(v___x_1551_);
v_a_1598_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1586_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1586_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
}
else
{
size_t v___x_1607_; size_t v___x_1608_; uint8_t v___x_1609_; 
lean_dec(v_a_1543_);
v___x_1607_ = lean_ptr_addr(v_a_u2081_1547_);
v___x_1608_ = lean_ptr_addr(v_a_u2082_1548_);
v___x_1609_ = lean_usize_dec_eq(v___x_1607_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; 
lean_del_object(v___x_1545_);
v___x_1610_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_1547_, v_a_u2082_1548_, v___x_1609_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1612_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1610_, 1);
v___x_1612_ = l_Lean_Meta_mkCongrArg(v___x_1540_, v_a_1611_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1621_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1615_ = v___x_1612_;
v_isShared_1616_ = v_isSharedCheck_1621_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1612_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1621_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1617_, 0, v_a_1613_);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 0, v___x_1617_);
v___x_1619_ = v___x_1615_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
v_a_1622_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1612_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1612_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec_ref(v___x_1540_);
v_a_1630_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1610_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1610_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1640_; 
lean_dec_ref(v_a_u2082_1548_);
lean_dec_ref(v_a_u2081_1547_);
lean_dec_ref(v___x_1540_);
v___x_1638_ = lean_box(0);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1638_);
v___x_1640_ = v___x_1545_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1638_);
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
}
else
{
lean_dec_ref(v___x_1540_);
return v___x_1542_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3(void){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1646_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__2));
v___x_1647_ = lean_unsigned_to_nat(14u);
v___x_1648_ = lean_unsigned_to_nat(22u);
v___x_1649_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__1));
v___x_1650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__0));
v___x_1651_ = l_mkPanicMessageWithDecl(v___x_1650_, v___x_1649_, v___x_1648_, v___x_1647_, v___x_1646_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(lean_object* v_lhs_1652_, lean_object* v_rhs_1653_, uint8_t v_heq_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_1652_, v_rhs_1653_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1680_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1680_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1680_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___y_1672_; 
if (lean_obj_tag(v_a_1667_) == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3);
v___x_1678_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_spec__13(v___x_1677_);
v___y_1672_ = v___x_1678_;
goto v___jp_1671_;
}
else
{
lean_object* v_val_1679_; 
v_val_1679_ = lean_ctor_get(v_a_1667_, 0);
lean_inc(v_val_1679_);
lean_dec_ref_known(v_a_1667_, 1);
v___y_1672_ = v_val_1679_;
goto v___jp_1671_;
}
v___jp_1671_:
{
if (v_heq_1654_ == 0)
{
lean_object* v___x_1674_; 
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v___y_1672_);
v___x_1674_ = v___x_1669_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___y_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
else
{
lean_object* v___x_1676_; 
lean_del_object(v___x_1669_);
v___x_1676_ = l_Lean_Meta_mkHEqOfEq(v___y_1672_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_);
return v___x_1676_;
}
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
v_a_1681_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1666_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1666_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__1(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1690_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1691_ = lean_unsigned_to_nat(36u);
v___x_1692_ = lean_unsigned_to_nat(143u);
v___x_1693_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1694_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1695_ = l_mkPanicMessageWithDecl(v___x_1694_, v___x_1693_, v___x_1692_, v___x_1691_, v___x_1690_);
return v___x_1695_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__2(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1696_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1697_ = lean_unsigned_to_nat(34u);
v___x_1698_ = lean_unsigned_to_nat(144u);
v___x_1699_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1700_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1701_ = l_mkPanicMessageWithDecl(v___x_1700_, v___x_1699_, v___x_1698_, v___x_1697_, v___x_1696_);
return v___x_1701_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__4(void){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1703_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__3));
v___x_1704_ = lean_unsigned_to_nat(4u);
v___x_1705_ = lean_unsigned_to_nat(145u);
v___x_1706_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1707_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1708_ = l_mkPanicMessageWithDecl(v___x_1707_, v___x_1706_, v___x_1705_, v___x_1704_, v___x_1703_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrProof(lean_object* v_lhs_1719_, lean_object* v_rhs_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; uint8_t v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; uint8_t v___y_1768_; lean_object* v_toCold_1804_; lean_object* v_currRecDepth_1805_; lean_object* v_ref_1806_; uint8_t v_diag_1807_; uint8_t v_suppressElabErrors_1808_; lean_object* v_maxRecDepth_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v_toCold_1804_ = lean_ctor_get(v_a_1729_, 0);
v_currRecDepth_1805_ = lean_ctor_get(v_a_1729_, 1);
v_ref_1806_ = lean_ctor_get(v_a_1729_, 2);
v_diag_1807_ = lean_ctor_get_uint8(v_a_1729_, sizeof(void*)*3);
v_suppressElabErrors_1808_ = lean_ctor_get_uint8(v_a_1729_, sizeof(void*)*3 + 1);
v_maxRecDepth_1809_ = lean_ctor_get(v_toCold_1804_, 3);
v___x_1810_ = l_Lean_Expr_cleanupAnnotations(v_lhs_1719_);
v___x_1811_ = l_Lean_Expr_isApp(v___x_1810_);
v___x_1841_ = lean_unsigned_to_nat(0u);
v___x_1842_ = lean_nat_dec_eq(v_maxRecDepth_1809_, v___x_1841_);
if (v___x_1842_ == 0)
{
uint8_t v___x_1843_; 
v___x_1843_ = lean_nat_dec_eq(v_currRecDepth_1805_, v_maxRecDepth_1809_);
if (v___x_1843_ == 0)
{
goto v___jp_1812_;
}
else
{
lean_object* v___x_1844_; 
lean_dec_ref(v___x_1810_);
lean_dec_ref(v_rhs_1720_);
lean_inc(v_ref_1806_);
v___x_1844_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1806_);
return v___x_1844_;
}
}
else
{
goto v___jp_1812_;
}
v___jp_1732_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__1, &l_Lean_Meta_Grind_mkEqCongrProof___closed__1_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__1);
v___x_1744_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1743_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
lean_dec_ref(v___y_1741_);
return v___x_1744_;
}
v___jp_1745_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__2, &l_Lean_Meta_Grind_mkEqCongrProof___closed__2_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__2);
v___x_1757_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1756_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
lean_dec_ref(v___y_1754_);
return v___x_1757_;
}
v___jp_1758_:
{
if (v___y_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_dec_ref(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec_ref(v___y_1764_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec_ref(v___y_1759_);
v___x_1769_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__4, &l_Lean_Meta_Grind_mkEqCongrProof___closed__4_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__4);
v___x_1770_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1769_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v___y_1765_, v_a_1730_);
lean_dec_ref(v___y_1765_);
return v___x_1770_;
}
else
{
lean_object* v___x_1771_; size_t v___x_1772_; size_t v___x_1773_; uint8_t v___x_1774_; 
v___x_1771_ = l_Lean_Expr_constLevels_x21(v___y_1767_);
lean_dec_ref(v___y_1767_);
v___x_1772_ = lean_ptr_addr(v___y_1764_);
v___x_1773_ = lean_ptr_addr(v___y_1766_);
v___x_1774_ = lean_usize_dec_eq(v___x_1772_, v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; 
lean_inc_ref(v___y_1760_);
lean_inc_ref(v___y_1759_);
v___x_1775_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1759_, v___y_1760_, v___y_1763_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v___y_1765_, v_a_1730_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1777_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref_known(v___x_1775_, 1);
lean_inc_ref(v___y_1761_);
lean_inc_ref(v___y_1762_);
v___x_1777_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1762_, v___y_1761_, v___y_1763_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v___y_1765_, v_a_1730_);
lean_dec_ref(v___y_1765_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1788_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1788_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1788_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1782_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__6));
v___x_1783_ = l_Lean_mkConst(v___x_1782_, v___x_1771_);
v___x_1784_ = l_Lean_mkApp8(v___x_1783_, v___y_1764_, v___y_1766_, v___y_1759_, v___y_1762_, v___y_1760_, v___y_1761_, v_a_1776_, v_a_1778_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1784_);
v___x_1786_ = v___x_1780_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
else
{
lean_dec(v_a_1776_);
lean_dec(v___x_1771_);
lean_dec_ref(v___y_1766_);
lean_dec_ref(v___y_1764_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec_ref(v___y_1759_);
return v___x_1777_;
}
}
else
{
lean_dec(v___x_1771_);
lean_dec_ref(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec_ref(v___y_1759_);
return v___x_1775_;
}
}
else
{
uint8_t v___x_1789_; lean_object* v___x_1790_; 
lean_dec_ref(v___y_1766_);
v___x_1789_ = 0;
lean_inc_ref(v___y_1760_);
lean_inc_ref(v___y_1759_);
v___x_1790_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1759_, v___y_1760_, v___x_1789_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v___y_1765_, v_a_1730_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1792_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1790_, 1);
lean_inc_ref(v___y_1761_);
lean_inc_ref(v___y_1762_);
v___x_1792_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1762_, v___y_1761_, v___x_1789_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v___y_1765_, v_a_1730_);
lean_dec_ref(v___y_1765_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1803_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1795_ = v___x_1792_;
v_isShared_1796_ = v_isSharedCheck_1803_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1792_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1803_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1801_; 
v___x_1797_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__8));
v___x_1798_ = l_Lean_mkConst(v___x_1797_, v___x_1771_);
v___x_1799_ = l_Lean_mkApp7(v___x_1798_, v___y_1764_, v___y_1759_, v___y_1762_, v___y_1760_, v___y_1761_, v_a_1791_, v_a_1793_);
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v___x_1799_);
v___x_1801_ = v___x_1795_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
else
{
lean_dec(v_a_1791_);
lean_dec(v___x_1771_);
lean_dec_ref(v___y_1764_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec_ref(v___y_1759_);
return v___x_1792_;
}
}
else
{
lean_dec(v___x_1771_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec_ref(v___y_1759_);
return v___x_1790_;
}
}
}
}
v___jp_1812_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = lean_unsigned_to_nat(1u);
v___x_1814_ = lean_nat_add(v_currRecDepth_1805_, v___x_1813_);
lean_inc(v_ref_1806_);
lean_inc_ref(v_toCold_1804_);
v___x_1815_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1815_, 0, v_toCold_1804_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
lean_ctor_set(v___x_1815_, 2, v_ref_1806_);
lean_ctor_set_uint8(v___x_1815_, sizeof(void*)*3, v_diag_1807_);
lean_ctor_set_uint8(v___x_1815_, sizeof(void*)*3 + 1, v_suppressElabErrors_1808_);
if (v___x_1811_ == 0)
{
lean_dec_ref(v___x_1810_);
lean_dec_ref(v_rhs_1720_);
v___y_1733_ = v_a_1721_;
v___y_1734_ = v_a_1722_;
v___y_1735_ = v_a_1723_;
v___y_1736_ = v_a_1724_;
v___y_1737_ = v_a_1725_;
v___y_1738_ = v_a_1726_;
v___y_1739_ = v_a_1727_;
v___y_1740_ = v_a_1728_;
v___y_1741_ = v___x_1815_;
v___y_1742_ = v_a_1730_;
goto v___jp_1732_;
}
else
{
lean_object* v_arg_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v_arg_1816_ = lean_ctor_get(v___x_1810_, 1);
lean_inc_ref(v_arg_1816_);
v___x_1817_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1810_);
v___x_1818_ = l_Lean_Expr_isApp(v___x_1817_);
if (v___x_1818_ == 0)
{
lean_dec_ref(v___x_1817_);
lean_dec_ref(v_arg_1816_);
lean_dec_ref(v_rhs_1720_);
v___y_1733_ = v_a_1721_;
v___y_1734_ = v_a_1722_;
v___y_1735_ = v_a_1723_;
v___y_1736_ = v_a_1724_;
v___y_1737_ = v_a_1725_;
v___y_1738_ = v_a_1726_;
v___y_1739_ = v_a_1727_;
v___y_1740_ = v_a_1728_;
v___y_1741_ = v___x_1815_;
v___y_1742_ = v_a_1730_;
goto v___jp_1732_;
}
else
{
lean_object* v_arg_1819_; lean_object* v___x_1820_; uint8_t v___x_1821_; 
v_arg_1819_ = lean_ctor_get(v___x_1817_, 1);
lean_inc_ref(v_arg_1819_);
v___x_1820_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1817_);
v___x_1821_ = l_Lean_Expr_isApp(v___x_1820_);
if (v___x_1821_ == 0)
{
lean_dec_ref(v___x_1820_);
lean_dec_ref(v_arg_1819_);
lean_dec_ref(v_arg_1816_);
lean_dec_ref(v_rhs_1720_);
v___y_1733_ = v_a_1721_;
v___y_1734_ = v_a_1722_;
v___y_1735_ = v_a_1723_;
v___y_1736_ = v_a_1724_;
v___y_1737_ = v_a_1725_;
v___y_1738_ = v_a_1726_;
v___y_1739_ = v_a_1727_;
v___y_1740_ = v_a_1728_;
v___y_1741_ = v___x_1815_;
v___y_1742_ = v_a_1730_;
goto v___jp_1732_;
}
else
{
lean_object* v_arg_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; 
v_arg_1822_ = lean_ctor_get(v___x_1820_, 1);
lean_inc_ref(v_arg_1822_);
v___x_1823_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1820_);
v___x_1824_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_1825_ = l_Lean_Expr_isConstOf(v___x_1823_, v___x_1824_);
if (v___x_1825_ == 0)
{
lean_dec_ref(v___x_1823_);
lean_dec_ref(v_arg_1822_);
lean_dec_ref(v_arg_1819_);
lean_dec_ref(v_arg_1816_);
lean_dec_ref(v_rhs_1720_);
v___y_1733_ = v_a_1721_;
v___y_1734_ = v_a_1722_;
v___y_1735_ = v_a_1723_;
v___y_1736_ = v_a_1724_;
v___y_1737_ = v_a_1725_;
v___y_1738_ = v_a_1726_;
v___y_1739_ = v_a_1727_;
v___y_1740_ = v_a_1728_;
v___y_1741_ = v___x_1815_;
v___y_1742_ = v_a_1730_;
goto v___jp_1732_;
}
else
{
lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1826_ = l_Lean_Expr_cleanupAnnotations(v_rhs_1720_);
v___x_1827_ = l_Lean_Expr_isApp(v___x_1826_);
if (v___x_1827_ == 0)
{
lean_dec_ref(v___x_1826_);
lean_dec_ref(v___x_1823_);
lean_dec_ref(v_arg_1822_);
lean_dec_ref(v_arg_1819_);
lean_dec_ref(v_arg_1816_);
v___y_1746_ = v_a_1721_;
v___y_1747_ = v_a_1722_;
v___y_1748_ = v_a_1723_;
v___y_1749_ = v_a_1724_;
v___y_1750_ = v_a_1725_;
v___y_1751_ = v_a_1726_;
v___y_1752_ = v_a_1727_;
v___y_1753_ = v_a_1728_;
v___y_1754_ = v___x_1815_;
v___y_1755_ = v_a_1730_;
goto v___jp_1745_;
}
else
{
lean_object* v_arg_1828_; lean_object* v___x_1829_; uint8_t v___x_1830_; 
v_arg_1828_ = lean_ctor_get(v___x_1826_, 1);
lean_inc_ref(v_arg_1828_);
v___x_1829_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1826_);
v___x_1830_ = l_Lean_Expr_isApp(v___x_1829_);
if (v___x_1830_ == 0)
{
lean_dec_ref(v___x_1829_);
lean_dec_ref(v_arg_1828_);
lean_dec_ref(v___x_1823_);
lean_dec_ref(v_arg_1822_);
lean_dec_ref(v_arg_1819_);
lean_dec_ref(v_arg_1816_);
v___y_1746_ = v_a_1721_;
v___y_1747_ = v_a_1722_;
v___y_1748_ = v_a_1723_;
v___y_1749_ = v_a_1724_;
v___y_1750_ = v_a_1725_;
v___y_1751_ = v_a_1726_;
v___y_1752_ = v_a_1727_;
v___y_1753_ = v_a_1728_;
v___y_1754_ = v___x_1815_;
v___y_1755_ = v_a_1730_;
goto v___jp_1745_;
}
else
{
lean_object* v_arg_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v_arg_1831_ = lean_ctor_get(v___x_1829_, 1);
lean_inc_ref(v_arg_1831_);
v___x_1832_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1829_);
v___x_1833_ = l_Lean_Expr_isApp(v___x_1832_);
if (v___x_1833_ == 0)
{
lean_dec_ref(v___x_1832_);
lean_dec_ref(v_arg_1831_);
lean_dec_ref(v_arg_1828_);
lean_dec_ref(v___x_1823_);
lean_dec_ref(v_arg_1822_);
lean_dec_ref(v_arg_1819_);
lean_dec_ref(v_arg_1816_);
v___y_1746_ = v_a_1721_;
v___y_1747_ = v_a_1722_;
v___y_1748_ = v_a_1723_;
v___y_1749_ = v_a_1724_;
v___y_1750_ = v_a_1725_;
v___y_1751_ = v_a_1726_;
v___y_1752_ = v_a_1727_;
v___y_1753_ = v_a_1728_;
v___y_1754_ = v___x_1815_;
v___y_1755_ = v_a_1730_;
goto v___jp_1745_;
}
else
{
lean_object* v_arg_1834_; lean_object* v___x_1835_; uint8_t v___x_1836_; 
v_arg_1834_ = lean_ctor_get(v___x_1832_, 1);
lean_inc_ref(v_arg_1834_);
v___x_1835_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1832_);
v___x_1836_ = l_Lean_Expr_isConstOf(v___x_1835_, v___x_1824_);
lean_dec_ref(v___x_1835_);
if (v___x_1836_ == 0)
{
lean_dec_ref(v_arg_1834_);
lean_dec_ref(v_arg_1831_);
lean_dec_ref(v_arg_1828_);
lean_dec_ref(v___x_1823_);
lean_dec_ref(v_arg_1822_);
lean_dec_ref(v_arg_1819_);
lean_dec_ref(v_arg_1816_);
v___y_1746_ = v_a_1721_;
v___y_1747_ = v_a_1722_;
v___y_1748_ = v_a_1723_;
v___y_1749_ = v_a_1724_;
v___y_1750_ = v_a_1725_;
v___y_1751_ = v_a_1726_;
v___y_1752_ = v_a_1727_;
v___y_1753_ = v_a_1728_;
v___y_1754_ = v___x_1815_;
v___y_1755_ = v_a_1730_;
goto v___jp_1745_;
}
else
{
lean_object* v___x_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1837_ = lean_st_ref_get(v_a_1721_);
v___x_1838_ = lean_st_ref_get(v_a_1721_);
v___x_1839_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1837_, v_arg_1819_, v_arg_1831_);
lean_dec(v___x_1837_);
if (v___x_1839_ == 0)
{
lean_dec(v___x_1838_);
v___y_1759_ = v_arg_1819_;
v___y_1760_ = v_arg_1831_;
v___y_1761_ = v_arg_1828_;
v___y_1762_ = v_arg_1816_;
v___y_1763_ = v___x_1836_;
v___y_1764_ = v_arg_1822_;
v___y_1765_ = v___x_1815_;
v___y_1766_ = v_arg_1834_;
v___y_1767_ = v___x_1823_;
v___y_1768_ = v___x_1839_;
goto v___jp_1758_;
}
else
{
uint8_t v___x_1840_; 
v___x_1840_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1838_, v_arg_1816_, v_arg_1828_);
lean_dec(v___x_1838_);
v___y_1759_ = v_arg_1819_;
v___y_1760_ = v_arg_1831_;
v___y_1761_ = v_arg_1828_;
v___y_1762_ = v_arg_1816_;
v___y_1763_ = v___x_1836_;
v___y_1764_ = v_arg_1822_;
v___y_1765_ = v___x_1815_;
v___y_1766_ = v_arg_1834_;
v___y_1767_ = v___x_1823_;
v___y_1768_ = v___x_1840_;
goto v___jp_1758_;
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
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = lean_box(0);
v___x_1856_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3));
v___x_1857_ = l_Lean_mkConst(v___x_1856_, v___x_1855_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(lean_object* v_lhs_1858_, lean_object* v_rhs_1859_, uint8_t v_heq_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v___x_1872_; lean_object* v_p_1873_; lean_object* v___x_1874_; lean_object* v_q_1875_; uint8_t v___x_1876_; lean_object* v___x_1877_; 
v___x_1872_ = l_Lean_Expr_appFn_x21(v_lhs_1858_);
v_p_1873_ = l_Lean_Expr_appArg_x21(v___x_1872_);
lean_dec_ref(v___x_1872_);
v___x_1874_ = l_Lean_Expr_appFn_x21(v_rhs_1859_);
v_q_1875_ = l_Lean_Expr_appArg_x21(v___x_1874_);
lean_dec_ref(v___x_1874_);
v___x_1876_ = 0;
lean_inc_ref(v_q_1875_);
lean_inc_ref(v_p_1873_);
v___x_1877_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_p_1873_, v_q_1875_, v___x_1876_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v_hp_1879_; lean_object* v_hq_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref_known(v___x_1877_, 1);
v_hp_1879_ = l_Lean_Expr_appArg_x21(v_lhs_1858_);
v_hq_1880_ = l_Lean_Expr_appArg_x21(v_rhs_1859_);
v___x_1881_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4);
v___x_1882_ = l_Lean_mkApp5(v___x_1881_, v_p_1873_, v_q_1875_, v_a_1878_, v_hp_1879_, v_hq_1880_);
v___x_1883_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v___x_1882_, v_heq_1860_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_);
return v___x_1883_;
}
else
{
lean_dec_ref(v_q_1875_);
lean_dec_ref(v_p_1873_);
return v___x_1877_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2(void){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1894_ = lean_box(0);
v___x_1895_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1));
v___x_1896_ = l_Lean_mkConst(v___x_1895_, v___x_1894_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(lean_object* v_lhs_1897_, lean_object* v_rhs_1898_, uint8_t v_heq_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v___x_1911_; lean_object* v_p_1912_; lean_object* v___x_1913_; lean_object* v_q_1914_; uint8_t v___x_1915_; lean_object* v___x_1916_; 
v___x_1911_ = l_Lean_Expr_appFn_x21(v_lhs_1897_);
v_p_1912_ = l_Lean_Expr_appArg_x21(v___x_1911_);
lean_dec_ref(v___x_1911_);
v___x_1913_ = l_Lean_Expr_appFn_x21(v_rhs_1898_);
v_q_1914_ = l_Lean_Expr_appArg_x21(v___x_1913_);
lean_dec_ref(v___x_1913_);
v___x_1915_ = 0;
lean_inc_ref(v_q_1914_);
lean_inc_ref(v_p_1912_);
v___x_1916_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_p_1912_, v_q_1914_, v___x_1915_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v_hp_1918_; lean_object* v_hq_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1916_, 1);
v_hp_1918_ = l_Lean_Expr_appArg_x21(v_lhs_1897_);
v_hq_1919_ = l_Lean_Expr_appArg_x21(v_rhs_1898_);
v___x_1920_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2);
v___x_1921_ = l_Lean_mkApp5(v___x_1920_, v_p_1912_, v_q_1914_, v_a_1917_, v_hp_1918_, v_hq_1919_);
v___x_1922_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v___x_1921_, v_heq_1899_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
return v___x_1922_;
}
else
{
lean_dec_ref(v_q_1914_);
lean_dec_ref(v_p_1912_);
return v___x_1916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(lean_object* v_lhs_1923_, lean_object* v_rhs_1924_, uint8_t v_heq_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_){
_start:
{
if (lean_obj_tag(v_lhs_1923_) == 7)
{
if (lean_obj_tag(v_rhs_1924_) == 7)
{
lean_object* v_binderType_1937_; lean_object* v_body_1938_; lean_object* v_binderType_1939_; lean_object* v_body_1940_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1972_; lean_object* v___x_2001_; uint8_t v_transparency_2002_; uint8_t v___x_2003_; uint8_t v___x_2004_; 
v_binderType_1937_ = lean_ctor_get(v_lhs_1923_, 1);
lean_inc_ref(v_binderType_1937_);
v_body_1938_ = lean_ctor_get(v_lhs_1923_, 2);
lean_inc_ref(v_body_1938_);
lean_dec_ref_known(v_lhs_1923_, 3);
v_binderType_1939_ = lean_ctor_get(v_rhs_1924_, 1);
lean_inc_ref(v_binderType_1939_);
v_body_1940_ = lean_ctor_get(v_rhs_1924_, 2);
lean_inc_ref(v_body_1940_);
lean_dec_ref_known(v_rhs_1924_, 3);
v___x_2001_ = l_Lean_Meta_Context_config(v_a_1932_);
v_transparency_2002_ = lean_ctor_get_uint8(v___x_2001_, 9);
lean_dec_ref(v___x_2001_);
v___x_2003_ = 1;
v___x_2004_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2002_, v___x_2003_);
if (v___x_2004_ == 0)
{
lean_object* v_keyedConfig_2005_; uint8_t v_trackZetaDelta_2006_; lean_object* v_zetaDeltaSet_2007_; lean_object* v_lctx_2008_; lean_object* v_localInstances_2009_; lean_object* v_defEqCtx_x3f_2010_; lean_object* v_synthPendingDepth_2011_; lean_object* v_customCanUnfoldPredicate_x3f_2012_; uint8_t v_univApprox_2013_; uint8_t v_inTypeClassResolution_2014_; uint8_t v_cacheInferType_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v_keyedConfig_2005_ = lean_ctor_get(v_a_1932_, 0);
v_trackZetaDelta_2006_ = lean_ctor_get_uint8(v_a_1932_, sizeof(void*)*7);
v_zetaDeltaSet_2007_ = lean_ctor_get(v_a_1932_, 1);
v_lctx_2008_ = lean_ctor_get(v_a_1932_, 2);
v_localInstances_2009_ = lean_ctor_get(v_a_1932_, 3);
v_defEqCtx_x3f_2010_ = lean_ctor_get(v_a_1932_, 4);
v_synthPendingDepth_2011_ = lean_ctor_get(v_a_1932_, 5);
v_customCanUnfoldPredicate_x3f_2012_ = lean_ctor_get(v_a_1932_, 6);
v_univApprox_2013_ = lean_ctor_get_uint8(v_a_1932_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2014_ = lean_ctor_get_uint8(v_a_1932_, sizeof(void*)*7 + 2);
v_cacheInferType_2015_ = lean_ctor_get_uint8(v_a_1932_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2005_);
v___x_2016_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2003_, v_keyedConfig_2005_);
lean_inc(v_customCanUnfoldPredicate_x3f_2012_);
lean_inc(v_synthPendingDepth_2011_);
lean_inc(v_defEqCtx_x3f_2010_);
lean_inc_ref(v_localInstances_2009_);
lean_inc_ref(v_lctx_2008_);
lean_inc(v_zetaDeltaSet_2007_);
v___x_2017_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
lean_ctor_set(v___x_2017_, 1, v_zetaDeltaSet_2007_);
lean_ctor_set(v___x_2017_, 2, v_lctx_2008_);
lean_ctor_set(v___x_2017_, 3, v_localInstances_2009_);
lean_ctor_set(v___x_2017_, 4, v_defEqCtx_x3f_2010_);
lean_ctor_set(v___x_2017_, 5, v_synthPendingDepth_2011_);
lean_ctor_set(v___x_2017_, 6, v_customCanUnfoldPredicate_x3f_2012_);
lean_ctor_set_uint8(v___x_2017_, sizeof(void*)*7, v_trackZetaDelta_2006_);
lean_ctor_set_uint8(v___x_2017_, sizeof(void*)*7 + 1, v_univApprox_2013_);
lean_ctor_set_uint8(v___x_2017_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2014_);
lean_ctor_set_uint8(v___x_2017_, sizeof(void*)*7 + 3, v_cacheInferType_2015_);
lean_inc_ref(v_binderType_1937_);
v___x_2018_ = l_Lean_Meta_getLevel(v_binderType_1937_, v___x_2017_, v_a_1933_, v_a_1934_, v_a_1935_);
lean_dec_ref_known(v___x_2017_, 7);
v___y_1972_ = v___x_2018_;
goto v___jp_1971_;
}
else
{
lean_object* v___x_2019_; 
lean_inc_ref(v_binderType_1937_);
v___x_2019_ = l_Lean_Meta_getLevel(v_binderType_1937_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
v___y_1972_ = v___x_2019_;
goto v___jp_1971_;
}
v___jp_1941_:
{
if (lean_obj_tag(v___y_1943_) == 0)
{
lean_object* v_a_1944_; uint8_t v___x_1945_; lean_object* v___x_1946_; 
v_a_1944_ = lean_ctor_get(v___y_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref_known(v___y_1943_, 1);
v___x_1945_ = 0;
lean_inc_ref(v_binderType_1939_);
lean_inc_ref(v_binderType_1937_);
v___x_1946_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_binderType_1937_, v_binderType_1939_, v___x_1945_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1948_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1946_, 1);
lean_inc_ref(v_body_1940_);
lean_inc_ref(v_body_1938_);
v___x_1948_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_body_1938_, v_body_1940_, v___x_1945_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1962_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1951_ = v___x_1948_;
v_isShared_1952_ = v_isSharedCheck_1962_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1962_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1960_; 
v___x_1953_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__1));
v___x_1954_ = lean_box(0);
v___x_1955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1955_, 0, v_a_1944_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___y_1942_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = l_Lean_mkConst(v___x_1953_, v___x_1956_);
v___x_1958_ = l_Lean_mkApp6(v___x_1957_, v_binderType_1937_, v_binderType_1939_, v_body_1938_, v_body_1940_, v_a_1947_, v_a_1949_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1958_);
v___x_1960_ = v___x_1951_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
else
{
lean_dec(v_a_1947_);
lean_dec(v_a_1944_);
lean_dec(v___y_1942_);
lean_dec_ref(v_body_1940_);
lean_dec_ref(v_binderType_1939_);
lean_dec_ref(v_body_1938_);
lean_dec_ref(v_binderType_1937_);
return v___x_1948_;
}
}
else
{
lean_dec(v_a_1944_);
lean_dec(v___y_1942_);
lean_dec_ref(v_body_1940_);
lean_dec_ref(v_binderType_1939_);
lean_dec_ref(v_body_1938_);
lean_dec_ref(v_binderType_1937_);
return v___x_1946_;
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec(v___y_1942_);
lean_dec_ref(v_body_1940_);
lean_dec_ref(v_binderType_1939_);
lean_dec_ref(v_body_1938_);
lean_dec_ref(v_binderType_1937_);
v_a_1963_ = lean_ctor_get(v___y_1943_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___y_1943_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___y_1943_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___y_1943_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
v___jp_1971_:
{
if (lean_obj_tag(v___y_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1974_; uint8_t v_transparency_1975_; uint8_t v___x_1976_; uint8_t v___x_1977_; 
v_a_1973_ = lean_ctor_get(v___y_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v___y_1972_, 1);
v___x_1974_ = l_Lean_Meta_Context_config(v_a_1932_);
v_transparency_1975_ = lean_ctor_get_uint8(v___x_1974_, 9);
lean_dec_ref(v___x_1974_);
v___x_1976_ = 1;
v___x_1977_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1975_, v___x_1976_);
if (v___x_1977_ == 0)
{
lean_object* v_keyedConfig_1978_; uint8_t v_trackZetaDelta_1979_; lean_object* v_zetaDeltaSet_1980_; lean_object* v_lctx_1981_; lean_object* v_localInstances_1982_; lean_object* v_defEqCtx_x3f_1983_; lean_object* v_synthPendingDepth_1984_; lean_object* v_customCanUnfoldPredicate_x3f_1985_; uint8_t v_univApprox_1986_; uint8_t v_inTypeClassResolution_1987_; uint8_t v_cacheInferType_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v_keyedConfig_1978_ = lean_ctor_get(v_a_1932_, 0);
v_trackZetaDelta_1979_ = lean_ctor_get_uint8(v_a_1932_, sizeof(void*)*7);
v_zetaDeltaSet_1980_ = lean_ctor_get(v_a_1932_, 1);
v_lctx_1981_ = lean_ctor_get(v_a_1932_, 2);
v_localInstances_1982_ = lean_ctor_get(v_a_1932_, 3);
v_defEqCtx_x3f_1983_ = lean_ctor_get(v_a_1932_, 4);
v_synthPendingDepth_1984_ = lean_ctor_get(v_a_1932_, 5);
v_customCanUnfoldPredicate_x3f_1985_ = lean_ctor_get(v_a_1932_, 6);
v_univApprox_1986_ = lean_ctor_get_uint8(v_a_1932_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1987_ = lean_ctor_get_uint8(v_a_1932_, sizeof(void*)*7 + 2);
v_cacheInferType_1988_ = lean_ctor_get_uint8(v_a_1932_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1978_);
v___x_1989_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1976_, v_keyedConfig_1978_);
lean_inc(v_customCanUnfoldPredicate_x3f_1985_);
lean_inc(v_synthPendingDepth_1984_);
lean_inc(v_defEqCtx_x3f_1983_);
lean_inc_ref(v_localInstances_1982_);
lean_inc_ref(v_lctx_1981_);
lean_inc(v_zetaDeltaSet_1980_);
v___x_1990_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
lean_ctor_set(v___x_1990_, 1, v_zetaDeltaSet_1980_);
lean_ctor_set(v___x_1990_, 2, v_lctx_1981_);
lean_ctor_set(v___x_1990_, 3, v_localInstances_1982_);
lean_ctor_set(v___x_1990_, 4, v_defEqCtx_x3f_1983_);
lean_ctor_set(v___x_1990_, 5, v_synthPendingDepth_1984_);
lean_ctor_set(v___x_1990_, 6, v_customCanUnfoldPredicate_x3f_1985_);
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*7, v_trackZetaDelta_1979_);
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*7 + 1, v_univApprox_1986_);
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1987_);
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*7 + 3, v_cacheInferType_1988_);
lean_inc_ref(v_body_1938_);
v___x_1991_ = l_Lean_Meta_getLevel(v_body_1938_, v___x_1990_, v_a_1933_, v_a_1934_, v_a_1935_);
lean_dec_ref_known(v___x_1990_, 7);
v___y_1942_ = v_a_1973_;
v___y_1943_ = v___x_1991_;
goto v___jp_1941_;
}
else
{
lean_object* v___x_1992_; 
lean_inc_ref(v_body_1938_);
v___x_1992_ = l_Lean_Meta_getLevel(v_body_1938_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
v___y_1942_ = v_a_1973_;
v___y_1943_ = v___x_1992_;
goto v___jp_1941_;
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec_ref(v_body_1940_);
lean_dec_ref(v_binderType_1939_);
lean_dec_ref(v_body_1938_);
lean_dec_ref(v_binderType_1937_);
v_a_1993_ = lean_ctor_get(v___y_1972_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___y_1972_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___y_1972_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___y_1972_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
lean_dec_ref_known(v_lhs_1923_, 3);
lean_dec_ref(v_rhs_1924_);
v___x_2020_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3);
v___x_2021_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2020_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
return v___x_2021_;
}
}
else
{
lean_object* v___x_2022_; 
lean_inc_ref(v_lhs_1923_);
v___x_2022_ = l_Lean_Meta_Grind_useFunCC___redArg(v_lhs_1923_, v_a_1926_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; uint8_t v___x_2024_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
v___x_2024_ = lean_unbox(v_a_2023_);
lean_dec(v_a_2023_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2025_ = l_Lean_Expr_getAppNumArgs(v_lhs_1923_);
v___x_2026_ = l_Lean_Expr_getAppNumArgs(v_rhs_1924_);
v___x_2027_ = lean_nat_dec_eq(v___x_2026_, v___x_2025_);
lean_dec(v___x_2026_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
lean_dec(v___x_2025_);
lean_dec_ref(v_rhs_1924_);
lean_dec_ref(v_lhs_1923_);
v___x_2028_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5);
v___x_2029_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2028_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
return v___x_2029_;
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2055_; uint8_t v___x_2056_; 
v___x_2030_ = l_Lean_Expr_getAppFn(v_lhs_1923_);
v___x_2031_ = l_Lean_Expr_getAppFn(v_rhs_1924_);
v___x_2055_ = lean_unsigned_to_nat(2u);
v___x_2056_ = lean_nat_dec_eq(v___x_2025_, v___x_2055_);
if (v___x_2056_ == 0)
{
goto v___jp_2057_;
}
else
{
lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_2062_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9));
v___x_2063_ = l_Lean_Expr_isConstOf(v___x_2030_, v___x_2062_);
if (v___x_2063_ == 0)
{
goto v___jp_2057_;
}
else
{
uint8_t v___x_2064_; 
v___x_2064_ = l_Lean_Expr_isConstOf(v___x_2031_, v___x_2062_);
if (v___x_2064_ == 0)
{
goto v___jp_2057_;
}
else
{
lean_object* v___x_2065_; 
lean_dec_ref(v___x_2031_);
lean_dec_ref(v___x_2030_);
lean_dec(v___x_2025_);
v___x_2065_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_1923_, v_rhs_1924_, v_heq_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
lean_dec_ref(v_rhs_1924_);
lean_dec_ref(v_lhs_1923_);
return v___x_2065_;
}
}
}
v___jp_2032_:
{
lean_object* v___x_2033_; 
lean_inc_ref(v_rhs_1924_);
lean_inc_ref(v_lhs_1923_);
v___x_2033_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(v_lhs_1923_, v_rhs_1924_, v___x_2030_, v___x_2031_, v___x_2025_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
lean_dec_ref(v___x_2031_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; uint8_t v___x_2035_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___x_2033_, 1);
v___x_2035_ = lean_unbox(v_a_2034_);
lean_dec(v_a_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; 
v___x_2036_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_1923_, v_rhs_1924_, v_heq_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
return v___x_2036_;
}
else
{
lean_object* v___x_2037_; 
v___x_2037_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_1923_, v_rhs_1924_, v_heq_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
lean_dec_ref(v_rhs_1924_);
lean_dec_ref(v_lhs_1923_);
return v___x_2037_;
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec_ref(v_rhs_1924_);
lean_dec_ref(v_lhs_1923_);
v_a_2038_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2033_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2033_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
v___jp_2046_:
{
lean_object* v___x_2047_; uint8_t v___x_2048_; 
v___x_2047_ = lean_unsigned_to_nat(3u);
v___x_2048_ = lean_nat_dec_eq(v___x_2025_, v___x_2047_);
if (v___x_2048_ == 0)
{
goto v___jp_2032_;
}
else
{
lean_object* v___x_2049_; uint8_t v___x_2050_; 
v___x_2049_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_2050_ = l_Lean_Expr_isConstOf(v___x_2030_, v___x_2049_);
if (v___x_2050_ == 0)
{
goto v___jp_2032_;
}
else
{
uint8_t v___x_2051_; 
v___x_2051_ = l_Lean_Expr_isConstOf(v___x_2031_, v___x_2049_);
if (v___x_2051_ == 0)
{
goto v___jp_2032_;
}
else
{
lean_object* v___x_2052_; 
lean_dec_ref(v___x_2031_);
lean_dec_ref(v___x_2030_);
lean_dec(v___x_2025_);
v___x_2052_ = l_Lean_Meta_Grind_mkEqCongrProof(v_lhs_1923_, v_rhs_1924_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
if (lean_obj_tag(v___x_2052_) == 0)
{
if (v_heq_1925_ == 0)
{
return v___x_2052_;
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2054_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref_known(v___x_2052_, 1);
v___x_2054_ = l_Lean_Meta_mkHEqOfEq(v_a_2053_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
return v___x_2054_;
}
}
else
{
return v___x_2052_;
}
}
}
}
}
v___jp_2057_:
{
if (v___x_2056_ == 0)
{
goto v___jp_2046_;
}
else
{
lean_object* v___x_2058_; uint8_t v___x_2059_; 
v___x_2058_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7));
v___x_2059_ = l_Lean_Expr_isConstOf(v___x_2030_, v___x_2058_);
if (v___x_2059_ == 0)
{
goto v___jp_2046_;
}
else
{
uint8_t v___x_2060_; 
v___x_2060_ = l_Lean_Expr_isConstOf(v___x_2031_, v___x_2058_);
if (v___x_2060_ == 0)
{
goto v___jp_2046_;
}
else
{
lean_object* v___x_2061_; 
lean_dec_ref(v___x_2031_);
lean_dec_ref(v___x_2030_);
lean_dec(v___x_2025_);
v___x_2061_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_1923_, v_rhs_1924_, v_heq_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
lean_dec_ref(v_rhs_1924_);
lean_dec_ref(v_lhs_1923_);
return v___x_2061_;
}
}
}
}
}
}
else
{
lean_object* v___x_2066_; 
v___x_2066_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_1923_, v_rhs_1924_, v_heq_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
return v___x_2066_;
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec_ref(v_rhs_1924_);
lean_dec_ref(v_lhs_1923_);
v_a_2067_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2022_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2022_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(lean_object* v_lhs_2075_, lean_object* v_rhs_2076_, lean_object* v_h_2077_, uint8_t v_flipped_2078_, uint8_t v_heq_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2091_ = l_Lean_Meta_Grind_congrPlaceholderProof;
v___x_2092_ = lean_expr_eqv(v_h_2077_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; uint8_t v___x_2094_; 
v___x_2093_ = l_Lean_Meta_Grind_eqCongrSymmPlaceholderProof;
v___x_2094_ = lean_expr_eqv(v_h_2077_, v___x_2093_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; 
lean_dec_ref(v_rhs_2076_);
lean_dec_ref(v_lhs_2075_);
v___x_2095_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(v_h_2077_, v_flipped_2078_, v_heq_2079_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
return v___x_2095_;
}
else
{
lean_object* v___x_2096_; 
lean_dec_ref(v_h_2077_);
v___x_2096_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(v_lhs_2075_, v_rhs_2076_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2096_) == 0)
{
if (v_heq_2079_ == 0)
{
return v___x_2096_;
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2098_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2096_, 1);
v___x_2098_ = l_Lean_Meta_mkHEqOfEq(v_a_2097_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
return v___x_2098_;
}
}
else
{
return v___x_2096_;
}
}
}
else
{
lean_object* v___x_2099_; 
lean_dec_ref(v_h_2077_);
v___x_2099_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(v_lhs_2075_, v_rhs_2076_, v_heq_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
return v___x_2099_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1(void){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2101_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2102_ = lean_unsigned_to_nat(29u);
v___x_2103_ = lean_unsigned_to_nat(288u);
v___x_2104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0));
v___x_2105_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2106_ = l_mkPanicMessageWithDecl(v___x_2105_, v___x_2104_, v___x_2103_, v___x_2102_, v___x_2101_);
return v___x_2106_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2107_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2108_ = lean_unsigned_to_nat(35u);
v___x_2109_ = lean_unsigned_to_nat(287u);
v___x_2110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0));
v___x_2111_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2112_ = l_mkPanicMessageWithDecl(v___x_2111_, v___x_2110_, v___x_2109_, v___x_2108_, v___x_2107_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(lean_object* v_lhs_2113_, lean_object* v_common_2114_, lean_object* v_acc_2115_, uint8_t v_heq_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
size_t v___x_2128_; size_t v___x_2129_; uint8_t v___x_2130_; 
v___x_2128_ = lean_ptr_addr(v_lhs_2113_);
v___x_2129_ = lean_ptr_addr(v_common_2114_);
v___x_2130_ = lean_usize_dec_eq(v___x_2128_, v___x_2129_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = lean_st_ref_get(v_a_2117_);
lean_inc_ref(v_lhs_2113_);
v___x_2132_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2131_, v_lhs_2113_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
lean_dec(v___x_2131_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v_target_x3f_2134_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v_target_x3f_2134_ = lean_ctor_get(v_a_2133_, 4);
lean_inc(v_target_x3f_2134_);
if (lean_obj_tag(v_target_x3f_2134_) == 1)
{
lean_object* v_proof_x3f_2135_; 
v_proof_x3f_2135_ = lean_ctor_get(v_a_2133_, 5);
lean_inc(v_proof_x3f_2135_);
if (lean_obj_tag(v_proof_x3f_2135_) == 1)
{
uint8_t v_flipped_2136_; lean_object* v_val_2137_; lean_object* v_val_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2166_; 
v_flipped_2136_ = lean_ctor_get_uint8(v_a_2133_, sizeof(void*)*12);
lean_dec(v_a_2133_);
v_val_2137_ = lean_ctor_get(v_target_x3f_2134_, 0);
lean_inc(v_val_2137_);
lean_dec_ref_known(v_target_x3f_2134_, 1);
v_val_2138_ = lean_ctor_get(v_proof_x3f_2135_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_proof_x3f_2135_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2140_ = v_proof_x3f_2135_;
v_isShared_2141_ = v_isSharedCheck_2166_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_val_2138_);
lean_dec(v_proof_x3f_2135_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2166_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; 
lean_inc(v_val_2137_);
v___x_2142_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_lhs_2113_, v_val_2137_, v_val_2138_, v_flipped_2136_, v_heq_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2144_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2142_, 1);
v___x_2144_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_acc_2115_, v_a_2143_, v_heq_2116_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2147_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v_a_2145_);
v___x_2147_ = v___x_2140_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2145_);
v___x_2147_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
v_lhs_2113_ = v_val_2137_;
v_acc_2115_ = v___x_2147_;
goto _start;
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_del_object(v___x_2140_);
lean_dec(v_val_2137_);
v_a_2150_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2144_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2144_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_del_object(v___x_2140_);
lean_dec(v_val_2137_);
lean_dec(v_acc_2115_);
v_a_2158_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2142_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2142_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
else
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_dec(v_proof_x3f_2135_);
lean_dec_ref_known(v_target_x3f_2134_, 1);
lean_dec(v_a_2133_);
lean_dec(v_acc_2115_);
lean_dec_ref(v_lhs_2113_);
v___x_2167_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1);
v___x_2168_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2167_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
return v___x_2168_;
}
}
else
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
lean_dec(v_target_x3f_2134_);
lean_dec(v_a_2133_);
lean_dec(v_acc_2115_);
lean_dec_ref(v_lhs_2113_);
v___x_2169_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2);
v___x_2170_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2169_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
return v___x_2170_;
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec(v_acc_2115_);
lean_dec_ref(v_lhs_2113_);
v_a_2171_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2132_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2132_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
else
{
lean_object* v___x_2179_; 
lean_dec_ref(v_lhs_2113_);
v___x_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2179_, 0, v_acc_2115_);
return v___x_2179_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2181_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2182_ = lean_unsigned_to_nat(29u);
v___x_2183_ = lean_unsigned_to_nat(300u);
v___x_2184_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0));
v___x_2185_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2186_ = l_mkPanicMessageWithDecl(v___x_2185_, v___x_2184_, v___x_2183_, v___x_2182_, v___x_2181_);
return v___x_2186_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2187_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2188_ = lean_unsigned_to_nat(35u);
v___x_2189_ = lean_unsigned_to_nat(299u);
v___x_2190_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0));
v___x_2191_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2192_ = l_mkPanicMessageWithDecl(v___x_2191_, v___x_2190_, v___x_2189_, v___x_2188_, v___x_2187_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(lean_object* v_rhs_2193_, lean_object* v_common_2194_, lean_object* v_lhsEqCommon_x3f_2195_, uint8_t v_heq_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
size_t v___x_2208_; size_t v___x_2209_; uint8_t v___x_2210_; 
v___x_2208_ = lean_ptr_addr(v_rhs_2193_);
v___x_2209_ = lean_ptr_addr(v_common_2194_);
v___x_2210_ = lean_usize_dec_eq(v___x_2208_, v___x_2209_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = lean_st_ref_get(v_a_2197_);
lean_inc_ref(v_rhs_2193_);
v___x_2212_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2211_, v_rhs_2193_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
lean_dec(v___x_2211_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v_target_x3f_2214_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2213_);
lean_dec_ref_known(v___x_2212_, 1);
v_target_x3f_2214_ = lean_ctor_get(v_a_2213_, 4);
lean_inc(v_target_x3f_2214_);
if (lean_obj_tag(v_target_x3f_2214_) == 1)
{
lean_object* v_proof_x3f_2215_; 
v_proof_x3f_2215_ = lean_ctor_get(v_a_2213_, 5);
lean_inc(v_proof_x3f_2215_);
if (lean_obj_tag(v_proof_x3f_2215_) == 1)
{
uint8_t v_flipped_2216_; lean_object* v_val_2217_; lean_object* v_val_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2257_; 
v_flipped_2216_ = lean_ctor_get_uint8(v_a_2213_, sizeof(void*)*12);
lean_dec(v_a_2213_);
v_val_2217_ = lean_ctor_get(v_target_x3f_2214_, 0);
lean_inc(v_val_2217_);
lean_dec_ref_known(v_target_x3f_2214_, 1);
v_val_2218_ = lean_ctor_get(v_proof_x3f_2215_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_proof_x3f_2215_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2220_ = v_proof_x3f_2215_;
v_isShared_2221_ = v_isSharedCheck_2257_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_val_2218_);
lean_dec(v_proof_x3f_2215_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2257_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
uint8_t v___y_2223_; 
if (v_flipped_2216_ == 0)
{
uint8_t v___x_2256_; 
v___x_2256_ = 1;
v___y_2223_ = v___x_2256_;
goto v___jp_2222_;
}
else
{
v___y_2223_ = v___x_2210_;
goto v___jp_2222_;
}
v___jp_2222_:
{
lean_object* v___x_2224_; 
lean_inc(v_val_2217_);
v___x_2224_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_val_2217_, v_rhs_2193_, v_val_2218_, v___y_2223_, v_heq_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2226_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref_known(v___x_2224_, 1);
v___x_2226_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_val_2217_, v_common_2194_, v_lhsEqCommon_x3f_2195_, v_heq_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2228_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2226_, 1);
v___x_2228_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_a_2227_, v_a_2225_, v_heq_2196_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2239_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2239_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2239_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v_a_2229_);
v___x_2234_ = v___x_2220_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
lean_object* v___x_2236_; 
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v___x_2234_);
v___x_2236_ = v___x_2231_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_del_object(v___x_2220_);
v_a_2240_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2228_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2228_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
else
{
lean_dec(v_a_2225_);
lean_del_object(v___x_2220_);
return v___x_2226_;
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_del_object(v___x_2220_);
lean_dec(v_val_2217_);
lean_dec(v_lhsEqCommon_x3f_2195_);
v_a_2248_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2224_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2224_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
}
}
else
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
lean_dec_ref_known(v_target_x3f_2214_, 1);
lean_dec(v_proof_x3f_2215_);
lean_dec(v_a_2213_);
lean_dec(v_lhsEqCommon_x3f_2195_);
lean_dec_ref(v_rhs_2193_);
v___x_2258_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1);
v___x_2259_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2258_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
return v___x_2259_;
}
}
else
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
lean_dec(v_target_x3f_2214_);
lean_dec(v_a_2213_);
lean_dec(v_lhsEqCommon_x3f_2195_);
lean_dec_ref(v_rhs_2193_);
v___x_2260_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2);
v___x_2261_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2260_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
return v___x_2261_;
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_dec(v_lhsEqCommon_x3f_2195_);
lean_dec_ref(v_rhs_2193_);
v_a_2262_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2212_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2212_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
else
{
lean_object* v___x_2270_; 
lean_dec_ref(v_rhs_2193_);
v___x_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2270_, 0, v_lhsEqCommon_x3f_2195_);
return v___x_2270_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2271_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2272_ = lean_unsigned_to_nat(72u);
v___x_2273_ = lean_unsigned_to_nat(321u);
v___x_2274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0));
v___x_2275_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2276_ = l_mkPanicMessageWithDecl(v___x_2275_, v___x_2274_, v___x_2273_, v___x_2272_, v___x_2271_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(lean_object* v_lhs_2277_, lean_object* v_rhs_2278_, uint8_t v_heq_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_){
_start:
{
size_t v___x_2291_; size_t v___x_2292_; uint8_t v___x_2293_; 
v___x_2291_ = lean_ptr_addr(v_lhs_2277_);
v___x_2292_ = lean_ptr_addr(v_rhs_2278_);
v___x_2293_ = lean_usize_dec_eq(v___x_2291_, v___x_2292_);
if (v___x_2293_ == 0)
{
lean_object* v___x_2294_; 
lean_inc_ref(v_lhs_2277_);
v___x_2294_ = l_Lean_Meta_Grind_getRootENode___redArg(v_lhs_2277_, v_a_2280_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v___x_2296_ = lean_st_ref_get(v_a_2280_);
lean_inc_ref(v_lhs_2277_);
v___x_2297_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2296_, v_lhs_2277_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
lean_dec(v___x_2296_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___x_2297_, 1);
v___x_2299_ = lean_st_ref_get(v_a_2280_);
lean_inc_ref(v_rhs_2278_);
v___x_2300_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2299_, v_rhs_2278_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
lean_dec(v___x_2299_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v_root_2302_; lean_object* v_root_2303_; size_t v___x_2304_; size_t v___x_2305_; uint8_t v___x_2306_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_a_2301_);
lean_dec_ref_known(v___x_2300_, 1);
v_root_2302_ = lean_ctor_get(v_a_2298_, 2);
lean_inc_ref(v_root_2302_);
lean_dec(v_a_2298_);
v_root_2303_ = lean_ctor_get(v_a_2301_, 2);
lean_inc_ref(v_root_2303_);
lean_dec(v_a_2301_);
v___x_2304_ = lean_ptr_addr(v_root_2302_);
lean_dec_ref(v_root_2302_);
v___x_2305_ = lean_ptr_addr(v_root_2303_);
lean_dec_ref(v_root_2303_);
v___x_2306_ = lean_usize_dec_eq(v___x_2304_, v___x_2305_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
lean_dec(v_a_2295_);
lean_dec_ref(v_rhs_2278_);
lean_dec_ref(v_lhs_2277_);
v___x_2307_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2);
v___x_2308_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2307_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_2308_;
}
else
{
lean_object* v___x_2309_; 
lean_inc_ref(v_rhs_2278_);
lean_inc_ref(v_lhs_2277_);
v___x_2309_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(v_lhs_2277_, v_rhs_2278_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; uint8_t v_heqProofs_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
lean_dec_ref_known(v___x_2309_, 1);
v_heqProofs_2311_ = lean_ctor_get_uint8(v_a_2295_, sizeof(void*)*12 + 4);
lean_dec(v_a_2295_);
v___x_2312_ = lean_box(0);
v___x_2313_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_2277_, v_a_2310_, v___x_2312_, v_heqProofs_2311_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2315_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref_known(v___x_2313_, 1);
v___x_2315_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_2278_, v_a_2310_, v_a_2314_, v_heqProofs_2311_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
lean_dec(v_a_2310_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2331_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2331_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2331_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
if (lean_obj_tag(v_a_2316_) == 1)
{
lean_object* v_val_2320_; uint8_t v___y_2325_; 
v_val_2320_ = lean_ctor_get(v_a_2316_, 0);
lean_inc(v_val_2320_);
lean_dec_ref_known(v_a_2316_, 1);
if (v_heqProofs_2311_ == 0)
{
if (v_heq_2279_ == 0)
{
v___y_2325_ = v___x_2306_;
goto v___jp_2324_;
}
else
{
lean_del_object(v___x_2318_);
goto v___jp_2321_;
}
}
else
{
v___y_2325_ = v_heq_2279_;
goto v___jp_2324_;
}
v___jp_2321_:
{
if (v_heq_2279_ == 0)
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lean_Meta_mkEqOfHEq(v_val_2320_, v_heq_2279_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_2322_;
}
else
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Lean_Meta_mkHEqOfEq(v_val_2320_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_2323_;
}
}
v___jp_2324_:
{
if (v___y_2325_ == 0)
{
lean_del_object(v___x_2318_);
goto v___jp_2321_;
}
else
{
lean_object* v___x_2327_; 
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v_val_2320_);
v___x_2327_ = v___x_2318_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_val_2320_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
else
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
lean_del_object(v___x_2318_);
lean_dec(v_a_2316_);
v___x_2329_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3);
v___x_2330_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2329_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_2330_;
}
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
v_a_2332_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2315_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2315_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec(v_a_2310_);
lean_dec_ref(v_rhs_2278_);
v_a_2340_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2313_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2313_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
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
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
else
{
lean_dec(v_a_2295_);
lean_dec_ref(v_rhs_2278_);
lean_dec_ref(v_lhs_2277_);
return v___x_2309_;
}
}
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_dec(v_a_2298_);
lean_dec(v_a_2295_);
lean_dec_ref(v_rhs_2278_);
lean_dec_ref(v_lhs_2277_);
v_a_2348_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2300_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2300_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_dec(v_a_2295_);
lean_dec_ref(v_rhs_2278_);
lean_dec_ref(v_lhs_2277_);
v_a_2356_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2297_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2297_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec_ref(v_rhs_2278_);
lean_dec_ref(v_lhs_2277_);
v_a_2364_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2294_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2294_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
else
{
lean_object* v___x_2372_; 
lean_dec_ref(v_rhs_2278_);
v___x_2372_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(v_lhs_2277_, v_heq_2279_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_2372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(lean_object* v_thm_2373_, lean_object* v_lhs_2374_, lean_object* v_rhs_2375_, lean_object* v_i_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v___x_2388_; uint8_t v___x_2389_; 
v___x_2388_ = lean_unsigned_to_nat(0u);
v___x_2389_ = lean_nat_dec_lt(v___x_2388_, v_i_2376_);
if (v___x_2389_ == 0)
{
lean_object* v_proof_2390_; lean_object* v___x_2391_; 
v_proof_2390_ = lean_ctor_get(v_thm_2373_, 1);
lean_inc_ref(v_proof_2390_);
v___x_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2391_, 0, v_proof_2390_);
return v___x_2391_;
}
else
{
lean_object* v___x_2392_; lean_object* v_i_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2392_ = lean_unsigned_to_nat(1u);
v_i_2393_ = lean_nat_sub(v_i_2376_, v___x_2392_);
v___x_2394_ = l_Lean_Expr_appFn_x21(v_lhs_2374_);
v___x_2395_ = l_Lean_Expr_appFn_x21(v_rhs_2375_);
v___x_2396_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_2373_, v___x_2394_, v___x_2395_, v_i_2393_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec_ref(v___x_2395_);
lean_dec_ref(v___x_2394_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v_argKinds_2398_; uint8_t v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; uint8_t v___y_2403_; lean_object* v___x_2414_; lean_object* v___x_2415_; uint8_t v___x_2416_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref_known(v___x_2396_, 1);
v_argKinds_2398_ = lean_ctor_get(v_thm_2373_, 2);
v___x_2399_ = 0;
v___x_2400_ = l_Lean_Expr_appArg_x21(v_lhs_2374_);
v___x_2401_ = l_Lean_Expr_appArg_x21(v_rhs_2375_);
v___x_2414_ = lean_box(v___x_2399_);
v___x_2415_ = lean_array_get(v___x_2414_, v_argKinds_2398_, v_i_2393_);
lean_dec(v_i_2393_);
lean_dec(v___x_2414_);
v___x_2416_ = lean_unbox(v___x_2415_);
lean_dec(v___x_2415_);
if (v___x_2416_ == 4)
{
v___y_2403_ = v___x_2389_;
goto v___jp_2402_;
}
else
{
uint8_t v___x_2417_; 
v___x_2417_ = 0;
v___y_2403_ = v___x_2417_;
goto v___jp_2402_;
}
v___jp_2402_:
{
lean_object* v___x_2404_; 
lean_inc_ref(v___x_2401_);
lean_inc_ref(v___x_2400_);
v___x_2404_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___x_2400_, v___x_2401_, v___y_2403_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2413_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2407_ = v___x_2404_;
v_isShared_2408_ = v_isSharedCheck_2413_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2404_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2413_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2409_; lean_object* v___x_2411_; 
v___x_2409_ = l_Lean_mkApp3(v_a_2397_, v___x_2400_, v___x_2401_, v_a_2405_);
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 0, v___x_2409_);
v___x_2411_ = v___x_2407_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
else
{
lean_dec_ref(v___x_2401_);
lean_dec_ref(v___x_2400_);
lean_dec(v_a_2397_);
return v___x_2404_;
}
}
}
else
{
lean_dec(v_i_2393_);
return v___x_2396_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(lean_object* v_f_2421_, lean_object* v_g_2422_, lean_object* v_numArgs_2423_, lean_object* v_lhs_2424_, lean_object* v_rhs_2425_, uint8_t v_heq_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v___x_2438_; 
lean_inc(v_numArgs_2423_);
lean_inc_ref(v_f_2421_);
v___x_2438_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(v_f_2421_, v_numArgs_2423_, v_a_2430_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_a_2439_; lean_object* v_argKinds_2440_; lean_object* v___x_2441_; uint8_t v___x_2442_; 
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_a_2439_);
lean_dec_ref_known(v___x_2438_, 1);
v_argKinds_2440_ = lean_ctor_get(v_a_2439_, 2);
v___x_2441_ = lean_array_get_size(v_argKinds_2440_);
v___x_2442_ = lean_nat_dec_eq(v___x_2441_, v_numArgs_2423_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
lean_dec(v_a_2439_);
lean_dec_ref(v_rhs_2425_);
lean_dec_ref(v_lhs_2424_);
lean_dec(v_numArgs_2423_);
lean_dec_ref(v_g_2422_);
lean_dec_ref(v_f_2421_);
v___x_2443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2);
v___x_2444_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2443_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
return v___x_2444_;
}
else
{
lean_object* v___x_2445_; 
v___x_2445_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_2439_, v_lhs_2424_, v_rhs_2425_, v_numArgs_2423_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
lean_dec(v_a_2439_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; size_t v___x_2447_; size_t v___x_2448_; uint8_t v___x_2449_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
lean_dec_ref_known(v___x_2445_, 1);
v___x_2447_ = lean_ptr_addr(v_f_2421_);
v___x_2448_ = lean_ptr_addr(v_g_2422_);
v___x_2449_ = lean_usize_dec_eq(v___x_2447_, v___x_2448_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__4));
v___x_2451_ = l_Lean_Core_mkFreshUserName(v___x_2450_, v_a_2435_, v_a_2436_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; lean_object* v___x_2453_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2452_);
lean_dec_ref_known(v___x_2451_, 1);
lean_inc(v_a_2436_);
lean_inc_ref(v_a_2435_);
lean_inc(v_a_2434_);
lean_inc_ref(v_a_2433_);
lean_inc_ref(v_f_2421_);
v___x_2453_ = lean_infer_type(v_f_2421_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___f_2457_; lean_object* v___x_2458_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2454_);
lean_dec_ref_known(v___x_2453_, 1);
v___x_2455_ = lean_box(v___x_2449_);
v___x_2456_ = lean_box(v___x_2442_);
v___f_2457_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___boxed), 17, 5);
lean_closure_set(v___f_2457_, 0, v_numArgs_2423_);
lean_closure_set(v___f_2457_, 1, v_rhs_2425_);
lean_closure_set(v___f_2457_, 2, v_lhs_2424_);
lean_closure_set(v___f_2457_, 3, v___x_2455_);
lean_closure_set(v___f_2457_, 4, v___x_2456_);
v___x_2458_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_a_2452_, v_a_2454_, v___f_2457_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2460_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___x_2458_, 1);
v___x_2460_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_f_2421_, v_g_2422_, v___x_2449_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2462_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2461_);
lean_dec_ref_known(v___x_2460_, 1);
v___x_2462_ = l_Lean_Meta_mkEqNDRec(v_a_2459_, v_a_2446_, v_a_2461_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2464_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_a_2463_);
lean_dec_ref_known(v___x_2462_, 1);
v___x_2464_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_2463_, v_heq_2426_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
return v___x_2464_;
}
else
{
return v___x_2462_;
}
}
else
{
lean_dec(v_a_2459_);
lean_dec(v_a_2446_);
return v___x_2460_;
}
}
else
{
lean_dec(v_a_2446_);
lean_dec_ref(v_g_2422_);
lean_dec_ref(v_f_2421_);
return v___x_2458_;
}
}
else
{
lean_dec(v_a_2452_);
lean_dec(v_a_2446_);
lean_dec_ref(v_rhs_2425_);
lean_dec_ref(v_lhs_2424_);
lean_dec(v_numArgs_2423_);
lean_dec_ref(v_g_2422_);
lean_dec_ref(v_f_2421_);
return v___x_2453_;
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec(v_a_2446_);
lean_dec_ref(v_rhs_2425_);
lean_dec_ref(v_lhs_2424_);
lean_dec(v_numArgs_2423_);
lean_dec_ref(v_g_2422_);
lean_dec_ref(v_f_2421_);
v_a_2465_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2451_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2451_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
else
{
lean_object* v___x_2473_; 
lean_dec_ref(v_rhs_2425_);
lean_dec_ref(v_lhs_2424_);
lean_dec(v_numArgs_2423_);
lean_dec_ref(v_g_2422_);
lean_dec_ref(v_f_2421_);
v___x_2473_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_2446_, v_heq_2426_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
return v___x_2473_;
}
}
else
{
lean_dec_ref(v_rhs_2425_);
lean_dec_ref(v_lhs_2424_);
lean_dec(v_numArgs_2423_);
lean_dec_ref(v_g_2422_);
lean_dec_ref(v_f_2421_);
return v___x_2445_;
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec_ref(v_rhs_2425_);
lean_dec_ref(v_lhs_2424_);
lean_dec(v_numArgs_2423_);
lean_dec_ref(v_g_2422_);
lean_dec_ref(v_f_2421_);
v_a_2474_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2438_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2438_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1(void){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2483_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2484_ = lean_unsigned_to_nat(27u);
v___x_2485_ = lean_unsigned_to_nat(237u);
v___x_2486_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0));
v___x_2487_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2488_ = l_mkPanicMessageWithDecl(v___x_2487_, v___x_2486_, v___x_2485_, v___x_2484_, v___x_2483_);
return v___x_2488_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2(void){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2489_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2490_ = lean_unsigned_to_nat(27u);
v___x_2491_ = lean_unsigned_to_nat(236u);
v___x_2492_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0));
v___x_2493_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2494_ = l_mkPanicMessageWithDecl(v___x_2493_, v___x_2492_, v___x_2491_, v___x_2490_, v___x_2489_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(lean_object* v_lhs_2495_, lean_object* v_rhs_2496_, uint8_t v_heq_2497_, lean_object* v_e_u2081_2498_, lean_object* v_e_u2082_2499_, lean_object* v_numArgs_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_){
_start:
{
if (lean_obj_tag(v_e_u2081_2498_) == 5)
{
if (lean_obj_tag(v_e_u2082_2499_) == 5)
{
lean_object* v_fn_2512_; lean_object* v_fn_2513_; lean_object* v___x_2514_; lean_object* v_numArgs_2515_; size_t v___x_2516_; size_t v___x_2517_; uint8_t v___x_2518_; 
v_fn_2512_ = lean_ctor_get(v_e_u2081_2498_, 0);
lean_inc_ref(v_fn_2512_);
lean_dec_ref_known(v_e_u2081_2498_, 2);
v_fn_2513_ = lean_ctor_get(v_e_u2082_2499_, 0);
lean_inc_ref(v_fn_2513_);
lean_dec_ref_known(v_e_u2082_2499_, 2);
v___x_2514_ = lean_unsigned_to_nat(1u);
v_numArgs_2515_ = lean_nat_add(v_numArgs_2500_, v___x_2514_);
lean_dec(v_numArgs_2500_);
v___x_2516_ = lean_ptr_addr(v_fn_2512_);
v___x_2517_ = lean_ptr_addr(v_fn_2513_);
v___x_2518_ = lean_usize_dec_eq(v___x_2516_, v___x_2517_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; 
lean_inc_ref(v_fn_2513_);
lean_inc_ref(v_fn_2512_);
v___x_2519_ = l_Lean_Meta_Grind_hasSameType(v_fn_2512_, v_fn_2513_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; uint8_t v___x_2521_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___x_2519_, 1);
v___x_2521_ = lean_unbox(v_a_2520_);
lean_dec(v_a_2520_);
if (v___x_2521_ == 0)
{
v_e_u2081_2498_ = v_fn_2512_;
v_e_u2082_2499_ = v_fn_2513_;
v_numArgs_2500_ = v_numArgs_2515_;
goto _start;
}
else
{
lean_object* v___x_2523_; 
v___x_2523_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_2512_, v_fn_2513_, v_numArgs_2515_, v_lhs_2495_, v_rhs_2496_, v_heq_2497_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_);
return v___x_2523_;
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec(v_numArgs_2515_);
lean_dec_ref(v_fn_2513_);
lean_dec_ref(v_fn_2512_);
lean_dec_ref(v_rhs_2496_);
lean_dec_ref(v_lhs_2495_);
v_a_2524_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2519_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2519_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
else
{
lean_object* v___x_2532_; 
v___x_2532_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_2512_, v_fn_2513_, v_numArgs_2515_, v_lhs_2495_, v_rhs_2496_, v_heq_2497_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_);
return v___x_2532_;
}
}
else
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
lean_dec_ref_known(v_e_u2081_2498_, 2);
lean_dec(v_numArgs_2500_);
lean_dec_ref(v_e_u2082_2499_);
lean_dec_ref(v_rhs_2496_);
lean_dec_ref(v_lhs_2495_);
v___x_2533_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1);
v___x_2534_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2533_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_);
return v___x_2534_;
}
}
else
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
lean_dec(v_numArgs_2500_);
lean_dec_ref(v_e_u2082_2499_);
lean_dec_ref(v_e_u2081_2498_);
lean_dec_ref(v_rhs_2496_);
lean_dec_ref(v_lhs_2495_);
v___x_2535_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2);
v___x_2536_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2535_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_);
return v___x_2536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(lean_object* v_lhs_2537_, lean_object* v_rhs_2538_, uint8_t v_heq_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_rhs_2538_);
lean_inc_ref(v_lhs_2537_);
v___x_2552_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(v_lhs_2537_, v_rhs_2538_, v_heq_2539_, v_lhs_2537_, v_rhs_2538_, v___x_2551_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC___boxed(lean_object* v_lhs_2553_, lean_object* v_rhs_2554_, lean_object* v_heq_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_){
_start:
{
uint8_t v_heq_boxed_2567_; lean_object* v_res_2568_; 
v_heq_boxed_2567_ = lean_unbox(v_heq_2555_);
v_res_2568_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_2553_, v_rhs_2554_, v_heq_boxed_2567_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_);
lean_dec(v_a_2565_);
lean_dec_ref(v_a_2564_);
lean_dec(v_a_2563_);
lean_dec_ref(v_a_2562_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec(v_a_2556_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___boxed(lean_object* v_lhs_2569_, lean_object* v_rhs_2570_, lean_object* v_heq_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_){
_start:
{
uint8_t v_heq_boxed_2583_; lean_object* v_res_2584_; 
v_heq_boxed_2583_ = lean_unbox(v_heq_2571_);
v_res_2584_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_2569_, v_rhs_2570_, v_heq_boxed_2583_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_);
lean_dec(v_a_2581_);
lean_dec_ref(v_a_2580_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
lean_dec(v_a_2573_);
lean_dec(v_a_2572_);
lean_dec_ref(v_rhs_2570_);
lean_dec_ref(v_lhs_2569_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___boxed(lean_object* v_lhs_2585_, lean_object* v_rhs_2586_, lean_object* v_heq_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_){
_start:
{
uint8_t v_heq_boxed_2599_; lean_object* v_res_2600_; 
v_heq_boxed_2599_ = lean_unbox(v_heq_2587_);
v_res_2600_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_2585_, v_rhs_2586_, v_heq_boxed_2599_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_);
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_a_2595_);
lean_dec_ref(v_a_2594_);
lean_dec(v_a_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_a_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_a_2589_);
lean_dec(v_a_2588_);
lean_dec_ref(v_rhs_2586_);
lean_dec_ref(v_lhs_2585_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof___boxed(lean_object* v_lhs_2601_, lean_object* v_rhs_2602_, lean_object* v_h_2603_, lean_object* v_flipped_2604_, lean_object* v_heq_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_){
_start:
{
uint8_t v_flipped_boxed_2617_; uint8_t v_heq_boxed_2618_; lean_object* v_res_2619_; 
v_flipped_boxed_2617_ = lean_unbox(v_flipped_2604_);
v_heq_boxed_2618_ = lean_unbox(v_heq_2605_);
v_res_2619_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_lhs_2601_, v_rhs_2602_, v_h_2603_, v_flipped_boxed_2617_, v_heq_boxed_2618_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
lean_dec(v_a_2613_);
lean_dec_ref(v_a_2612_);
lean_dec(v_a_2611_);
lean_dec_ref(v_a_2610_);
lean_dec(v_a_2609_);
lean_dec_ref(v_a_2608_);
lean_dec(v_a_2607_);
lean_dec(v_a_2606_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___boxed(lean_object* v_lhs_2620_, lean_object* v_rhs_2621_, lean_object* v_heq_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
uint8_t v_heq_boxed_2634_; lean_object* v_res_2635_; 
v_heq_boxed_2634_ = lean_unbox(v_heq_2622_);
v_res_2635_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_2620_, v_rhs_2621_, v_heq_boxed_2634_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
lean_dec(v_a_2626_);
lean_dec_ref(v_a_2625_);
lean_dec(v_a_2624_);
lean_dec(v_a_2623_);
lean_dec_ref(v_rhs_2621_);
lean_dec_ref(v_lhs_2620_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper___boxed(lean_object* v_thm_2636_, lean_object* v_lhs_2637_, lean_object* v_rhs_2638_, lean_object* v_i_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_2636_, v_lhs_2637_, v_rhs_2638_, v_i_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
lean_dec(v_a_2649_);
lean_dec_ref(v_a_2648_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec(v_a_2640_);
lean_dec(v_i_2639_);
lean_dec_ref(v_rhs_2638_);
lean_dec_ref(v_lhs_2637_);
lean_dec_ref(v_thm_2636_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___boxed(lean_object** _args){
lean_object* v_lhs_2652_ = _args[0];
lean_object* v_rhs_2653_ = _args[1];
lean_object* v_heq_2654_ = _args[2];
lean_object* v_e_u2081_2655_ = _args[3];
lean_object* v_e_u2082_2656_ = _args[4];
lean_object* v_numArgs_2657_ = _args[5];
lean_object* v_a_2658_ = _args[6];
lean_object* v_a_2659_ = _args[7];
lean_object* v_a_2660_ = _args[8];
lean_object* v_a_2661_ = _args[9];
lean_object* v_a_2662_ = _args[10];
lean_object* v_a_2663_ = _args[11];
lean_object* v_a_2664_ = _args[12];
lean_object* v_a_2665_ = _args[13];
lean_object* v_a_2666_ = _args[14];
lean_object* v_a_2667_ = _args[15];
lean_object* v_a_2668_ = _args[16];
_start:
{
uint8_t v_heq_boxed_2669_; lean_object* v_res_2670_; 
v_heq_boxed_2669_ = lean_unbox(v_heq_2654_);
v_res_2670_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(v_lhs_2652_, v_rhs_2653_, v_heq_boxed_2669_, v_e_u2081_2655_, v_e_u2082_2656_, v_numArgs_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec(v_a_2658_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___boxed(lean_object* v_lhs_2671_, lean_object* v_common_2672_, lean_object* v_acc_2673_, lean_object* v_heq_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
uint8_t v_heq_boxed_2686_; lean_object* v_res_2687_; 
v_heq_boxed_2686_ = lean_unbox(v_heq_2674_);
v_res_2687_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_2671_, v_common_2672_, v_acc_2673_, v_heq_boxed_2686_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec_ref(v_common_2672_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___boxed(lean_object** _args){
lean_object* v_f_2688_ = _args[0];
lean_object* v_g_2689_ = _args[1];
lean_object* v_numArgs_2690_ = _args[2];
lean_object* v_lhs_2691_ = _args[3];
lean_object* v_rhs_2692_ = _args[4];
lean_object* v_heq_2693_ = _args[5];
lean_object* v_a_2694_ = _args[6];
lean_object* v_a_2695_ = _args[7];
lean_object* v_a_2696_ = _args[8];
lean_object* v_a_2697_ = _args[9];
lean_object* v_a_2698_ = _args[10];
lean_object* v_a_2699_ = _args[11];
lean_object* v_a_2700_ = _args[12];
lean_object* v_a_2701_ = _args[13];
lean_object* v_a_2702_ = _args[14];
lean_object* v_a_2703_ = _args[15];
lean_object* v_a_2704_ = _args[16];
_start:
{
uint8_t v_heq_boxed_2705_; lean_object* v_res_2706_; 
v_heq_boxed_2705_ = lean_unbox(v_heq_2693_);
v_res_2706_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_2688_, v_g_2689_, v_numArgs_2690_, v_lhs_2691_, v_rhs_2692_, v_heq_boxed_2705_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
lean_dec(v_a_2703_);
lean_dec_ref(v_a_2702_);
lean_dec(v_a_2701_);
lean_dec_ref(v_a_2700_);
lean_dec(v_a_2699_);
lean_dec_ref(v_a_2698_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
lean_dec(v_a_2695_);
lean_dec(v_a_2694_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___boxed(lean_object* v_rhs_2707_, lean_object* v_common_2708_, lean_object* v_lhsEqCommon_x3f_2709_, lean_object* v_heq_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_){
_start:
{
uint8_t v_heq_boxed_2722_; lean_object* v_res_2723_; 
v_heq_boxed_2722_ = lean_unbox(v_heq_2710_);
v_res_2723_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_2707_, v_common_2708_, v_lhsEqCommon_x3f_2709_, v_heq_boxed_2722_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_);
lean_dec(v_a_2720_);
lean_dec_ref(v_a_2719_);
lean_dec(v_a_2718_);
lean_dec_ref(v_a_2717_);
lean_dec(v_a_2716_);
lean_dec_ref(v_a_2715_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec(v_a_2711_);
lean_dec_ref(v_common_2708_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___boxed(lean_object* v_lhs_2724_, lean_object* v_rhs_2725_, lean_object* v_heq_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
uint8_t v_heq_boxed_2738_; lean_object* v_res_2739_; 
v_heq_boxed_2738_ = lean_unbox(v_heq_2726_);
v_res_2739_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_2724_, v_rhs_2725_, v_heq_boxed_2738_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
lean_dec(v_a_2732_);
lean_dec_ref(v_a_2731_);
lean_dec(v_a_2730_);
lean_dec_ref(v_a_2729_);
lean_dec(v_a_2728_);
lean_dec(v_a_2727_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop___boxed(lean_object* v_lhs_2740_, lean_object* v_rhs_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_2740_, v_rhs_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
lean_dec(v_a_2751_);
lean_dec_ref(v_a_2750_);
lean_dec(v_a_2749_);
lean_dec_ref(v_a_2748_);
lean_dec(v_a_2747_);
lean_dec_ref(v_a_2746_);
lean_dec(v_a_2745_);
lean_dec_ref(v_a_2744_);
lean_dec(v_a_2743_);
lean_dec(v_a_2742_);
lean_dec_ref(v_rhs_2741_);
lean_dec_ref(v_lhs_2740_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___boxed(lean_object* v_lhs_2754_, lean_object* v_rhs_2755_, lean_object* v_heq_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_){
_start:
{
uint8_t v_heq_boxed_2768_; lean_object* v_res_2769_; 
v_heq_boxed_2768_ = lean_unbox(v_heq_2756_);
v_res_2769_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_lhs_2754_, v_rhs_2755_, v_heq_boxed_2768_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_);
lean_dec(v_a_2766_);
lean_dec_ref(v_a_2765_);
lean_dec(v_a_2764_);
lean_dec_ref(v_a_2763_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2761_);
lean_dec(v_a_2760_);
lean_dec_ref(v_a_2759_);
lean_dec(v_a_2758_);
lean_dec(v_a_2757_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrProof___boxed(lean_object* v_lhs_2770_, lean_object* v_rhs_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Lean_Meta_Grind_mkEqCongrProof(v_lhs_2770_, v_rhs_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_);
lean_dec(v_a_2781_);
lean_dec_ref(v_a_2780_);
lean_dec(v_a_2779_);
lean_dec_ref(v_a_2778_);
lean_dec(v_a_2777_);
lean_dec_ref(v_a_2776_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
lean_dec(v_a_2773_);
lean_dec(v_a_2772_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___boxed(lean_object* v_lhs_2784_, lean_object* v_rhs_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(v_lhs_2784_, v_rhs_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_);
lean_dec(v_a_2795_);
lean_dec_ref(v_a_2794_);
lean_dec(v_a_2793_);
lean_dec_ref(v_a_2792_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
lean_dec(v_a_2787_);
lean_dec(v_a_2786_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___boxed(lean_object* v_lhs_2798_, lean_object* v_rhs_2799_, lean_object* v_heq_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_){
_start:
{
uint8_t v_heq_boxed_2812_; lean_object* v_res_2813_; 
v_heq_boxed_2812_ = lean_unbox(v_heq_2800_);
v_res_2813_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(v_lhs_2798_, v_rhs_2799_, v_heq_boxed_2812_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_);
lean_dec(v_a_2810_);
lean_dec_ref(v_a_2809_);
lean_dec(v_a_2808_);
lean_dec_ref(v_a_2807_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2802_);
lean_dec(v_a_2801_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(lean_object* v_00_u03b1_2814_, lean_object* v_ref_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_2815_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___boxed(lean_object* v_00_u03b1_2828_, lean_object* v_ref_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(v_00_u03b1_2828_, v_ref_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec(v___y_2830_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(lean_object* v_00_u03b1_2842_, lean_object* v_name_2843_, uint8_t v_bi_2844_, lean_object* v_type_2845_, lean_object* v_k_2846_, uint8_t v_kind_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_2843_, v_bi_2844_, v_type_2845_, v_k_2846_, v_kind_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___boxed(lean_object** _args){
lean_object* v_00_u03b1_2860_ = _args[0];
lean_object* v_name_2861_ = _args[1];
lean_object* v_bi_2862_ = _args[2];
lean_object* v_type_2863_ = _args[3];
lean_object* v_k_2864_ = _args[4];
lean_object* v_kind_2865_ = _args[5];
lean_object* v___y_2866_ = _args[6];
lean_object* v___y_2867_ = _args[7];
lean_object* v___y_2868_ = _args[8];
lean_object* v___y_2869_ = _args[9];
lean_object* v___y_2870_ = _args[10];
lean_object* v___y_2871_ = _args[11];
lean_object* v___y_2872_ = _args[12];
lean_object* v___y_2873_ = _args[13];
lean_object* v___y_2874_ = _args[14];
lean_object* v___y_2875_ = _args[15];
lean_object* v___y_2876_ = _args[16];
_start:
{
uint8_t v_bi_boxed_2877_; uint8_t v_kind_boxed_2878_; lean_object* v_res_2879_; 
v_bi_boxed_2877_ = lean_unbox(v_bi_2862_);
v_kind_boxed_2878_ = lean_unbox(v_kind_2865_);
v_res_2879_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(v_00_u03b1_2860_, v_name_2861_, v_bi_boxed_2877_, v_type_2863_, v_k_2864_, v_kind_boxed_2878_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec(v___y_2866_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(lean_object* v_00_u03b1_2880_, lean_object* v_name_2881_, lean_object* v_type_2882_, lean_object* v_k_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_name_2881_, v_type_2882_, v_k_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___boxed(lean_object* v_00_u03b1_2896_, lean_object* v_name_2897_, lean_object* v_type_2898_, lean_object* v_k_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(v_00_u03b1_2896_, v_name_2897_, v_type_2898_, v_k_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec(v___y_2900_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(lean_object* v_00_u03b1_2912_, lean_object* v_msg_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v_msg_2913_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___boxed(lean_object* v_00_u03b1_2926_, lean_object* v_msg_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(v_00_u03b1_2926_, v_msg_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec(v___y_2928_);
return v_res_2939_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__1(void){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__0));
v___x_2942_ = l_Lean_stringToMessageData(v___x_2941_);
return v___x_2942_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__3(void){
_start:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2944_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__2));
v___x_2945_ = l_Lean_stringToMessageData(v___x_2944_);
return v___x_2945_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__5(void){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2947_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__4));
v___x_2948_ = l_Lean_stringToMessageData(v___x_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* lean_grind_mk_eq_proof(lean_object* v_a_2949_, lean_object* v_b_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_){
_start:
{
lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___x_2975_; 
lean_inc_ref(v_b_2950_);
lean_inc_ref(v_a_2949_);
v___x_2975_ = l_Lean_Meta_Grind_hasSameType(v_a_2949_, v_b_2950_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; uint8_t v___x_2977_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_a_2976_);
lean_dec_ref_known(v___x_2975_, 1);
v___x_2977_ = lean_unbox(v_a_2976_);
lean_dec(v_a_2976_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; 
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
lean_dec(v_a_2952_);
lean_dec(v_a_2951_);
lean_inc(v_a_2960_);
lean_inc_ref(v_a_2959_);
lean_inc(v_a_2958_);
lean_inc_ref(v_a_2957_);
lean_inc_ref(v_a_2949_);
v___x_2978_ = lean_infer_type(v_a_2949_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2980_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2978_, 1);
lean_inc(v_a_2960_);
lean_inc_ref(v_a_2959_);
lean_inc(v_a_2958_);
lean_inc_ref(v_a_2957_);
lean_inc_ref(v_b_2950_);
v___x_2980_ = lean_infer_type(v_b_2950_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v___x_2982_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__1, &l_Lean_Meta_Grind_mkEqProofImpl___closed__1_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__1);
v___x_2983_ = l_Lean_indentExpr(v_a_2949_);
v___x_2984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2982_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
v___x_2985_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__3, &l_Lean_Meta_Grind_mkEqProofImpl___closed__3_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__3);
v___x_2986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2984_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
v___x_2987_ = l_Lean_indentExpr(v_a_2979_);
v___x_2988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2986_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
v___x_2989_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__5, &l_Lean_Meta_Grind_mkEqProofImpl___closed__5_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__5);
v___x_2990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2988_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
v___x_2991_ = l_Lean_indentExpr(v_b_2950_);
v___x_2992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2990_);
lean_ctor_set(v___x_2992_, 1, v___x_2991_);
v___x_2993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
lean_ctor_set(v___x_2993_, 1, v___x_2985_);
v___x_2994_ = l_Lean_indentExpr(v_a_2981_);
v___x_2995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2993_);
lean_ctor_set(v___x_2995_, 1, v___x_2994_);
v___x_2996_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v___x_2995_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_);
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2996_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2996_);
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
else
{
lean_dec(v_a_2979_);
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
lean_dec_ref(v_b_2950_);
lean_dec_ref(v_a_2949_);
return v___x_2980_;
}
}
else
{
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
lean_dec_ref(v_b_2950_);
lean_dec_ref(v_a_2949_);
return v___x_2978_;
}
}
else
{
v___y_2963_ = v_a_2951_;
v___y_2964_ = v_a_2952_;
v___y_2965_ = v_a_2953_;
v___y_2966_ = v_a_2954_;
v___y_2967_ = v_a_2955_;
v___y_2968_ = v_a_2956_;
v___y_2969_ = v_a_2957_;
v___y_2970_ = v_a_2958_;
v___y_2971_ = v_a_2959_;
v___y_2972_ = v_a_2960_;
goto v___jp_2962_;
}
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
lean_dec(v_a_2952_);
lean_dec(v_a_2951_);
lean_dec_ref(v_b_2950_);
lean_dec_ref(v_a_2949_);
v_a_3005_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2975_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_2975_);
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
v___jp_2962_:
{
uint8_t v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = 0;
v___x_2974_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_2949_, v_b_2950_, v___x_2973_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec(v___y_2963_);
return v___x_2974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqProofImpl___boxed(lean_object* v_a_3013_, lean_object* v_b_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = lean_grind_mk_eq_proof(v_a_3013_, v_b_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* lean_grind_mk_heq_proof(lean_object* v_a_3027_, lean_object* v_b_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_){
_start:
{
uint8_t v___x_3040_; lean_object* v___x_3041_; 
v___x_3040_ = 1;
v___x_3041_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_3027_, v_b_3028_, v___x_3040_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
lean_dec(v_a_3038_);
lean_dec_ref(v_a_3037_);
lean_dec(v_a_3036_);
lean_dec_ref(v_a_3035_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
lean_dec(v_a_3030_);
lean_dec(v_a_3029_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHEqProofImpl___boxed(lean_object* v_a_3042_, lean_object* v_b_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = lean_grind_mk_heq_proof(v_a_3042_, v_b_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_);
return v_res_3055_;
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
