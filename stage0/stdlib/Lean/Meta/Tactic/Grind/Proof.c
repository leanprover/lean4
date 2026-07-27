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
uint8_t v___y_50_; size_t v___x_75_; size_t v___x_76_; uint8_t v___x_77_; 
v___x_75_ = lean_ptr_addr(v_a_47_);
v___x_76_ = lean_ptr_addr(v_b_48_);
v___x_77_ = lean_usize_dec_eq(v___x_75_, v___x_76_);
if (v___x_77_ == 0)
{
uint8_t v___x_78_; 
v___x_78_ = l_Lean_Expr_isApp(v_a_47_);
if (v___x_78_ == 0)
{
v___y_50_ = v___x_78_;
goto v___jp_49_;
}
else
{
uint8_t v___x_79_; 
v___x_79_ = l_Lean_Expr_isApp(v_b_48_);
v___y_50_ = v___x_79_;
goto v___jp_49_;
}
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_81_, 0, v_a_47_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v___x_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
v___jp_49_:
{
if (v___y_50_ == 0)
{
lean_object* v___x_51_; 
lean_dec_ref(v_a_47_);
v___x_51_ = lean_box(0);
return v___x_51_;
}
else
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = l_Lean_Expr_appFn_x21(v_a_47_);
lean_dec_ref(v_a_47_);
v___x_53_ = l_Lean_Expr_appFn_x21(v_b_48_);
v___x_54_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(v___x_52_, v___x_53_);
lean_dec_ref(v___x_53_);
if (lean_obj_tag(v___x_54_) == 1)
{
lean_object* v_val_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_73_; 
v_val_55_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_73_ == 0)
{
v___x_57_ = v___x_54_;
v_isShared_58_ = v_isSharedCheck_73_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_val_55_);
lean_dec(v___x_54_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_73_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v_fst_59_; lean_object* v_snd_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_72_; 
v_fst_59_ = lean_ctor_get(v_val_55_, 0);
v_snd_60_ = lean_ctor_get(v_val_55_, 1);
v_isSharedCheck_72_ = !lean_is_exclusive(v_val_55_);
if (v_isSharedCheck_72_ == 0)
{
v___x_62_ = v_val_55_;
v_isShared_63_ = v_isSharedCheck_72_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_snd_60_);
lean_inc(v_fst_59_);
lean_dec(v_val_55_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_72_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_67_; 
v___x_64_ = lean_unsigned_to_nat(1u);
v___x_65_ = lean_nat_add(v_snd_60_, v___x_64_);
lean_dec(v_snd_60_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 1, v___x_65_);
v___x_67_ = v___x_62_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_fst_59_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v___x_65_);
v___x_67_ = v_reuseFailAlloc_71_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
lean_object* v___x_69_; 
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_67_);
v___x_69_ = v___x_57_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_67_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
}
}
else
{
lean_object* v___x_74_; 
lean_dec(v___x_54_);
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(lean_object* v_h_86_, uint8_t v_flipped_87_, uint8_t v_heq_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof___boxed(lean_object* v_h_116_, lean_object* v_flipped_117_, lean_object* v_heq_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
uint8_t v_flipped_boxed_124_; uint8_t v_heq_boxed_125_; lean_object* v_res_126_; 
v_flipped_boxed_124_ = lean_unbox(v_flipped_117_);
v_heq_boxed_125_ = lean_unbox(v_heq_118_);
v_res_126_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(v_h_116_, v_flipped_boxed_124_, v_heq_boxed_125_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(lean_object* v_a_127_, uint8_t v_heq_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
if (v_heq_128_ == 0)
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Meta_mkEqRefl(v_a_127_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
return v___x_134_;
}
else
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Meta_mkHEqRefl(v_a_127_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl___boxed(lean_object* v_a_136_, lean_object* v_heq_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
uint8_t v_heq_boxed_143_; lean_object* v_res_144_; 
v_heq_boxed_143_ = lean_unbox(v_heq_137_);
v_res_144_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(v_a_136_, v_heq_boxed_143_, v_a_138_, v_a_139_, v_a_140_, v_a_141_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans(lean_object* v_h_u2081_145_, lean_object* v_h_u2082_146_, uint8_t v_heq_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
if (v_heq_147_ == 0)
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_Meta_mkEqTrans(v_h_u2081_145_, v_h_u2082_146_, v_a_148_, v_a_149_, v_a_150_, v_a_151_);
return v___x_153_;
}
else
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Meta_mkHEqTrans(v_h_u2081_145_, v_h_u2082_146_, v_a_148_, v_a_149_, v_a_150_, v_a_151_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans___boxed(lean_object* v_h_u2081_155_, lean_object* v_h_u2082_156_, lean_object* v_heq_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
uint8_t v_heq_boxed_163_; lean_object* v_res_164_; 
v_heq_boxed_163_ = lean_unbox(v_heq_157_);
v_res_164_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans(v_h_u2081_155_, v_h_u2082_156_, v_heq_boxed_163_, v_a_158_, v_a_159_, v_a_160_, v_a_161_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(lean_object* v_h_u2081_165_, lean_object* v_h_u2082_166_, uint8_t v_heq_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
if (lean_obj_tag(v_h_u2081_165_) == 1)
{
lean_object* v_val_173_; lean_object* v___x_174_; 
v_val_173_ = lean_ctor_get(v_h_u2081_165_, 0);
lean_inc(v_val_173_);
lean_dec_ref_known(v_h_u2081_165_, 1);
v___x_174_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans(v_val_173_, v_h_u2082_166_, v_heq_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
return v___x_174_;
}
else
{
lean_object* v___x_175_; 
lean_dec(v_h_u2081_165_);
v___x_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_175_, 0, v_h_u2082_166_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27___boxed(lean_object* v_h_u2081_176_, lean_object* v_h_u2082_177_, lean_object* v_heq_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
uint8_t v_heq_boxed_184_; lean_object* v_res_185_; 
v_heq_boxed_184_ = lean_unbox(v_heq_178_);
v_res_185_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_h_u2081_176_, v_h_u2082_177_, v_heq_boxed_184_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(lean_object* v_h_186_, uint8_t v_heq_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
if (v_heq_187_ == 0)
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_Meta_mkEqOfHEq(v_h_186_, v_heq_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
return v___x_193_;
}
else
{
lean_object* v___x_194_; 
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v_h_186_);
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded___boxed(lean_object* v_h_195_, lean_object* v_heq_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
uint8_t v_heq_boxed_202_; lean_object* v_res_203_; 
v_heq_boxed_202_ = lean_unbox(v_heq_196_);
v_res_203_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_h_195_, v_heq_boxed_202_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
return v_res_203_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0(void){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3(lean_object* v_msg_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_12187__overap_218_; lean_object* v___x_219_; 
v___x_217_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0);
v___x_12187__overap_218_ = lean_panic_fn_borrowed(v___x_217_, v_msg_205_);
lean_inc(v___y_215_);
lean_inc_ref(v___y_214_);
lean_inc(v___y_213_);
lean_inc_ref(v___y_212_);
lean_inc(v___y_211_);
lean_inc_ref(v___y_210_);
lean_inc(v___y_209_);
lean_inc_ref(v___y_208_);
lean_inc(v___y_207_);
lean_inc(v___y_206_);
v___x_219_ = lean_apply_11(v___x_12187__overap_218_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, lean_box(0));
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___boxed(lean_object* v_msg_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3(v_msg_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec(v___y_221_);
return v_res_232_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0(void){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(lean_object* v_msg_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v___x_246_; lean_object* v___x_12985__overap_247_; lean_object* v___x_248_; 
v___x_246_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0);
v___x_12985__overap_247_ = lean_panic_fn_borrowed(v___x_246_, v_msg_234_);
lean_inc(v___y_244_);
lean_inc_ref(v___y_243_);
lean_inc(v___y_242_);
lean_inc_ref(v___y_241_);
lean_inc(v___y_240_);
lean_inc_ref(v___y_239_);
lean_inc(v___y_238_);
lean_inc_ref(v___y_237_);
lean_inc(v___y_236_);
lean_inc(v___y_235_);
v___x_248_ = lean_apply_11(v___x_12985__overap_247_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, lean_box(0));
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___boxed(lean_object* v_msg_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v_msg_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec(v___y_250_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(lean_object* v_t_262_, lean_object* v_k_263_){
_start:
{
if (lean_obj_tag(v_t_262_) == 0)
{
lean_object* v_k_264_; lean_object* v_v_265_; lean_object* v_l_266_; lean_object* v_r_267_; uint8_t v___x_268_; 
v_k_264_ = lean_ctor_get(v_t_262_, 1);
v_v_265_ = lean_ctor_get(v_t_262_, 2);
v_l_266_ = lean_ctor_get(v_t_262_, 3);
v_r_267_ = lean_ctor_get(v_t_262_, 4);
v___x_268_ = lean_nat_dec_lt(v_k_263_, v_k_264_);
if (v___x_268_ == 0)
{
uint8_t v___x_269_; 
v___x_269_ = lean_nat_dec_eq(v_k_263_, v_k_264_);
if (v___x_269_ == 0)
{
v_t_262_ = v_r_267_;
goto _start;
}
else
{
lean_object* v___x_271_; 
lean_inc(v_v_265_);
v___x_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_271_, 0, v_v_265_);
return v___x_271_;
}
}
else
{
v_t_262_ = v_l_266_;
goto _start;
}
}
else
{
lean_object* v___x_273_; 
v___x_273_ = lean_box(0);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg___boxed(lean_object* v_t_274_, lean_object* v_k_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(v_t_274_, v_k_275_);
lean_dec(v_k_275_);
lean_dec(v_t_274_);
return v_res_276_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_280_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_281_ = lean_unsigned_to_nat(35u);
v___x_282_ = lean_unsigned_to_nat(87u);
v___x_283_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__1));
v___x_284_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_285_ = l_mkPanicMessageWithDecl(v___x_284_, v___x_283_, v___x_282_, v___x_281_, v___x_280_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(lean_object* v___x_286_, lean_object* v_a_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v___x_299_; lean_object* v_snd_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_347_; 
v___x_299_ = lean_st_ref_get(v___y_288_);
v_snd_300_ = lean_ctor_get(v_a_287_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v_a_287_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; 
v_unused_348_ = lean_ctor_get(v_a_287_, 0);
lean_dec(v_unused_348_);
v___x_302_ = v_a_287_;
v_isShared_303_ = v_isSharedCheck_347_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_snd_300_);
lean_dec(v_a_287_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_347_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; 
lean_inc(v_snd_300_);
v___x_304_ = l_Lean_Meta_Grind_Goal_getENode(v___x_299_, v_snd_300_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___x_299_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_338_; 
v_a_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_338_ == 0)
{
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_338_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_338_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v_target_x3f_309_; lean_object* v_idx_310_; lean_object* v___x_311_; 
v_target_x3f_309_ = lean_ctor_get(v_a_305_, 4);
lean_inc(v_target_x3f_309_);
v_idx_310_ = lean_ctor_get(v_a_305_, 7);
lean_inc(v_idx_310_);
lean_dec(v_a_305_);
v___x_311_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(v___x_286_, v_idx_310_);
lean_dec(v_idx_310_);
if (lean_obj_tag(v___x_311_) == 1)
{
lean_object* v___x_313_; 
lean_dec(v_target_x3f_309_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_311_);
v___x_313_ = v___x_302_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_snd_300_);
v___x_313_ = v_reuseFailAlloc_317_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_315_; 
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_313_);
v___x_315_ = v___x_307_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
else
{
lean_object* v___x_318_; 
lean_dec(v___x_311_);
lean_del_object(v___x_307_);
v___x_318_ = lean_box(0);
if (lean_obj_tag(v_target_x3f_309_) == 1)
{
lean_object* v_val_319_; lean_object* v___x_321_; 
lean_dec(v_snd_300_);
v_val_319_ = lean_ctor_get(v_target_x3f_309_, 0);
lean_inc(v_val_319_);
lean_dec_ref_known(v_target_x3f_309_, 1);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v_val_319_);
lean_ctor_set(v___x_302_, 0, v___x_318_);
v___x_321_ = v___x_302_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_val_319_);
v___x_321_ = v_reuseFailAlloc_323_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
v_a_287_ = v___x_321_;
goto _start;
}
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; 
lean_dec(v_target_x3f_309_);
v___x_324_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3);
v___x_325_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3(v___x_324_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v___x_327_; 
lean_dec_ref_known(v___x_325_, 1);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_318_);
v___x_327_ = v___x_302_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_snd_300_);
v___x_327_ = v_reuseFailAlloc_329_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
v_a_287_ = v___x_327_;
goto _start;
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_del_object(v___x_302_);
lean_dec(v_snd_300_);
v_a_330_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_325_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_325_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_del_object(v___x_302_);
lean_dec(v_snd_300_);
v_a_339_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_304_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_304_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___boxed(lean_object* v___x_349_, lean_object* v_a_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(v___x_349_, v_a_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec(v___y_351_);
lean_dec(v___x_349_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(lean_object* v_k_363_, lean_object* v_v_364_, lean_object* v_t_365_){
_start:
{
if (lean_obj_tag(v_t_365_) == 0)
{
lean_object* v_size_366_; lean_object* v_k_367_; lean_object* v_v_368_; lean_object* v_l_369_; lean_object* v_r_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_651_; 
v_size_366_ = lean_ctor_get(v_t_365_, 0);
v_k_367_ = lean_ctor_get(v_t_365_, 1);
v_v_368_ = lean_ctor_get(v_t_365_, 2);
v_l_369_ = lean_ctor_get(v_t_365_, 3);
v_r_370_ = lean_ctor_get(v_t_365_, 4);
v_isSharedCheck_651_ = !lean_is_exclusive(v_t_365_);
if (v_isSharedCheck_651_ == 0)
{
v___x_372_ = v_t_365_;
v_isShared_373_ = v_isSharedCheck_651_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_r_370_);
lean_inc(v_l_369_);
lean_inc(v_v_368_);
lean_inc(v_k_367_);
lean_inc(v_size_366_);
lean_dec(v_t_365_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_651_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
uint8_t v___x_374_; 
v___x_374_ = lean_nat_dec_lt(v_k_363_, v_k_367_);
if (v___x_374_ == 0)
{
uint8_t v___x_375_; 
v___x_375_ = lean_nat_dec_eq(v_k_363_, v_k_367_);
if (v___x_375_ == 0)
{
lean_object* v_impl_376_; lean_object* v___x_377_; 
lean_dec(v_size_366_);
v_impl_376_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_k_363_, v_v_364_, v_r_370_);
v___x_377_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_369_) == 0)
{
lean_object* v_size_378_; lean_object* v_size_379_; lean_object* v_k_380_; lean_object* v_v_381_; lean_object* v_l_382_; lean_object* v_r_383_; lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v_size_378_ = lean_ctor_get(v_l_369_, 0);
v_size_379_ = lean_ctor_get(v_impl_376_, 0);
lean_inc(v_size_379_);
v_k_380_ = lean_ctor_get(v_impl_376_, 1);
lean_inc(v_k_380_);
v_v_381_ = lean_ctor_get(v_impl_376_, 2);
lean_inc(v_v_381_);
v_l_382_ = lean_ctor_get(v_impl_376_, 3);
lean_inc(v_l_382_);
v_r_383_ = lean_ctor_get(v_impl_376_, 4);
lean_inc(v_r_383_);
v___x_384_ = lean_unsigned_to_nat(3u);
v___x_385_ = lean_nat_mul(v___x_384_, v_size_378_);
v___x_386_ = lean_nat_dec_lt(v___x_385_, v_size_379_);
lean_dec(v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
lean_dec(v_r_383_);
lean_dec(v_l_382_);
lean_dec(v_v_381_);
lean_dec(v_k_380_);
v___x_387_ = lean_nat_add(v___x_377_, v_size_378_);
v___x_388_ = lean_nat_add(v___x_387_, v_size_379_);
lean_dec(v_size_379_);
lean_dec(v___x_387_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v_impl_376_);
lean_ctor_set(v___x_372_, 0, v___x_388_);
v___x_390_ = v___x_372_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_391_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_391_, 3, v_l_369_);
lean_ctor_set(v_reuseFailAlloc_391_, 4, v_impl_376_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
else
{
lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_455_; 
v_isSharedCheck_455_ = !lean_is_exclusive(v_impl_376_);
if (v_isSharedCheck_455_ == 0)
{
lean_object* v_unused_456_; lean_object* v_unused_457_; lean_object* v_unused_458_; lean_object* v_unused_459_; lean_object* v_unused_460_; 
v_unused_456_ = lean_ctor_get(v_impl_376_, 4);
lean_dec(v_unused_456_);
v_unused_457_ = lean_ctor_get(v_impl_376_, 3);
lean_dec(v_unused_457_);
v_unused_458_ = lean_ctor_get(v_impl_376_, 2);
lean_dec(v_unused_458_);
v_unused_459_ = lean_ctor_get(v_impl_376_, 1);
lean_dec(v_unused_459_);
v_unused_460_ = lean_ctor_get(v_impl_376_, 0);
lean_dec(v_unused_460_);
v___x_393_ = v_impl_376_;
v_isShared_394_ = v_isSharedCheck_455_;
goto v_resetjp_392_;
}
else
{
lean_dec(v_impl_376_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_455_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v_size_395_; lean_object* v_k_396_; lean_object* v_v_397_; lean_object* v_l_398_; lean_object* v_r_399_; lean_object* v_size_400_; lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v_size_395_ = lean_ctor_get(v_l_382_, 0);
v_k_396_ = lean_ctor_get(v_l_382_, 1);
v_v_397_ = lean_ctor_get(v_l_382_, 2);
v_l_398_ = lean_ctor_get(v_l_382_, 3);
v_r_399_ = lean_ctor_get(v_l_382_, 4);
v_size_400_ = lean_ctor_get(v_r_383_, 0);
v___x_401_ = lean_unsigned_to_nat(2u);
v___x_402_ = lean_nat_mul(v___x_401_, v_size_400_);
v___x_403_ = lean_nat_dec_lt(v_size_395_, v___x_402_);
lean_dec(v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_431_; 
lean_inc(v_r_399_);
lean_inc(v_l_398_);
lean_inc(v_v_397_);
lean_inc(v_k_396_);
v_isSharedCheck_431_ = !lean_is_exclusive(v_l_382_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; lean_object* v_unused_433_; lean_object* v_unused_434_; lean_object* v_unused_435_; lean_object* v_unused_436_; 
v_unused_432_ = lean_ctor_get(v_l_382_, 4);
lean_dec(v_unused_432_);
v_unused_433_ = lean_ctor_get(v_l_382_, 3);
lean_dec(v_unused_433_);
v_unused_434_ = lean_ctor_get(v_l_382_, 2);
lean_dec(v_unused_434_);
v_unused_435_ = lean_ctor_get(v_l_382_, 1);
lean_dec(v_unused_435_);
v_unused_436_ = lean_ctor_get(v_l_382_, 0);
lean_dec(v_unused_436_);
v___x_405_ = v_l_382_;
v_isShared_406_ = v_isSharedCheck_431_;
goto v_resetjp_404_;
}
else
{
lean_dec(v_l_382_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_431_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_421_; 
v___x_407_ = lean_nat_add(v___x_377_, v_size_378_);
v___x_408_ = lean_nat_add(v___x_407_, v_size_379_);
lean_dec(v_size_379_);
if (lean_obj_tag(v_l_398_) == 0)
{
lean_object* v_size_429_; 
v_size_429_ = lean_ctor_get(v_l_398_, 0);
lean_inc(v_size_429_);
v___y_421_ = v_size_429_;
goto v___jp_420_;
}
else
{
lean_object* v___x_430_; 
v___x_430_ = lean_unsigned_to_nat(0u);
v___y_421_ = v___x_430_;
goto v___jp_420_;
}
v___jp_409_:
{
lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_413_ = lean_nat_add(v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec(v___y_411_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 4, v_r_383_);
lean_ctor_set(v___x_405_, 3, v_r_399_);
lean_ctor_set(v___x_405_, 2, v_v_381_);
lean_ctor_set(v___x_405_, 1, v_k_380_);
lean_ctor_set(v___x_405_, 0, v___x_413_);
v___x_415_ = v___x_405_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_k_380_);
lean_ctor_set(v_reuseFailAlloc_419_, 2, v_v_381_);
lean_ctor_set(v_reuseFailAlloc_419_, 3, v_r_399_);
lean_ctor_set(v_reuseFailAlloc_419_, 4, v_r_383_);
v___x_415_ = v_reuseFailAlloc_419_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_417_; 
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 4, v___x_415_);
lean_ctor_set(v___x_393_, 3, v___y_410_);
lean_ctor_set(v___x_393_, 2, v_v_397_);
lean_ctor_set(v___x_393_, 1, v_k_396_);
lean_ctor_set(v___x_393_, 0, v___x_408_);
v___x_417_ = v___x_393_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_k_396_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v_v_397_);
lean_ctor_set(v_reuseFailAlloc_418_, 3, v___y_410_);
lean_ctor_set(v_reuseFailAlloc_418_, 4, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
v___jp_420_:
{
lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_422_ = lean_nat_add(v___x_407_, v___y_421_);
lean_dec(v___y_421_);
lean_dec(v___x_407_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v_l_398_);
lean_ctor_set(v___x_372_, 0, v___x_422_);
v___x_424_ = v___x_372_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v_l_369_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_l_398_);
v___x_424_ = v_reuseFailAlloc_428_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_425_; 
v___x_425_ = lean_nat_add(v___x_377_, v_size_400_);
if (lean_obj_tag(v_r_399_) == 0)
{
lean_object* v_size_426_; 
v_size_426_ = lean_ctor_get(v_r_399_, 0);
lean_inc(v_size_426_);
v___y_410_ = v___x_424_;
v___y_411_ = v___x_425_;
v___y_412_ = v_size_426_;
goto v___jp_409_;
}
else
{
lean_object* v___x_427_; 
v___x_427_ = lean_unsigned_to_nat(0u);
v___y_410_ = v___x_424_;
v___y_411_ = v___x_425_;
v___y_412_ = v___x_427_;
goto v___jp_409_;
}
}
}
}
}
else
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_441_; 
lean_del_object(v___x_372_);
v___x_437_ = lean_nat_add(v___x_377_, v_size_378_);
v___x_438_ = lean_nat_add(v___x_437_, v_size_379_);
lean_dec(v_size_379_);
v___x_439_ = lean_nat_add(v___x_437_, v_size_395_);
lean_dec(v___x_437_);
lean_inc_ref(v_l_369_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 4, v_l_382_);
lean_ctor_set(v___x_393_, 3, v_l_369_);
lean_ctor_set(v___x_393_, 2, v_v_368_);
lean_ctor_set(v___x_393_, 1, v_k_367_);
lean_ctor_set(v___x_393_, 0, v___x_439_);
v___x_441_ = v___x_393_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v_l_369_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v_l_382_);
v___x_441_ = v_reuseFailAlloc_454_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
v_isSharedCheck_448_ = !lean_is_exclusive(v_l_369_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; lean_object* v_unused_450_; lean_object* v_unused_451_; lean_object* v_unused_452_; lean_object* v_unused_453_; 
v_unused_449_ = lean_ctor_get(v_l_369_, 4);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_l_369_, 3);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v_l_369_, 2);
lean_dec(v_unused_451_);
v_unused_452_ = lean_ctor_get(v_l_369_, 1);
lean_dec(v_unused_452_);
v_unused_453_ = lean_ctor_get(v_l_369_, 0);
lean_dec(v_unused_453_);
v___x_443_ = v_l_369_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_dec(v_l_369_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 4, v_r_383_);
lean_ctor_set(v___x_443_, 3, v___x_441_);
lean_ctor_set(v___x_443_, 2, v_v_381_);
lean_ctor_set(v___x_443_, 1, v_k_380_);
lean_ctor_set(v___x_443_, 0, v___x_438_);
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_k_380_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_v_381_);
lean_ctor_set(v_reuseFailAlloc_447_, 3, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_447_, 4, v_r_383_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_461_; 
v_l_461_ = lean_ctor_get(v_impl_376_, 3);
lean_inc(v_l_461_);
if (lean_obj_tag(v_l_461_) == 0)
{
lean_object* v_r_462_; lean_object* v_k_463_; lean_object* v_v_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_487_; 
v_r_462_ = lean_ctor_get(v_impl_376_, 4);
v_k_463_ = lean_ctor_get(v_impl_376_, 1);
v_v_464_ = lean_ctor_get(v_impl_376_, 2);
v_isSharedCheck_487_ = !lean_is_exclusive(v_impl_376_);
if (v_isSharedCheck_487_ == 0)
{
lean_object* v_unused_488_; lean_object* v_unused_489_; 
v_unused_488_ = lean_ctor_get(v_impl_376_, 3);
lean_dec(v_unused_488_);
v_unused_489_ = lean_ctor_get(v_impl_376_, 0);
lean_dec(v_unused_489_);
v___x_466_ = v_impl_376_;
v_isShared_467_ = v_isSharedCheck_487_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_r_462_);
lean_inc(v_v_464_);
lean_inc(v_k_463_);
lean_dec(v_impl_376_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_487_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v_k_468_; lean_object* v_v_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_483_; 
v_k_468_ = lean_ctor_get(v_l_461_, 1);
v_v_469_ = lean_ctor_get(v_l_461_, 2);
v_isSharedCheck_483_ = !lean_is_exclusive(v_l_461_);
if (v_isSharedCheck_483_ == 0)
{
lean_object* v_unused_484_; lean_object* v_unused_485_; lean_object* v_unused_486_; 
v_unused_484_ = lean_ctor_get(v_l_461_, 4);
lean_dec(v_unused_484_);
v_unused_485_ = lean_ctor_get(v_l_461_, 3);
lean_dec(v_unused_485_);
v_unused_486_ = lean_ctor_get(v_l_461_, 0);
lean_dec(v_unused_486_);
v___x_471_ = v_l_461_;
v_isShared_472_ = v_isSharedCheck_483_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_v_469_);
lean_inc(v_k_468_);
lean_dec(v_l_461_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_483_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_473_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_462_, 2);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 4, v_r_462_);
lean_ctor_set(v___x_471_, 3, v_r_462_);
lean_ctor_set(v___x_471_, 2, v_v_368_);
lean_ctor_set(v___x_471_, 1, v_k_367_);
lean_ctor_set(v___x_471_, 0, v___x_377_);
v___x_475_ = v___x_471_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_482_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_482_, 3, v_r_462_);
lean_ctor_set(v_reuseFailAlloc_482_, 4, v_r_462_);
v___x_475_ = v_reuseFailAlloc_482_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_477_; 
lean_inc(v_r_462_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 3, v_r_462_);
lean_ctor_set(v___x_466_, 0, v___x_377_);
v___x_477_ = v___x_466_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_k_463_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_v_464_);
lean_ctor_set(v_reuseFailAlloc_481_, 3, v_r_462_);
lean_ctor_set(v_reuseFailAlloc_481_, 4, v_r_462_);
v___x_477_ = v_reuseFailAlloc_481_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_479_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v___x_477_);
lean_ctor_set(v___x_372_, 3, v___x_475_);
lean_ctor_set(v___x_372_, 2, v_v_469_);
lean_ctor_set(v___x_372_, 1, v_k_468_);
lean_ctor_set(v___x_372_, 0, v___x_473_);
v___x_479_ = v___x_372_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_k_468_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_v_469_);
lean_ctor_set(v_reuseFailAlloc_480_, 3, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_480_, 4, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
}
else
{
lean_object* v_r_490_; 
v_r_490_ = lean_ctor_get(v_impl_376_, 4);
lean_inc(v_r_490_);
if (lean_obj_tag(v_r_490_) == 0)
{
lean_object* v_k_491_; lean_object* v_v_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_503_; 
v_k_491_ = lean_ctor_get(v_impl_376_, 1);
v_v_492_ = lean_ctor_get(v_impl_376_, 2);
v_isSharedCheck_503_ = !lean_is_exclusive(v_impl_376_);
if (v_isSharedCheck_503_ == 0)
{
lean_object* v_unused_504_; lean_object* v_unused_505_; lean_object* v_unused_506_; 
v_unused_504_ = lean_ctor_get(v_impl_376_, 4);
lean_dec(v_unused_504_);
v_unused_505_ = lean_ctor_get(v_impl_376_, 3);
lean_dec(v_unused_505_);
v_unused_506_ = lean_ctor_get(v_impl_376_, 0);
lean_dec(v_unused_506_);
v___x_494_ = v_impl_376_;
v_isShared_495_ = v_isSharedCheck_503_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_v_492_);
lean_inc(v_k_491_);
lean_dec(v_impl_376_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_503_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_496_ = lean_unsigned_to_nat(3u);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 4, v_l_461_);
lean_ctor_set(v___x_494_, 2, v_v_368_);
lean_ctor_set(v___x_494_, 1, v_k_367_);
lean_ctor_set(v___x_494_, 0, v___x_377_);
v___x_498_ = v___x_494_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_502_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_502_, 3, v_l_461_);
lean_ctor_set(v_reuseFailAlloc_502_, 4, v_l_461_);
v___x_498_ = v_reuseFailAlloc_502_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_500_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v_r_490_);
lean_ctor_set(v___x_372_, 3, v___x_498_);
lean_ctor_set(v___x_372_, 2, v_v_492_);
lean_ctor_set(v___x_372_, 1, v_k_491_);
lean_ctor_set(v___x_372_, 0, v___x_496_);
v___x_500_ = v___x_372_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_k_491_);
lean_ctor_set(v_reuseFailAlloc_501_, 2, v_v_492_);
lean_ctor_set(v_reuseFailAlloc_501_, 3, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_501_, 4, v_r_490_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
else
{
lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_507_ = lean_unsigned_to_nat(2u);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v_impl_376_);
lean_ctor_set(v___x_372_, 3, v_r_490_);
lean_ctor_set(v___x_372_, 0, v___x_507_);
v___x_509_ = v___x_372_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_510_, 3, v_r_490_);
lean_ctor_set(v_reuseFailAlloc_510_, 4, v_impl_376_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
else
{
lean_object* v___x_512_; 
lean_dec(v_v_368_);
lean_dec(v_k_367_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 2, v_v_364_);
lean_ctor_set(v___x_372_, 1, v_k_363_);
v___x_512_ = v___x_372_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_size_366_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_k_363_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v_v_364_);
lean_ctor_set(v_reuseFailAlloc_513_, 3, v_l_369_);
lean_ctor_set(v_reuseFailAlloc_513_, 4, v_r_370_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
else
{
lean_object* v_impl_514_; lean_object* v___x_515_; 
lean_dec(v_size_366_);
v_impl_514_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_k_363_, v_v_364_, v_l_369_);
v___x_515_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_370_) == 0)
{
lean_object* v_size_516_; lean_object* v_size_517_; lean_object* v_k_518_; lean_object* v_v_519_; lean_object* v_l_520_; lean_object* v_r_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v_size_516_ = lean_ctor_get(v_r_370_, 0);
v_size_517_ = lean_ctor_get(v_impl_514_, 0);
lean_inc(v_size_517_);
v_k_518_ = lean_ctor_get(v_impl_514_, 1);
lean_inc(v_k_518_);
v_v_519_ = lean_ctor_get(v_impl_514_, 2);
lean_inc(v_v_519_);
v_l_520_ = lean_ctor_get(v_impl_514_, 3);
lean_inc(v_l_520_);
v_r_521_ = lean_ctor_get(v_impl_514_, 4);
lean_inc(v_r_521_);
v___x_522_ = lean_unsigned_to_nat(3u);
v___x_523_ = lean_nat_mul(v___x_522_, v_size_516_);
v___x_524_ = lean_nat_dec_lt(v___x_523_, v_size_517_);
lean_dec(v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
lean_dec(v_r_521_);
lean_dec(v_l_520_);
lean_dec(v_v_519_);
lean_dec(v_k_518_);
v___x_525_ = lean_nat_add(v___x_515_, v_size_517_);
lean_dec(v_size_517_);
v___x_526_ = lean_nat_add(v___x_525_, v_size_516_);
lean_dec(v___x_525_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 3, v_impl_514_);
lean_ctor_set(v___x_372_, 0, v___x_526_);
v___x_528_ = v___x_372_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_529_, 3, v_impl_514_);
lean_ctor_set(v_reuseFailAlloc_529_, 4, v_r_370_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
else
{
lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_595_; 
v_isSharedCheck_595_ = !lean_is_exclusive(v_impl_514_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; lean_object* v_unused_597_; lean_object* v_unused_598_; lean_object* v_unused_599_; lean_object* v_unused_600_; 
v_unused_596_ = lean_ctor_get(v_impl_514_, 4);
lean_dec(v_unused_596_);
v_unused_597_ = lean_ctor_get(v_impl_514_, 3);
lean_dec(v_unused_597_);
v_unused_598_ = lean_ctor_get(v_impl_514_, 2);
lean_dec(v_unused_598_);
v_unused_599_ = lean_ctor_get(v_impl_514_, 1);
lean_dec(v_unused_599_);
v_unused_600_ = lean_ctor_get(v_impl_514_, 0);
lean_dec(v_unused_600_);
v___x_531_ = v_impl_514_;
v_isShared_532_ = v_isSharedCheck_595_;
goto v_resetjp_530_;
}
else
{
lean_dec(v_impl_514_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_595_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v_size_533_; lean_object* v_size_534_; lean_object* v_k_535_; lean_object* v_v_536_; lean_object* v_l_537_; lean_object* v_r_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_size_533_ = lean_ctor_get(v_l_520_, 0);
v_size_534_ = lean_ctor_get(v_r_521_, 0);
v_k_535_ = lean_ctor_get(v_r_521_, 1);
v_v_536_ = lean_ctor_get(v_r_521_, 2);
v_l_537_ = lean_ctor_get(v_r_521_, 3);
v_r_538_ = lean_ctor_get(v_r_521_, 4);
v___x_539_ = lean_unsigned_to_nat(2u);
v___x_540_ = lean_nat_mul(v___x_539_, v_size_533_);
v___x_541_ = lean_nat_dec_lt(v_size_534_, v___x_540_);
lean_dec(v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_570_; 
lean_inc(v_r_538_);
lean_inc(v_l_537_);
lean_inc(v_v_536_);
lean_inc(v_k_535_);
v_isSharedCheck_570_ = !lean_is_exclusive(v_r_521_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; lean_object* v_unused_572_; lean_object* v_unused_573_; lean_object* v_unused_574_; lean_object* v_unused_575_; 
v_unused_571_ = lean_ctor_get(v_r_521_, 4);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_r_521_, 3);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_r_521_, 2);
lean_dec(v_unused_573_);
v_unused_574_ = lean_ctor_get(v_r_521_, 1);
lean_dec(v_unused_574_);
v_unused_575_ = lean_ctor_get(v_r_521_, 0);
lean_dec(v_unused_575_);
v___x_543_ = v_r_521_;
v_isShared_544_ = v_isSharedCheck_570_;
goto v_resetjp_542_;
}
else
{
lean_dec(v_r_521_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_570_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___x_558_; lean_object* v___y_560_; 
v___x_545_ = lean_nat_add(v___x_515_, v_size_517_);
lean_dec(v_size_517_);
v___x_546_ = lean_nat_add(v___x_545_, v_size_516_);
lean_dec(v___x_545_);
v___x_558_ = lean_nat_add(v___x_515_, v_size_533_);
if (lean_obj_tag(v_l_537_) == 0)
{
lean_object* v_size_568_; 
v_size_568_ = lean_ctor_get(v_l_537_, 0);
lean_inc(v_size_568_);
v___y_560_ = v_size_568_;
goto v___jp_559_;
}
else
{
lean_object* v___x_569_; 
v___x_569_ = lean_unsigned_to_nat(0u);
v___y_560_ = v___x_569_;
goto v___jp_559_;
}
v___jp_547_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_nat_add(v___y_548_, v___y_550_);
lean_dec(v___y_550_);
lean_dec(v___y_548_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 4, v_r_370_);
lean_ctor_set(v___x_543_, 3, v_r_538_);
lean_ctor_set(v___x_543_, 2, v_v_368_);
lean_ctor_set(v___x_543_, 1, v_k_367_);
lean_ctor_set(v___x_543_, 0, v___x_551_);
v___x_553_ = v___x_543_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_557_, 3, v_r_538_);
lean_ctor_set(v_reuseFailAlloc_557_, 4, v_r_370_);
v___x_553_ = v_reuseFailAlloc_557_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_555_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 4, v___x_553_);
lean_ctor_set(v___x_531_, 3, v___y_549_);
lean_ctor_set(v___x_531_, 2, v_v_536_);
lean_ctor_set(v___x_531_, 1, v_k_535_);
lean_ctor_set(v___x_531_, 0, v___x_546_);
v___x_555_ = v___x_531_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_k_535_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_v_536_);
lean_ctor_set(v_reuseFailAlloc_556_, 3, v___y_549_);
lean_ctor_set(v_reuseFailAlloc_556_, 4, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
v___jp_559_:
{
lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_561_ = lean_nat_add(v___x_558_, v___y_560_);
lean_dec(v___y_560_);
lean_dec(v___x_558_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v_l_537_);
lean_ctor_set(v___x_372_, 3, v_l_520_);
lean_ctor_set(v___x_372_, 2, v_v_519_);
lean_ctor_set(v___x_372_, 1, v_k_518_);
lean_ctor_set(v___x_372_, 0, v___x_561_);
v___x_563_ = v___x_372_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_k_518_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v_v_519_);
lean_ctor_set(v_reuseFailAlloc_567_, 3, v_l_520_);
lean_ctor_set(v_reuseFailAlloc_567_, 4, v_l_537_);
v___x_563_ = v_reuseFailAlloc_567_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_564_; 
v___x_564_ = lean_nat_add(v___x_515_, v_size_516_);
if (lean_obj_tag(v_r_538_) == 0)
{
lean_object* v_size_565_; 
v_size_565_ = lean_ctor_get(v_r_538_, 0);
lean_inc(v_size_565_);
v___y_548_ = v___x_564_;
v___y_549_ = v___x_563_;
v___y_550_ = v_size_565_;
goto v___jp_547_;
}
else
{
lean_object* v___x_566_; 
v___x_566_ = lean_unsigned_to_nat(0u);
v___y_548_ = v___x_564_;
v___y_549_ = v___x_563_;
v___y_550_ = v___x_566_;
goto v___jp_547_;
}
}
}
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
lean_del_object(v___x_372_);
v___x_576_ = lean_nat_add(v___x_515_, v_size_517_);
lean_dec(v_size_517_);
v___x_577_ = lean_nat_add(v___x_576_, v_size_516_);
lean_dec(v___x_576_);
v___x_578_ = lean_nat_add(v___x_515_, v_size_516_);
v___x_579_ = lean_nat_add(v___x_578_, v_size_534_);
lean_dec(v___x_578_);
lean_inc_ref(v_r_370_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 4, v_r_370_);
lean_ctor_set(v___x_531_, 3, v_r_521_);
lean_ctor_set(v___x_531_, 2, v_v_368_);
lean_ctor_set(v___x_531_, 1, v_k_367_);
lean_ctor_set(v___x_531_, 0, v___x_579_);
v___x_581_ = v___x_531_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_594_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_594_, 3, v_r_521_);
lean_ctor_set(v_reuseFailAlloc_594_, 4, v_r_370_);
v___x_581_ = v_reuseFailAlloc_594_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
v_isSharedCheck_588_ = !lean_is_exclusive(v_r_370_);
if (v_isSharedCheck_588_ == 0)
{
lean_object* v_unused_589_; lean_object* v_unused_590_; lean_object* v_unused_591_; lean_object* v_unused_592_; lean_object* v_unused_593_; 
v_unused_589_ = lean_ctor_get(v_r_370_, 4);
lean_dec(v_unused_589_);
v_unused_590_ = lean_ctor_get(v_r_370_, 3);
lean_dec(v_unused_590_);
v_unused_591_ = lean_ctor_get(v_r_370_, 2);
lean_dec(v_unused_591_);
v_unused_592_ = lean_ctor_get(v_r_370_, 1);
lean_dec(v_unused_592_);
v_unused_593_ = lean_ctor_get(v_r_370_, 0);
lean_dec(v_unused_593_);
v___x_583_ = v_r_370_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_dec(v_r_370_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 4, v___x_581_);
lean_ctor_set(v___x_583_, 3, v_l_520_);
lean_ctor_set(v___x_583_, 2, v_v_519_);
lean_ctor_set(v___x_583_, 1, v_k_518_);
lean_ctor_set(v___x_583_, 0, v___x_577_);
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_k_518_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v_v_519_);
lean_ctor_set(v_reuseFailAlloc_587_, 3, v_l_520_);
lean_ctor_set(v_reuseFailAlloc_587_, 4, v___x_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_601_; 
v_l_601_ = lean_ctor_get(v_impl_514_, 3);
lean_inc(v_l_601_);
if (lean_obj_tag(v_l_601_) == 0)
{
lean_object* v_r_602_; lean_object* v_k_603_; lean_object* v_v_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_615_; 
v_r_602_ = lean_ctor_get(v_impl_514_, 4);
v_k_603_ = lean_ctor_get(v_impl_514_, 1);
v_v_604_ = lean_ctor_get(v_impl_514_, 2);
v_isSharedCheck_615_ = !lean_is_exclusive(v_impl_514_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; lean_object* v_unused_617_; 
v_unused_616_ = lean_ctor_get(v_impl_514_, 3);
lean_dec(v_unused_616_);
v_unused_617_ = lean_ctor_get(v_impl_514_, 0);
lean_dec(v_unused_617_);
v___x_606_ = v_impl_514_;
v_isShared_607_ = v_isSharedCheck_615_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_r_602_);
lean_inc(v_v_604_);
lean_inc(v_k_603_);
lean_dec(v_impl_514_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_615_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_602_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 3, v_r_602_);
lean_ctor_set(v___x_606_, 2, v_v_368_);
lean_ctor_set(v___x_606_, 1, v_k_367_);
lean_ctor_set(v___x_606_, 0, v___x_515_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_614_, 3, v_r_602_);
lean_ctor_set(v_reuseFailAlloc_614_, 4, v_r_602_);
v___x_610_ = v_reuseFailAlloc_614_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_612_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v___x_610_);
lean_ctor_set(v___x_372_, 3, v_l_601_);
lean_ctor_set(v___x_372_, 2, v_v_604_);
lean_ctor_set(v___x_372_, 1, v_k_603_);
lean_ctor_set(v___x_372_, 0, v___x_608_);
v___x_612_ = v___x_372_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_k_603_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_v_604_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v_l_601_);
lean_ctor_set(v_reuseFailAlloc_613_, 4, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
else
{
lean_object* v_r_618_; 
v_r_618_ = lean_ctor_get(v_impl_514_, 4);
lean_inc(v_r_618_);
if (lean_obj_tag(v_r_618_) == 0)
{
lean_object* v_k_619_; lean_object* v_v_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_643_; 
v_k_619_ = lean_ctor_get(v_impl_514_, 1);
v_v_620_ = lean_ctor_get(v_impl_514_, 2);
v_isSharedCheck_643_ = !lean_is_exclusive(v_impl_514_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; lean_object* v_unused_645_; lean_object* v_unused_646_; 
v_unused_644_ = lean_ctor_get(v_impl_514_, 4);
lean_dec(v_unused_644_);
v_unused_645_ = lean_ctor_get(v_impl_514_, 3);
lean_dec(v_unused_645_);
v_unused_646_ = lean_ctor_get(v_impl_514_, 0);
lean_dec(v_unused_646_);
v___x_622_ = v_impl_514_;
v_isShared_623_ = v_isSharedCheck_643_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_v_620_);
lean_inc(v_k_619_);
lean_dec(v_impl_514_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_643_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_k_624_; lean_object* v_v_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_639_; 
v_k_624_ = lean_ctor_get(v_r_618_, 1);
v_v_625_ = lean_ctor_get(v_r_618_, 2);
v_isSharedCheck_639_ = !lean_is_exclusive(v_r_618_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; lean_object* v_unused_641_; lean_object* v_unused_642_; 
v_unused_640_ = lean_ctor_get(v_r_618_, 4);
lean_dec(v_unused_640_);
v_unused_641_ = lean_ctor_get(v_r_618_, 3);
lean_dec(v_unused_641_);
v_unused_642_ = lean_ctor_get(v_r_618_, 0);
lean_dec(v_unused_642_);
v___x_627_ = v_r_618_;
v_isShared_628_ = v_isSharedCheck_639_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_v_625_);
lean_inc(v_k_624_);
lean_dec(v_r_618_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_639_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_629_ = lean_unsigned_to_nat(3u);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 4, v_l_601_);
lean_ctor_set(v___x_627_, 3, v_l_601_);
lean_ctor_set(v___x_627_, 2, v_v_620_);
lean_ctor_set(v___x_627_, 1, v_k_619_);
lean_ctor_set(v___x_627_, 0, v___x_515_);
v___x_631_ = v___x_627_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v_l_601_);
lean_ctor_set(v_reuseFailAlloc_638_, 4, v_l_601_);
v___x_631_ = v_reuseFailAlloc_638_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_633_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 4, v_l_601_);
lean_ctor_set(v___x_622_, 2, v_v_368_);
lean_ctor_set(v___x_622_, 1, v_k_367_);
lean_ctor_set(v___x_622_, 0, v___x_515_);
v___x_633_ = v___x_622_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_l_601_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v_l_601_);
v___x_633_ = v_reuseFailAlloc_637_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_635_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v___x_633_);
lean_ctor_set(v___x_372_, 3, v___x_631_);
lean_ctor_set(v___x_372_, 2, v_v_625_);
lean_ctor_set(v___x_372_, 1, v_k_624_);
lean_ctor_set(v___x_372_, 0, v___x_629_);
v___x_635_ = v___x_372_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_k_624_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_v_625_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v___x_633_);
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
lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_647_ = lean_unsigned_to_nat(2u);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v_r_618_);
lean_ctor_set(v___x_372_, 3, v_impl_514_);
lean_ctor_set(v___x_372_, 0, v___x_647_);
v___x_649_ = v___x_372_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_650_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_650_, 3, v_impl_514_);
lean_ctor_set(v_reuseFailAlloc_650_, 4, v_r_618_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_unsigned_to_nat(1u);
v___x_653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v_k_363_);
lean_ctor_set(v___x_653_, 2, v_v_364_);
lean_ctor_set(v___x_653_, 3, v_t_365_);
lean_ctor_set(v___x_653_, 4, v_t_365_);
return v___x_653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(lean_object* v_a_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_661_; lean_object* v_fst_662_; lean_object* v_snd_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_696_; 
v___x_661_ = lean_st_ref_get(v___y_655_);
v_fst_662_ = lean_ctor_get(v_a_654_, 0);
v_snd_663_ = lean_ctor_get(v_a_654_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v_a_654_);
if (v_isSharedCheck_696_ == 0)
{
v___x_665_ = v_a_654_;
v_isShared_666_ = v_isSharedCheck_696_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_snd_663_);
lean_inc(v_fst_662_);
lean_dec(v_a_654_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_696_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; 
lean_inc(v_snd_663_);
v___x_667_ = l_Lean_Meta_Grind_Goal_getENode(v___x_661_, v_snd_663_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___x_661_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_687_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_687_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_687_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_687_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v_self_672_; lean_object* v_target_x3f_673_; lean_object* v_idx_674_; lean_object* v___x_675_; 
v_self_672_ = lean_ctor_get(v_a_668_, 0);
lean_inc_ref(v_self_672_);
v_target_x3f_673_ = lean_ctor_get(v_a_668_, 4);
lean_inc(v_target_x3f_673_);
v_idx_674_ = lean_ctor_get(v_a_668_, 7);
lean_inc(v_idx_674_);
lean_dec(v_a_668_);
v___x_675_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_idx_674_, v_self_672_, v_fst_662_);
if (lean_obj_tag(v_target_x3f_673_) == 1)
{
lean_object* v_val_676_; lean_object* v___x_678_; 
lean_del_object(v___x_670_);
lean_dec(v_snd_663_);
v_val_676_ = lean_ctor_get(v_target_x3f_673_, 0);
lean_inc(v_val_676_);
lean_dec_ref_known(v_target_x3f_673_, 1);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v_val_676_);
lean_ctor_set(v___x_665_, 0, v___x_675_);
v___x_678_ = v___x_665_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_val_676_);
v___x_678_ = v_reuseFailAlloc_680_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
v_a_654_ = v___x_678_;
goto _start;
}
}
else
{
lean_object* v___x_682_; 
lean_dec(v_target_x3f_673_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_675_);
v___x_682_ = v___x_665_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_snd_663_);
v___x_682_ = v_reuseFailAlloc_686_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_684_; 
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_682_);
v___x_684_ = v___x_670_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_del_object(v___x_665_);
lean_dec(v_snd_663_);
lean_dec(v_fst_662_);
v_a_688_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_667_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_667_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg___boxed(lean_object* v_a_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(v_a_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
return v_res_704_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_705_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_706_ = lean_unsigned_to_nat(2u);
v___x_707_ = lean_unsigned_to_nat(89u);
v___x_708_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__1));
v___x_709_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_710_ = l_mkPanicMessageWithDecl(v___x_709_, v___x_708_, v___x_707_, v___x_706_, v___x_705_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(lean_object* v_lhs_711_, lean_object* v_rhs_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_visited_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_visited_724_ = lean_box(1);
v___x_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_725_, 0, v_visited_724_);
lean_ctor_set(v___x_725_, 1, v_lhs_711_);
v___x_726_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(v___x_725_, v_a_713_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v_fst_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_757_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_726_, 1);
v_fst_728_ = lean_ctor_get(v_a_727_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v_a_727_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; 
v_unused_758_ = lean_ctor_get(v_a_727_, 1);
lean_dec(v_unused_758_);
v___x_730_ = v_a_727_;
v_isShared_731_ = v_isSharedCheck_757_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_fst_728_);
lean_dec(v_a_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_757_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_732_ = lean_box(0);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v_rhs_712_);
lean_ctor_set(v___x_730_, 0, v___x_732_);
v___x_734_ = v___x_730_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_rhs_712_);
v___x_734_ = v_reuseFailAlloc_756_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_735_; 
v___x_735_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(v_fst_728_, v___x_734_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
lean_dec(v_fst_728_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_747_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_747_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_747_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_747_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v_fst_740_; 
v_fst_740_ = lean_ctor_get(v_a_736_, 0);
lean_inc(v_fst_740_);
lean_dec(v_a_736_);
if (lean_obj_tag(v_fst_740_) == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; 
lean_del_object(v___x_738_);
v___x_741_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0);
v___x_742_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_741_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
return v___x_742_;
}
else
{
lean_object* v_val_743_; lean_object* v___x_745_; 
v_val_743_ = lean_ctor_get(v_fst_740_, 0);
lean_inc(v_val_743_);
lean_dec_ref_known(v_fst_740_, 1);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v_val_743_);
v___x_745_ = v___x_738_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_val_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
v_a_748_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_735_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_735_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
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
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec_ref(v_rhs_712_);
v_a_759_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_726_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_726_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___boxed(lean_object* v_lhs_767_, lean_object* v_rhs_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(v_lhs_767_, v_rhs_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec(v_a_770_);
lean_dec(v_a_769_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0(lean_object* v_00_u03b2_781_, lean_object* v_k_782_, lean_object* v_v_783_, lean_object* v_t_784_, lean_object* v_hl_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_k_782_, v_v_783_, v_t_784_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1(lean_object* v_inst_787_, lean_object* v_a_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(v_a_788_, v___y_789_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___boxed(lean_object* v_inst_801_, lean_object* v_a_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1(v_inst_801_, v_a_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec(v___y_803_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2(lean_object* v_00_u03b4_815_, lean_object* v_t_816_, lean_object* v_k_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(v_t_816_, v_k_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___boxed(lean_object* v_00_u03b4_819_, lean_object* v_t_820_, lean_object* v_k_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2(v_00_u03b4_819_, v_t_820_, v_k_821_);
lean_dec(v_k_821_);
lean_dec(v_t_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4(lean_object* v___x_823_, lean_object* v_inst_824_, lean_object* v_a_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(v___x_823_, v_a_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___boxed(lean_object* v___x_838_, lean_object* v_inst_839_, lean_object* v_a_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4(v___x_838_, v_inst_839_, v_a_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec(v___y_841_);
lean_dec(v___x_838_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(lean_object* v_info_853_, lean_object* v_lhs_854_, lean_object* v_rhs_855_, lean_object* v_i_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
uint8_t v___x_868_; 
v___x_868_ = l_Lean_Expr_isApp(v_lhs_854_);
if (v___x_868_ == 0)
{
uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
lean_dec(v_i_856_);
lean_dec_ref(v_rhs_855_);
lean_dec_ref(v_lhs_854_);
v___x_869_ = 1;
v___x_870_ = lean_box(v___x_869_);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
return v___x_871_;
}
else
{
lean_object* v_a_u2081_872_; lean_object* v_a_u2082_873_; lean_object* v___x_874_; lean_object* v_i_875_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; size_t v___x_890_; size_t v___x_891_; uint8_t v___x_892_; 
v_a_u2081_872_ = l_Lean_Expr_appArg_x21(v_lhs_854_);
v_a_u2082_873_ = l_Lean_Expr_appArg_x21(v_rhs_855_);
v___x_874_ = lean_unsigned_to_nat(1u);
v_i_875_ = lean_nat_sub(v_i_856_, v___x_874_);
lean_dec(v_i_856_);
v___x_890_ = lean_ptr_addr(v_a_u2081_872_);
lean_dec_ref(v_a_u2081_872_);
v___x_891_ = lean_ptr_addr(v_a_u2082_873_);
lean_dec_ref(v_a_u2082_873_);
v___x_892_ = lean_usize_dec_eq(v___x_890_, v___x_891_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_893_ = lean_array_get_size(v_info_853_);
v___x_894_ = lean_nat_dec_lt(v_i_875_, v___x_893_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; lean_object* v___x_896_; 
lean_dec(v_i_875_);
lean_dec_ref(v_rhs_855_);
lean_dec_ref(v_lhs_854_);
v___x_895_ = lean_box(v___x_892_);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
else
{
lean_object* v___x_897_; uint8_t v_hasFwdDeps_898_; 
v___x_897_ = lean_array_fget_borrowed(v_info_853_, v_i_875_);
v_hasFwdDeps_898_ = lean_ctor_get_uint8(v___x_897_, sizeof(void*)*1 + 1);
if (v_hasFwdDeps_898_ == 0)
{
v___y_877_ = v_a_857_;
v___y_878_ = v_a_858_;
v___y_879_ = v_a_859_;
v___y_880_ = v_a_860_;
v___y_881_ = v_a_861_;
v___y_882_ = v_a_862_;
v___y_883_ = v_a_863_;
v___y_884_ = v_a_864_;
v___y_885_ = v_a_865_;
v___y_886_ = v_a_866_;
goto v___jp_876_;
}
else
{
lean_object* v___x_899_; lean_object* v___x_900_; 
lean_dec(v_i_875_);
lean_dec_ref(v_rhs_855_);
lean_dec_ref(v_lhs_854_);
v___x_899_ = lean_box(v___x_892_);
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
}
}
else
{
v___y_877_ = v_a_857_;
v___y_878_ = v_a_858_;
v___y_879_ = v_a_859_;
v___y_880_ = v_a_860_;
v___y_881_ = v_a_861_;
v___y_882_ = v_a_862_;
v___y_883_ = v_a_863_;
v___y_884_ = v_a_864_;
v___y_885_ = v_a_865_;
v___y_886_ = v_a_866_;
goto v___jp_876_;
}
v___jp_876_:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = l_Lean_Expr_appFn_x21(v_lhs_854_);
lean_dec_ref(v_lhs_854_);
v___x_888_ = l_Lean_Expr_appFn_x21(v_rhs_855_);
lean_dec_ref(v_rhs_855_);
v_lhs_854_ = v___x_887_;
v_rhs_855_ = v___x_888_;
v_i_856_ = v_i_875_;
v_a_857_ = v___y_877_;
v_a_858_ = v___y_878_;
v_a_859_ = v___y_879_;
v_a_860_ = v___y_880_;
v_a_861_ = v___y_881_;
v_a_862_ = v___y_882_;
v_a_863_ = v___y_883_;
v_a_864_ = v___y_884_;
v_a_865_ = v___y_885_;
v_a_866_ = v___y_886_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop___boxed(lean_object* v_info_901_, lean_object* v_lhs_902_, lean_object* v_rhs_903_, lean_object* v_i_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(v_info_901_, v_lhs_902_, v_rhs_903_, v_i_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_info_901_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(lean_object* v_lhs_917_, lean_object* v_rhs_918_, lean_object* v_f_919_, lean_object* v_g_920_, lean_object* v_numArgs_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
size_t v___x_933_; size_t v___x_934_; uint8_t v___x_935_; 
v___x_933_ = lean_ptr_addr(v_f_919_);
v___x_934_ = lean_ptr_addr(v_g_920_);
v___x_935_ = lean_usize_dec_eq(v___x_933_, v___x_934_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec(v_numArgs_921_);
lean_dec_ref(v_f_919_);
lean_dec_ref(v_rhs_918_);
lean_dec_ref(v_lhs_917_);
v___x_936_ = lean_box(v___x_935_);
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
return v___x_937_;
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = lean_box(0);
v___x_939_ = l_Lean_Meta_getFunInfo(v_f_919_, v___x_938_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v_paramInfo_941_; lean_object* v___x_942_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_a_940_);
lean_dec_ref_known(v___x_939_, 1);
v_paramInfo_941_ = lean_ctor_get(v_a_940_, 0);
lean_inc_ref(v_paramInfo_941_);
lean_dec(v_a_940_);
v___x_942_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(v_paramInfo_941_, v_lhs_917_, v_rhs_918_, v_numArgs_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
lean_dec_ref(v_paramInfo_941_);
return v___x_942_;
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec(v_numArgs_921_);
lean_dec_ref(v_rhs_918_);
lean_dec_ref(v_lhs_917_);
v_a_943_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_939_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_939_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget___boxed(lean_object* v_lhs_951_, lean_object* v_rhs_952_, lean_object* v_f_953_, lean_object* v_g_954_, lean_object* v_numArgs_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(v_lhs_951_, v_rhs_952_, v_f_953_, v_g_954_, v_numArgs_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec(v_a_956_);
lean_dec_ref(v_g_954_);
return v_res_967_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0(void){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(lean_object* v_msg_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; lean_object* v___x_123301__overap_982_; lean_object* v___x_983_; 
v___x_981_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0);
v___x_123301__overap_982_ = lean_panic_fn_borrowed(v___x_981_, v_msg_969_);
lean_inc(v___y_979_);
lean_inc_ref(v___y_978_);
lean_inc(v___y_977_);
lean_inc_ref(v___y_976_);
lean_inc(v___y_975_);
lean_inc_ref(v___y_974_);
lean_inc(v___y_973_);
lean_inc_ref(v___y_972_);
lean_inc(v___y_971_);
lean_inc(v___y_970_);
v___x_983_ = lean_apply_11(v___x_123301__overap_982_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, lean_box(0));
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___boxed(lean_object* v_msg_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v_msg_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec(v___y_985_);
return v_res_996_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = l_Lean_maxRecDepthErrorMessage;
v___x_1003_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
return v___x_1003_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3);
v___x_1005_ = l_Lean_MessageData_ofFormat(v___x_1004_);
return v___x_1005_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4);
v___x_1007_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__2));
v___x_1008_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(lean_object* v_ref_1009_){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1011_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5);
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v_ref_1009_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___boxed(lean_object* v_ref_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1014_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0(lean_object* v_k_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v_b_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; 
lean_inc(v___y_1028_);
lean_inc_ref(v___y_1027_);
lean_inc(v___y_1026_);
lean_inc_ref(v___y_1025_);
lean_inc(v___y_1023_);
lean_inc_ref(v___y_1022_);
lean_inc(v___y_1021_);
lean_inc_ref(v___y_1020_);
lean_inc(v___y_1019_);
lean_inc(v___y_1018_);
v___x_1030_ = lean_apply_12(v_k_1017_, v_b_1024_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, lean_box(0));
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0___boxed(lean_object* v_k_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v_b_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0(v_k_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v_b_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec(v___y_1032_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(lean_object* v_name_1045_, uint8_t v_bi_1046_, lean_object* v_type_1047_, lean_object* v_k_1048_, uint8_t v_kind_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v___f_1061_; lean_object* v___x_1062_; 
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___y_1051_);
lean_inc(v___y_1050_);
v___f_1061_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_1061_, 0, v_k_1048_);
lean_closure_set(v___f_1061_, 1, v___y_1050_);
lean_closure_set(v___f_1061_, 2, v___y_1051_);
lean_closure_set(v___f_1061_, 3, v___y_1052_);
lean_closure_set(v___f_1061_, 4, v___y_1053_);
lean_closure_set(v___f_1061_, 5, v___y_1054_);
lean_closure_set(v___f_1061_, 6, v___y_1055_);
v___x_1062_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1045_, v_bi_1046_, v_type_1047_, v___f_1061_, v_kind_1049_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
if (lean_obj_tag(v___x_1062_) == 0)
{
return v___x_1062_;
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___boxed(lean_object* v_name_1071_, lean_object* v_bi_1072_, lean_object* v_type_1073_, lean_object* v_k_1074_, lean_object* v_kind_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
uint8_t v_bi_boxed_1087_; uint8_t v_kind_boxed_1088_; lean_object* v_res_1089_; 
v_bi_boxed_1087_ = lean_unbox(v_bi_1072_);
v_kind_boxed_1088_ = lean_unbox(v_kind_1075_);
v_res_1089_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_1071_, v_bi_boxed_1087_, v_type_1073_, v_k_1074_, v_kind_boxed_1088_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec(v___y_1076_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(lean_object* v_name_1090_, lean_object* v_type_1091_, lean_object* v_k_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
uint8_t v___x_1104_; uint8_t v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = 0;
v___x_1105_ = 0;
v___x_1106_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_1090_, v___x_1104_, v_type_1091_, v_k_1092_, v___x_1105_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg___boxed(lean_object* v_name_1107_, lean_object* v_type_1108_, lean_object* v_k_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_name_1107_, v_type_1108_, v_k_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec(v___y_1110_);
return v_res_1121_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1122_; lean_object* v_dummy_1123_; 
v___x_1122_ = lean_box(0);
v_dummy_1123_ = l_Lean_Expr_sort___override(v___x_1122_);
return v_dummy_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0(lean_object* v_numArgs_1124_, lean_object* v_rhs_1125_, lean_object* v_lhs_1126_, uint8_t v___x_1127_, uint8_t v___x_1128_, lean_object* v_x_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v_dummy_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v_dummy_1141_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0);
lean_inc(v_numArgs_1124_);
v___x_1142_ = lean_mk_array(v_numArgs_1124_, v_dummy_1141_);
v___x_1143_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_numArgs_1124_, v_rhs_1125_, v___x_1142_);
lean_inc_ref(v_x_1129_);
v___x_1144_ = l_Lean_mkAppN(v_x_1129_, v___x_1143_);
lean_dec_ref(v___x_1143_);
v___x_1145_ = l_Lean_Meta_mkHEq(v_lhs_1126_, v___x_1144_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; lean_object* v___x_1151_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
v___x_1147_ = lean_unsigned_to_nat(1u);
v___x_1148_ = lean_mk_empty_array_with_capacity(v___x_1147_);
v___x_1149_ = lean_array_push(v___x_1148_, v_x_1129_);
v___x_1150_ = 1;
v___x_1151_ = l_Lean_Meta_mkLambdaFVars(v___x_1149_, v_a_1146_, v___x_1127_, v___x_1128_, v___x_1127_, v___x_1128_, v___x_1150_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec_ref(v___x_1149_);
return v___x_1151_;
}
else
{
lean_dec_ref(v_x_1129_);
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___boxed(lean_object** _args){
lean_object* v_numArgs_1152_ = _args[0];
lean_object* v_rhs_1153_ = _args[1];
lean_object* v_lhs_1154_ = _args[2];
lean_object* v___x_1155_ = _args[3];
lean_object* v___x_1156_ = _args[4];
lean_object* v_x_1157_ = _args[5];
lean_object* v___y_1158_ = _args[6];
lean_object* v___y_1159_ = _args[7];
lean_object* v___y_1160_ = _args[8];
lean_object* v___y_1161_ = _args[9];
lean_object* v___y_1162_ = _args[10];
lean_object* v___y_1163_ = _args[11];
lean_object* v___y_1164_ = _args[12];
lean_object* v___y_1165_ = _args[13];
lean_object* v___y_1166_ = _args[14];
lean_object* v___y_1167_ = _args[15];
lean_object* v___y_1168_ = _args[16];
_start:
{
uint8_t v___x_131229__boxed_1169_; uint8_t v___x_131230__boxed_1170_; lean_object* v_res_1171_; 
v___x_131229__boxed_1169_ = lean_unbox(v___x_1155_);
v___x_131230__boxed_1170_ = lean_unbox(v___x_1156_);
v_res_1171_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0(v_numArgs_1152_, v_rhs_1153_, v_lhs_1154_, v___x_131229__boxed_1169_, v___x_131230__boxed_1170_, v_x_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec(v___y_1158_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_spec__13(lean_object* v_msg_1172_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = l_Lean_instInhabitedExpr;
v___x_1174_ = lean_panic_fn_borrowed(v___x_1173_, v_msg_1172_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(lean_object* v_msgData_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; lean_object* v_env_1182_; lean_object* v___x_1183_; lean_object* v_mctx_1184_; lean_object* v_lctx_1185_; lean_object* v_options_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1181_ = lean_st_ref_get(v___y_1179_);
v_env_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc_ref(v_env_1182_);
lean_dec(v___x_1181_);
v___x_1183_ = lean_st_ref_get(v___y_1177_);
v_mctx_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc_ref(v_mctx_1184_);
lean_dec(v___x_1183_);
v_lctx_1185_ = lean_ctor_get(v___y_1176_, 2);
v_options_1186_ = lean_ctor_get(v___y_1178_, 2);
lean_inc_ref(v_options_1186_);
lean_inc_ref(v_lctx_1185_);
v___x_1187_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1187_, 0, v_env_1182_);
lean_ctor_set(v___x_1187_, 1, v_mctx_1184_);
lean_ctor_set(v___x_1187_, 2, v_lctx_1185_);
lean_ctor_set(v___x_1187_, 3, v_options_1186_);
v___x_1188_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
lean_ctor_set(v___x_1188_, 1, v_msgData_1175_);
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
v_ref_1203_ = lean_ctor_get(v___y_1200_, 5);
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
lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; uint8_t v___y_1359_; lean_object* v___y_1360_; uint8_t v___y_1361_; lean_object* v_fileName_1397_; lean_object* v_fileMap_1398_; lean_object* v_options_1399_; lean_object* v_currRecDepth_1400_; lean_object* v_maxRecDepth_1401_; lean_object* v_ref_1402_; lean_object* v_currNamespace_1403_; lean_object* v_openDecls_1404_; lean_object* v_initHeartbeats_1405_; lean_object* v_maxHeartbeats_1406_; lean_object* v_quotContext_1407_; lean_object* v_currMacroScope_1408_; uint8_t v_diag_1409_; lean_object* v_cancelTk_x3f_1410_; uint8_t v_suppressElabErrors_1411_; lean_object* v_inheritedTraceOptions_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
v_fileName_1397_ = lean_ctor_get(v_a_1322_, 0);
v_fileMap_1398_ = lean_ctor_get(v_a_1322_, 1);
v_options_1399_ = lean_ctor_get(v_a_1322_, 2);
v_currRecDepth_1400_ = lean_ctor_get(v_a_1322_, 3);
v_maxRecDepth_1401_ = lean_ctor_get(v_a_1322_, 4);
v_ref_1402_ = lean_ctor_get(v_a_1322_, 5);
v_currNamespace_1403_ = lean_ctor_get(v_a_1322_, 6);
v_openDecls_1404_ = lean_ctor_get(v_a_1322_, 7);
v_initHeartbeats_1405_ = lean_ctor_get(v_a_1322_, 8);
v_maxHeartbeats_1406_ = lean_ctor_get(v_a_1322_, 9);
v_quotContext_1407_ = lean_ctor_get(v_a_1322_, 10);
v_currMacroScope_1408_ = lean_ctor_get(v_a_1322_, 11);
v_diag_1409_ = lean_ctor_get_uint8(v_a_1322_, sizeof(void*)*14);
v_cancelTk_x3f_1410_ = lean_ctor_get(v_a_1322_, 12);
v_suppressElabErrors_1411_ = lean_ctor_get_uint8(v_a_1322_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1412_ = lean_ctor_get(v_a_1322_, 13);
v___x_1413_ = l_Lean_Expr_cleanupAnnotations(v_lhs_1312_);
v___x_1414_ = l_Lean_Expr_isApp(v___x_1413_);
v___x_1444_ = lean_unsigned_to_nat(0u);
v___x_1445_ = lean_nat_dec_eq(v_maxRecDepth_1401_, v___x_1444_);
if (v___x_1445_ == 0)
{
uint8_t v___x_1446_; 
v___x_1446_ = lean_nat_dec_eq(v_currRecDepth_1400_, v_maxRecDepth_1401_);
if (v___x_1446_ == 0)
{
goto v___jp_1415_;
}
else
{
lean_object* v___x_1447_; 
lean_dec_ref(v___x_1413_);
lean_dec_ref(v_rhs_1313_);
lean_inc(v_ref_1402_);
v___x_1447_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1402_);
return v___x_1447_;
}
}
else
{
goto v___jp_1415_;
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
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec_ref(v___y_1352_);
v___x_1362_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4);
v___x_1363_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1362_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v___y_1358_, v_a_1323_);
lean_dec_ref(v___y_1358_);
return v___x_1363_;
}
else
{
lean_object* v___x_1364_; size_t v___x_1365_; size_t v___x_1366_; uint8_t v___x_1367_; 
v___x_1364_ = l_Lean_Expr_constLevels_x21(v___y_1352_);
lean_dec_ref(v___y_1352_);
v___x_1365_ = lean_ptr_addr(v___y_1353_);
v___x_1366_ = lean_ptr_addr(v___y_1355_);
v___x_1367_ = lean_usize_dec_eq(v___x_1365_, v___x_1366_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; 
lean_inc_ref(v___y_1357_);
lean_inc_ref(v___y_1360_);
v___x_1368_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1360_, v___y_1357_, v___y_1359_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v___y_1358_, v_a_1323_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1370_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1368_, 1);
lean_inc_ref(v___y_1354_);
lean_inc_ref(v___y_1356_);
v___x_1370_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1356_, v___y_1354_, v___y_1359_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v___y_1358_, v_a_1323_);
lean_dec_ref(v___y_1358_);
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
v___x_1377_ = l_Lean_mkApp8(v___x_1376_, v___y_1353_, v___y_1355_, v___y_1360_, v___y_1356_, v___y_1354_, v___y_1357_, v_a_1369_, v_a_1371_);
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
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v___x_1370_;
}
}
else
{
lean_dec(v___x_1364_);
lean_dec_ref(v___y_1360_);
lean_dec_ref(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v___x_1368_;
}
}
else
{
uint8_t v___x_1382_; lean_object* v___x_1383_; 
lean_dec_ref(v___y_1355_);
v___x_1382_ = 0;
lean_inc_ref(v___y_1357_);
lean_inc_ref(v___y_1360_);
v___x_1383_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1360_, v___y_1357_, v___x_1382_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v___y_1358_, v_a_1323_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1385_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1383_, 1);
lean_inc_ref(v___y_1354_);
lean_inc_ref(v___y_1356_);
v___x_1385_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1356_, v___y_1354_, v___x_1382_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v___y_1358_, v_a_1323_);
lean_dec_ref(v___y_1358_);
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
v___x_1392_ = l_Lean_mkApp7(v___x_1391_, v___y_1353_, v___y_1360_, v___y_1356_, v___y_1354_, v___y_1357_, v_a_1384_, v_a_1386_);
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
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v___x_1385_;
}
}
else
{
lean_dec(v___x_1364_);
lean_dec_ref(v___y_1360_);
lean_dec_ref(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v___x_1383_;
}
}
}
}
v___jp_1415_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1416_ = lean_unsigned_to_nat(1u);
v___x_1417_ = lean_nat_add(v_currRecDepth_1400_, v___x_1416_);
lean_inc_ref(v_inheritedTraceOptions_1412_);
lean_inc(v_cancelTk_x3f_1410_);
lean_inc(v_currMacroScope_1408_);
lean_inc(v_quotContext_1407_);
lean_inc(v_maxHeartbeats_1406_);
lean_inc(v_initHeartbeats_1405_);
lean_inc(v_openDecls_1404_);
lean_inc(v_currNamespace_1403_);
lean_inc(v_ref_1402_);
lean_inc(v_maxRecDepth_1401_);
lean_inc_ref(v_options_1399_);
lean_inc_ref(v_fileMap_1398_);
lean_inc_ref(v_fileName_1397_);
v___x_1418_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1418_, 0, v_fileName_1397_);
lean_ctor_set(v___x_1418_, 1, v_fileMap_1398_);
lean_ctor_set(v___x_1418_, 2, v_options_1399_);
lean_ctor_set(v___x_1418_, 3, v___x_1417_);
lean_ctor_set(v___x_1418_, 4, v_maxRecDepth_1401_);
lean_ctor_set(v___x_1418_, 5, v_ref_1402_);
lean_ctor_set(v___x_1418_, 6, v_currNamespace_1403_);
lean_ctor_set(v___x_1418_, 7, v_openDecls_1404_);
lean_ctor_set(v___x_1418_, 8, v_initHeartbeats_1405_);
lean_ctor_set(v___x_1418_, 9, v_maxHeartbeats_1406_);
lean_ctor_set(v___x_1418_, 10, v_quotContext_1407_);
lean_ctor_set(v___x_1418_, 11, v_currMacroScope_1408_);
lean_ctor_set(v___x_1418_, 12, v_cancelTk_x3f_1410_);
lean_ctor_set(v___x_1418_, 13, v_inheritedTraceOptions_1412_);
lean_ctor_set_uint8(v___x_1418_, sizeof(void*)*14, v_diag_1409_);
lean_ctor_set_uint8(v___x_1418_, sizeof(void*)*14 + 1, v_suppressElabErrors_1411_);
if (v___x_1414_ == 0)
{
lean_dec_ref(v___x_1413_);
lean_dec_ref(v_rhs_1313_);
v___y_1326_ = v_a_1314_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v_a_1316_;
v___y_1329_ = v_a_1317_;
v___y_1330_ = v_a_1318_;
v___y_1331_ = v_a_1319_;
v___y_1332_ = v_a_1320_;
v___y_1333_ = v_a_1321_;
v___y_1334_ = v___x_1418_;
v___y_1335_ = v_a_1323_;
goto v___jp_1325_;
}
else
{
lean_object* v_arg_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v_arg_1419_ = lean_ctor_get(v___x_1413_, 1);
lean_inc_ref(v_arg_1419_);
v___x_1420_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1413_);
v___x_1421_ = l_Lean_Expr_isApp(v___x_1420_);
if (v___x_1421_ == 0)
{
lean_dec_ref(v___x_1420_);
lean_dec_ref(v_arg_1419_);
lean_dec_ref(v_rhs_1313_);
v___y_1326_ = v_a_1314_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v_a_1316_;
v___y_1329_ = v_a_1317_;
v___y_1330_ = v_a_1318_;
v___y_1331_ = v_a_1319_;
v___y_1332_ = v_a_1320_;
v___y_1333_ = v_a_1321_;
v___y_1334_ = v___x_1418_;
v___y_1335_ = v_a_1323_;
goto v___jp_1325_;
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
lean_dec_ref(v_rhs_1313_);
v___y_1326_ = v_a_1314_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v_a_1316_;
v___y_1329_ = v_a_1317_;
v___y_1330_ = v_a_1318_;
v___y_1331_ = v_a_1319_;
v___y_1332_ = v_a_1320_;
v___y_1333_ = v_a_1321_;
v___y_1334_ = v___x_1418_;
v___y_1335_ = v_a_1323_;
goto v___jp_1325_;
}
else
{
lean_object* v_arg_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v_arg_1425_ = lean_ctor_get(v___x_1423_, 1);
lean_inc_ref(v_arg_1425_);
v___x_1426_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1423_);
v___x_1427_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_1428_ = l_Lean_Expr_isConstOf(v___x_1426_, v___x_1427_);
if (v___x_1428_ == 0)
{
lean_dec_ref(v___x_1426_);
lean_dec_ref(v_arg_1425_);
lean_dec_ref(v_arg_1422_);
lean_dec_ref(v_arg_1419_);
lean_dec_ref(v_rhs_1313_);
v___y_1326_ = v_a_1314_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v_a_1316_;
v___y_1329_ = v_a_1317_;
v___y_1330_ = v_a_1318_;
v___y_1331_ = v_a_1319_;
v___y_1332_ = v_a_1320_;
v___y_1333_ = v_a_1321_;
v___y_1334_ = v___x_1418_;
v___y_1335_ = v_a_1323_;
goto v___jp_1325_;
}
else
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = l_Lean_Expr_cleanupAnnotations(v_rhs_1313_);
v___x_1430_ = l_Lean_Expr_isApp(v___x_1429_);
if (v___x_1430_ == 0)
{
lean_dec_ref(v___x_1429_);
lean_dec_ref(v___x_1426_);
lean_dec_ref(v_arg_1425_);
lean_dec_ref(v_arg_1422_);
lean_dec_ref(v_arg_1419_);
v___y_1339_ = v_a_1314_;
v___y_1340_ = v_a_1315_;
v___y_1341_ = v_a_1316_;
v___y_1342_ = v_a_1317_;
v___y_1343_ = v_a_1318_;
v___y_1344_ = v_a_1319_;
v___y_1345_ = v_a_1320_;
v___y_1346_ = v_a_1321_;
v___y_1347_ = v___x_1418_;
v___y_1348_ = v_a_1323_;
goto v___jp_1338_;
}
else
{
lean_object* v_arg_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v_arg_1431_ = lean_ctor_get(v___x_1429_, 1);
lean_inc_ref(v_arg_1431_);
v___x_1432_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1429_);
v___x_1433_ = l_Lean_Expr_isApp(v___x_1432_);
if (v___x_1433_ == 0)
{
lean_dec_ref(v___x_1432_);
lean_dec_ref(v_arg_1431_);
lean_dec_ref(v___x_1426_);
lean_dec_ref(v_arg_1425_);
lean_dec_ref(v_arg_1422_);
lean_dec_ref(v_arg_1419_);
v___y_1339_ = v_a_1314_;
v___y_1340_ = v_a_1315_;
v___y_1341_ = v_a_1316_;
v___y_1342_ = v_a_1317_;
v___y_1343_ = v_a_1318_;
v___y_1344_ = v_a_1319_;
v___y_1345_ = v_a_1320_;
v___y_1346_ = v_a_1321_;
v___y_1347_ = v___x_1418_;
v___y_1348_ = v_a_1323_;
goto v___jp_1338_;
}
else
{
lean_object* v_arg_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v_arg_1434_ = lean_ctor_get(v___x_1432_, 1);
lean_inc_ref(v_arg_1434_);
v___x_1435_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1432_);
v___x_1436_ = l_Lean_Expr_isApp(v___x_1435_);
if (v___x_1436_ == 0)
{
lean_dec_ref(v___x_1435_);
lean_dec_ref(v_arg_1434_);
lean_dec_ref(v_arg_1431_);
lean_dec_ref(v___x_1426_);
lean_dec_ref(v_arg_1425_);
lean_dec_ref(v_arg_1422_);
lean_dec_ref(v_arg_1419_);
v___y_1339_ = v_a_1314_;
v___y_1340_ = v_a_1315_;
v___y_1341_ = v_a_1316_;
v___y_1342_ = v_a_1317_;
v___y_1343_ = v_a_1318_;
v___y_1344_ = v_a_1319_;
v___y_1345_ = v_a_1320_;
v___y_1346_ = v_a_1321_;
v___y_1347_ = v___x_1418_;
v___y_1348_ = v_a_1323_;
goto v___jp_1338_;
}
else
{
lean_object* v_arg_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v_arg_1437_ = lean_ctor_get(v___x_1435_, 1);
lean_inc_ref(v_arg_1437_);
v___x_1438_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1435_);
v___x_1439_ = l_Lean_Expr_isConstOf(v___x_1438_, v___x_1427_);
lean_dec_ref(v___x_1438_);
if (v___x_1439_ == 0)
{
lean_dec_ref(v_arg_1437_);
lean_dec_ref(v_arg_1434_);
lean_dec_ref(v_arg_1431_);
lean_dec_ref(v___x_1426_);
lean_dec_ref(v_arg_1425_);
lean_dec_ref(v_arg_1422_);
lean_dec_ref(v_arg_1419_);
v___y_1339_ = v_a_1314_;
v___y_1340_ = v_a_1315_;
v___y_1341_ = v_a_1316_;
v___y_1342_ = v_a_1317_;
v___y_1343_ = v_a_1318_;
v___y_1344_ = v_a_1319_;
v___y_1345_ = v_a_1320_;
v___y_1346_ = v_a_1321_;
v___y_1347_ = v___x_1418_;
v___y_1348_ = v_a_1323_;
goto v___jp_1338_;
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v___x_1440_ = lean_st_ref_get(v_a_1314_);
v___x_1441_ = lean_st_ref_get(v_a_1314_);
v___x_1442_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1440_, v_arg_1422_, v_arg_1431_);
lean_dec(v___x_1440_);
if (v___x_1442_ == 0)
{
lean_dec(v___x_1441_);
v___y_1352_ = v___x_1426_;
v___y_1353_ = v_arg_1425_;
v___y_1354_ = v_arg_1434_;
v___y_1355_ = v_arg_1437_;
v___y_1356_ = v_arg_1419_;
v___y_1357_ = v_arg_1431_;
v___y_1358_ = v___x_1418_;
v___y_1359_ = v___x_1439_;
v___y_1360_ = v_arg_1422_;
v___y_1361_ = v___x_1442_;
goto v___jp_1351_;
}
else
{
uint8_t v___x_1443_; 
v___x_1443_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1441_, v_arg_1419_, v_arg_1434_);
lean_dec(v___x_1441_);
v___y_1352_ = v___x_1426_;
v___y_1353_ = v_arg_1425_;
v___y_1354_ = v_arg_1434_;
v___y_1355_ = v_arg_1437_;
v___y_1356_ = v_arg_1419_;
v___y_1357_ = v_arg_1431_;
v___y_1358_ = v___x_1418_;
v___y_1359_ = v___x_1439_;
v___y_1360_ = v_arg_1422_;
v___y_1361_ = v___x_1443_;
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
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1452_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1453_ = lean_unsigned_to_nat(38u);
v___x_1454_ = lean_unsigned_to_nat(250u);
v___x_1455_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2));
v___x_1456_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1457_ = l_mkPanicMessageWithDecl(v___x_1456_, v___x_1455_, v___x_1454_, v___x_1453_, v___x_1452_);
return v___x_1457_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1459_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4));
v___x_1460_ = lean_unsigned_to_nat(6u);
v___x_1461_ = lean_unsigned_to_nat(260u);
v___x_1462_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2));
v___x_1463_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1464_ = l_mkPanicMessageWithDecl(v___x_1463_, v___x_1462_, v___x_1461_, v___x_1460_, v___x_1459_);
return v___x_1464_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1467_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__1));
v___x_1468_ = lean_unsigned_to_nat(4u);
v___x_1469_ = lean_unsigned_to_nat(219u);
v___x_1470_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__0));
v___x_1471_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1472_ = l_mkPanicMessageWithDecl(v___x_1471_, v___x_1470_, v___x_1469_, v___x_1468_, v___x_1467_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(lean_object* v_lhs_1473_, lean_object* v_rhs_1474_, uint8_t v_heq_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_numArgs_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
v_numArgs_1487_ = l_Lean_Expr_getAppNumArgs(v_lhs_1473_);
v___x_1488_ = l_Lean_Expr_getAppNumArgs(v_rhs_1474_);
v___x_1489_ = lean_nat_dec_eq(v___x_1488_, v_numArgs_1487_);
lean_dec(v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
lean_dec(v_numArgs_1487_);
lean_dec_ref(v_rhs_1474_);
lean_dec_ref(v_lhs_1473_);
v___x_1490_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2);
v___x_1491_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1490_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
return v___x_1491_;
}
else
{
lean_object* v_f_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v_f_1492_ = l_Lean_Expr_getAppFn(v_lhs_1473_);
v___x_1493_ = lean_box(0);
lean_inc_ref(v_f_1492_);
v___x_1494_ = l_Lean_Meta_getFunInfo(v_f_1492_, v___x_1493_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
lean_dec_ref_known(v___x_1494_, 1);
v___x_1496_ = l_Lean_Meta_FunInfo_getArity(v_a_1495_);
lean_dec(v_a_1495_);
v___x_1497_ = lean_nat_dec_lt(v___x_1496_, v_numArgs_1487_);
lean_dec(v___x_1496_);
if (v___x_1497_ == 0)
{
lean_object* v_g_1498_; lean_object* v___x_1499_; 
v_g_1498_ = l_Lean_Expr_getAppFn(v_rhs_1474_);
v___x_1499_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_1492_, v_g_1498_, v_numArgs_1487_, v_lhs_1473_, v_rhs_1474_, v_heq_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
return v___x_1499_;
}
else
{
lean_object* v___x_1500_; 
lean_dec_ref(v_f_1492_);
lean_dec(v_numArgs_1487_);
lean_inc_ref(v_lhs_1473_);
v___x_1500_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(v_lhs_1473_, v_rhs_1474_);
if (lean_obj_tag(v___x_1500_) == 1)
{
lean_object* v_val_1501_; lean_object* v_fst_1502_; lean_object* v_snd_1503_; lean_object* v___y_1505_; lean_object* v___x_1518_; 
v_val_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_val_1501_);
lean_dec_ref_known(v___x_1500_, 1);
v_fst_1502_ = lean_ctor_get(v_val_1501_, 0);
lean_inc(v_fst_1502_);
v_snd_1503_ = lean_ctor_get(v_val_1501_, 1);
lean_inc_n(v_snd_1503_, 2);
lean_dec(v_val_1501_);
v___x_1518_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(v_fst_1502_, v_snd_1503_, v_a_1479_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
if (lean_obj_tag(v___x_1518_) == 0)
{
v___y_1505_ = v___x_1518_;
goto v___jp_1504_;
}
else
{
lean_object* v_a_1519_; uint8_t v___y_1521_; uint8_t v___x_1523_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
v___x_1523_ = l_Lean_Exception_isInterrupt(v_a_1519_);
if (v___x_1523_ == 0)
{
uint8_t v___x_1524_; 
v___x_1524_ = l_Lean_Exception_isRuntime(v_a_1519_);
v___y_1521_ = v___x_1524_;
goto v___jp_1520_;
}
else
{
lean_dec(v_a_1519_);
v___y_1521_ = v___x_1523_;
goto v___jp_1520_;
}
v___jp_1520_:
{
if (v___y_1521_ == 0)
{
lean_object* v___x_1522_; 
lean_dec_ref_known(v___x_1518_, 1);
lean_inc_ref(v_rhs_1474_);
lean_inc_ref(v_lhs_1473_);
v___x_1522_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1473_, v_rhs_1474_, lean_box(0), v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
v___y_1505_ = v___x_1522_;
goto v___jp_1504_;
}
else
{
v___y_1505_ = v___x_1518_;
goto v___jp_1504_;
}
}
}
v___jp_1504_:
{
if (lean_obj_tag(v___y_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1507_; 
v_a_1506_ = lean_ctor_get(v___y_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref_known(v___y_1505_, 1);
v___x_1507_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_1506_, v_lhs_1473_, v_rhs_1474_, v_snd_1503_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
lean_dec(v_snd_1503_);
lean_dec_ref(v_rhs_1474_);
lean_dec_ref(v_lhs_1473_);
lean_dec(v_a_1506_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1509_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1508_);
lean_dec_ref_known(v___x_1507_, 1);
v___x_1509_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_1508_, v_heq_1475_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
return v___x_1509_;
}
else
{
return v___x_1507_;
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec(v_snd_1503_);
lean_dec_ref(v_rhs_1474_);
lean_dec_ref(v_lhs_1473_);
v_a_1510_ = lean_ctor_get(v___y_1505_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___y_1505_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___y_1505_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___y_1505_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
else
{
lean_object* v___x_1525_; 
lean_dec(v___x_1500_);
v___x_1525_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1473_, v_rhs_1474_, lean_box(0), v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
return v___x_1525_;
}
}
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
lean_dec_ref(v_f_1492_);
lean_dec(v_numArgs_1487_);
lean_dec_ref(v_rhs_1474_);
lean_dec_ref(v_lhs_1473_);
v_a_1526_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1494_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1494_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(lean_object* v_lhs_1534_, lean_object* v_rhs_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
uint8_t v___x_1547_; 
v___x_1547_ = l_Lean_Expr_isApp(v_lhs_1534_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_box(0);
v___x_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
return v___x_1549_;
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1550_ = l_Lean_Expr_appFn_x21(v_lhs_1534_);
v___x_1551_ = l_Lean_Expr_appFn_x21(v_rhs_1535_);
v___x_1552_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v___x_1550_, v___x_1551_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
lean_dec_ref(v___x_1551_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1652_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1652_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1652_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v_a_u2081_1557_; lean_object* v_a_u2082_1558_; 
v_a_u2081_1557_ = l_Lean_Expr_appArg_x21(v_lhs_1534_);
v_a_u2082_1558_ = l_Lean_Expr_appArg_x21(v_rhs_1535_);
if (lean_obj_tag(v_a_1553_) == 1)
{
lean_object* v_val_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1616_; 
lean_del_object(v___x_1555_);
lean_dec_ref(v___x_1550_);
v_val_1559_ = lean_ctor_get(v_a_1553_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_a_1553_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1561_ = v_a_1553_;
v_isShared_1562_ = v_isSharedCheck_1616_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_val_1559_);
lean_dec(v_a_1553_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1616_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
size_t v___x_1563_; size_t v___x_1564_; uint8_t v___x_1565_; 
v___x_1563_ = lean_ptr_addr(v_a_u2081_1557_);
v___x_1564_ = lean_ptr_addr(v_a_u2082_1558_);
v___x_1565_ = lean_usize_dec_eq(v___x_1563_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; 
v___x_1566_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_1557_, v_a_u2082_1558_, v___x_1565_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1568_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v___x_1566_, 1);
v___x_1568_ = l_Lean_Meta_mkCongr(v_val_1559_, v_a_1567_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1579_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1571_ = v___x_1568_;
v_isShared_1572_ = v_isSharedCheck_1579_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1579_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v_a_1569_);
v___x_1574_ = v___x_1561_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1576_; 
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 0, v___x_1574_);
v___x_1576_ = v___x_1571_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
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
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_del_object(v___x_1561_);
v_a_1580_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1568_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1568_);
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
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_del_object(v___x_1561_);
lean_dec(v_val_1559_);
v_a_1588_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1566_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1566_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
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
lean_object* v___x_1596_; 
lean_dec_ref(v_a_u2082_1558_);
v___x_1596_ = l_Lean_Meta_mkCongrFun(v_val_1559_, v_a_u2081_1557_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1607_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1599_ = v___x_1596_;
v_isShared_1600_ = v_isSharedCheck_1607_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1596_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1607_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v_a_1597_);
v___x_1602_ = v___x_1561_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1604_; 
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v___x_1602_);
v___x_1604_ = v___x_1599_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1602_);
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
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_del_object(v___x_1561_);
v_a_1608_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1596_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1596_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
}
else
{
size_t v___x_1617_; size_t v___x_1618_; uint8_t v___x_1619_; 
lean_dec(v_a_1553_);
v___x_1617_ = lean_ptr_addr(v_a_u2081_1557_);
v___x_1618_ = lean_ptr_addr(v_a_u2082_1558_);
v___x_1619_ = lean_usize_dec_eq(v___x_1617_, v___x_1618_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; 
lean_del_object(v___x_1555_);
v___x_1620_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_1557_, v_a_u2082_1558_, v___x_1619_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1622_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
v___x_1622_ = l_Lean_Meta_mkCongrArg(v___x_1550_, v_a_1621_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1631_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1631_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1631_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1627_, 0, v_a_1623_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1627_);
v___x_1629_ = v___x_1625_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
v_a_1632_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1622_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1622_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec_ref(v___x_1550_);
v_a_1640_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1620_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1620_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1650_; 
lean_dec_ref(v_a_u2082_1558_);
lean_dec_ref(v_a_u2081_1557_);
lean_dec_ref(v___x_1550_);
v___x_1648_ = lean_box(0);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1648_);
v___x_1650_ = v___x_1555_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
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
}
else
{
lean_dec_ref(v___x_1550_);
return v___x_1552_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3(void){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1656_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__2));
v___x_1657_ = lean_unsigned_to_nat(14u);
v___x_1658_ = lean_unsigned_to_nat(22u);
v___x_1659_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__1));
v___x_1660_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__0));
v___x_1661_ = l_mkPanicMessageWithDecl(v___x_1660_, v___x_1659_, v___x_1658_, v___x_1657_, v___x_1656_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(lean_object* v_lhs_1662_, lean_object* v_rhs_1663_, uint8_t v_heq_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_1662_, v_rhs_1663_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1690_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1679_ = v___x_1676_;
v_isShared_1680_ = v_isSharedCheck_1690_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1676_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1690_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___y_1682_; 
if (lean_obj_tag(v_a_1677_) == 0)
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3);
v___x_1688_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_spec__13(v___x_1687_);
v___y_1682_ = v___x_1688_;
goto v___jp_1681_;
}
else
{
lean_object* v_val_1689_; 
v_val_1689_ = lean_ctor_get(v_a_1677_, 0);
lean_inc(v_val_1689_);
lean_dec_ref_known(v_a_1677_, 1);
v___y_1682_ = v_val_1689_;
goto v___jp_1681_;
}
v___jp_1681_:
{
if (v_heq_1664_ == 0)
{
lean_object* v___x_1684_; 
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 0, v___y_1682_);
v___x_1684_ = v___x_1679_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___y_1682_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
else
{
lean_object* v___x_1686_; 
lean_del_object(v___x_1679_);
v___x_1686_ = l_Lean_Meta_mkHEqOfEq(v___y_1682_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
return v___x_1686_;
}
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
v_a_1691_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1676_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1676_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__1(void){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1700_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1701_ = lean_unsigned_to_nat(36u);
v___x_1702_ = lean_unsigned_to_nat(143u);
v___x_1703_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1704_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1705_ = l_mkPanicMessageWithDecl(v___x_1704_, v___x_1703_, v___x_1702_, v___x_1701_, v___x_1700_);
return v___x_1705_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__2(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1706_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1707_ = lean_unsigned_to_nat(34u);
v___x_1708_ = lean_unsigned_to_nat(144u);
v___x_1709_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1710_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1711_ = l_mkPanicMessageWithDecl(v___x_1710_, v___x_1709_, v___x_1708_, v___x_1707_, v___x_1706_);
return v___x_1711_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__4(void){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1713_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__3));
v___x_1714_ = lean_unsigned_to_nat(4u);
v___x_1715_ = lean_unsigned_to_nat(145u);
v___x_1716_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1717_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1718_ = l_mkPanicMessageWithDecl(v___x_1717_, v___x_1716_, v___x_1715_, v___x_1714_, v___x_1713_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrProof(lean_object* v_lhs_1729_, lean_object* v_rhs_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; uint8_t v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; uint8_t v___y_1778_; lean_object* v_fileName_1814_; lean_object* v_fileMap_1815_; lean_object* v_options_1816_; lean_object* v_currRecDepth_1817_; lean_object* v_maxRecDepth_1818_; lean_object* v_ref_1819_; lean_object* v_currNamespace_1820_; lean_object* v_openDecls_1821_; lean_object* v_initHeartbeats_1822_; lean_object* v_maxHeartbeats_1823_; lean_object* v_quotContext_1824_; lean_object* v_currMacroScope_1825_; uint8_t v_diag_1826_; lean_object* v_cancelTk_x3f_1827_; uint8_t v_suppressElabErrors_1828_; lean_object* v_inheritedTraceOptions_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
v_fileName_1814_ = lean_ctor_get(v_a_1739_, 0);
v_fileMap_1815_ = lean_ctor_get(v_a_1739_, 1);
v_options_1816_ = lean_ctor_get(v_a_1739_, 2);
v_currRecDepth_1817_ = lean_ctor_get(v_a_1739_, 3);
v_maxRecDepth_1818_ = lean_ctor_get(v_a_1739_, 4);
v_ref_1819_ = lean_ctor_get(v_a_1739_, 5);
v_currNamespace_1820_ = lean_ctor_get(v_a_1739_, 6);
v_openDecls_1821_ = lean_ctor_get(v_a_1739_, 7);
v_initHeartbeats_1822_ = lean_ctor_get(v_a_1739_, 8);
v_maxHeartbeats_1823_ = lean_ctor_get(v_a_1739_, 9);
v_quotContext_1824_ = lean_ctor_get(v_a_1739_, 10);
v_currMacroScope_1825_ = lean_ctor_get(v_a_1739_, 11);
v_diag_1826_ = lean_ctor_get_uint8(v_a_1739_, sizeof(void*)*14);
v_cancelTk_x3f_1827_ = lean_ctor_get(v_a_1739_, 12);
v_suppressElabErrors_1828_ = lean_ctor_get_uint8(v_a_1739_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1829_ = lean_ctor_get(v_a_1739_, 13);
v___x_1830_ = l_Lean_Expr_cleanupAnnotations(v_lhs_1729_);
v___x_1831_ = l_Lean_Expr_isApp(v___x_1830_);
v___x_1861_ = lean_unsigned_to_nat(0u);
v___x_1862_ = lean_nat_dec_eq(v_maxRecDepth_1818_, v___x_1861_);
if (v___x_1862_ == 0)
{
uint8_t v___x_1863_; 
v___x_1863_ = lean_nat_dec_eq(v_currRecDepth_1817_, v_maxRecDepth_1818_);
if (v___x_1863_ == 0)
{
goto v___jp_1832_;
}
else
{
lean_object* v___x_1864_; 
lean_dec_ref(v___x_1830_);
lean_dec_ref(v_rhs_1730_);
lean_inc(v_ref_1819_);
v___x_1864_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1819_);
return v___x_1864_;
}
}
else
{
goto v___jp_1832_;
}
v___jp_1742_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__1, &l_Lean_Meta_Grind_mkEqCongrProof___closed__1_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__1);
v___x_1754_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1753_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
lean_dec_ref(v___y_1751_);
return v___x_1754_;
}
v___jp_1755_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__2, &l_Lean_Meta_Grind_mkEqCongrProof___closed__2_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__2);
v___x_1767_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1766_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec_ref(v___y_1764_);
return v___x_1767_;
}
v___jp_1768_:
{
if (v___y_1778_ == 0)
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_dec_ref(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec_ref(v___y_1769_);
v___x_1779_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__4, &l_Lean_Meta_Grind_mkEqCongrProof___closed__4_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__4);
v___x_1780_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1779_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v___y_1777_, v_a_1740_);
lean_dec_ref(v___y_1777_);
return v___x_1780_;
}
else
{
lean_object* v___x_1781_; size_t v___x_1782_; size_t v___x_1783_; uint8_t v___x_1784_; 
v___x_1781_ = l_Lean_Expr_constLevels_x21(v___y_1770_);
lean_dec_ref(v___y_1770_);
v___x_1782_ = lean_ptr_addr(v___y_1776_);
v___x_1783_ = lean_ptr_addr(v___y_1771_);
v___x_1784_ = lean_usize_dec_eq(v___x_1782_, v___x_1783_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; 
lean_inc_ref(v___y_1775_);
lean_inc_ref(v___y_1774_);
v___x_1785_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1774_, v___y_1775_, v___y_1773_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v___y_1777_, v_a_1740_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1787_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
lean_dec_ref_known(v___x_1785_, 1);
lean_inc_ref(v___y_1772_);
lean_inc_ref(v___y_1769_);
v___x_1787_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1769_, v___y_1772_, v___y_1773_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v___y_1777_, v_a_1740_);
lean_dec_ref(v___y_1777_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1798_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1790_ = v___x_1787_;
v_isShared_1791_ = v_isSharedCheck_1798_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1798_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1796_; 
v___x_1792_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__6));
v___x_1793_ = l_Lean_mkConst(v___x_1792_, v___x_1781_);
v___x_1794_ = l_Lean_mkApp8(v___x_1793_, v___y_1776_, v___y_1771_, v___y_1774_, v___y_1769_, v___y_1775_, v___y_1772_, v_a_1786_, v_a_1788_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1794_);
v___x_1796_ = v___x_1790_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1794_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
else
{
lean_dec(v_a_1786_);
lean_dec(v___x_1781_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1769_);
return v___x_1787_;
}
}
else
{
lean_dec(v___x_1781_);
lean_dec_ref(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1769_);
return v___x_1785_;
}
}
else
{
uint8_t v___x_1799_; lean_object* v___x_1800_; 
lean_dec_ref(v___y_1771_);
v___x_1799_ = 0;
lean_inc_ref(v___y_1775_);
lean_inc_ref(v___y_1774_);
v___x_1800_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1774_, v___y_1775_, v___x_1799_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v___y_1777_, v_a_1740_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1802_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1801_);
lean_dec_ref_known(v___x_1800_, 1);
lean_inc_ref(v___y_1772_);
lean_inc_ref(v___y_1769_);
v___x_1802_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1769_, v___y_1772_, v___x_1799_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v___y_1777_, v_a_1740_);
lean_dec_ref(v___y_1777_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1813_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1813_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1813_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1807_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__8));
v___x_1808_ = l_Lean_mkConst(v___x_1807_, v___x_1781_);
v___x_1809_ = l_Lean_mkApp7(v___x_1808_, v___y_1776_, v___y_1774_, v___y_1769_, v___y_1775_, v___y_1772_, v_a_1801_, v_a_1803_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1809_);
v___x_1811_ = v___x_1805_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
else
{
lean_dec(v_a_1801_);
lean_dec(v___x_1781_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1769_);
return v___x_1802_;
}
}
else
{
lean_dec(v___x_1781_);
lean_dec_ref(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1769_);
return v___x_1800_;
}
}
}
}
v___jp_1832_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1833_ = lean_unsigned_to_nat(1u);
v___x_1834_ = lean_nat_add(v_currRecDepth_1817_, v___x_1833_);
lean_inc_ref(v_inheritedTraceOptions_1829_);
lean_inc(v_cancelTk_x3f_1827_);
lean_inc(v_currMacroScope_1825_);
lean_inc(v_quotContext_1824_);
lean_inc(v_maxHeartbeats_1823_);
lean_inc(v_initHeartbeats_1822_);
lean_inc(v_openDecls_1821_);
lean_inc(v_currNamespace_1820_);
lean_inc(v_ref_1819_);
lean_inc(v_maxRecDepth_1818_);
lean_inc_ref(v_options_1816_);
lean_inc_ref(v_fileMap_1815_);
lean_inc_ref(v_fileName_1814_);
v___x_1835_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1835_, 0, v_fileName_1814_);
lean_ctor_set(v___x_1835_, 1, v_fileMap_1815_);
lean_ctor_set(v___x_1835_, 2, v_options_1816_);
lean_ctor_set(v___x_1835_, 3, v___x_1834_);
lean_ctor_set(v___x_1835_, 4, v_maxRecDepth_1818_);
lean_ctor_set(v___x_1835_, 5, v_ref_1819_);
lean_ctor_set(v___x_1835_, 6, v_currNamespace_1820_);
lean_ctor_set(v___x_1835_, 7, v_openDecls_1821_);
lean_ctor_set(v___x_1835_, 8, v_initHeartbeats_1822_);
lean_ctor_set(v___x_1835_, 9, v_maxHeartbeats_1823_);
lean_ctor_set(v___x_1835_, 10, v_quotContext_1824_);
lean_ctor_set(v___x_1835_, 11, v_currMacroScope_1825_);
lean_ctor_set(v___x_1835_, 12, v_cancelTk_x3f_1827_);
lean_ctor_set(v___x_1835_, 13, v_inheritedTraceOptions_1829_);
lean_ctor_set_uint8(v___x_1835_, sizeof(void*)*14, v_diag_1826_);
lean_ctor_set_uint8(v___x_1835_, sizeof(void*)*14 + 1, v_suppressElabErrors_1828_);
if (v___x_1831_ == 0)
{
lean_dec_ref(v___x_1830_);
lean_dec_ref(v_rhs_1730_);
v___y_1743_ = v_a_1731_;
v___y_1744_ = v_a_1732_;
v___y_1745_ = v_a_1733_;
v___y_1746_ = v_a_1734_;
v___y_1747_ = v_a_1735_;
v___y_1748_ = v_a_1736_;
v___y_1749_ = v_a_1737_;
v___y_1750_ = v_a_1738_;
v___y_1751_ = v___x_1835_;
v___y_1752_ = v_a_1740_;
goto v___jp_1742_;
}
else
{
lean_object* v_arg_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; 
v_arg_1836_ = lean_ctor_get(v___x_1830_, 1);
lean_inc_ref(v_arg_1836_);
v___x_1837_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1830_);
v___x_1838_ = l_Lean_Expr_isApp(v___x_1837_);
if (v___x_1838_ == 0)
{
lean_dec_ref(v___x_1837_);
lean_dec_ref(v_arg_1836_);
lean_dec_ref(v_rhs_1730_);
v___y_1743_ = v_a_1731_;
v___y_1744_ = v_a_1732_;
v___y_1745_ = v_a_1733_;
v___y_1746_ = v_a_1734_;
v___y_1747_ = v_a_1735_;
v___y_1748_ = v_a_1736_;
v___y_1749_ = v_a_1737_;
v___y_1750_ = v_a_1738_;
v___y_1751_ = v___x_1835_;
v___y_1752_ = v_a_1740_;
goto v___jp_1742_;
}
else
{
lean_object* v_arg_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
v_arg_1839_ = lean_ctor_get(v___x_1837_, 1);
lean_inc_ref(v_arg_1839_);
v___x_1840_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1837_);
v___x_1841_ = l_Lean_Expr_isApp(v___x_1840_);
if (v___x_1841_ == 0)
{
lean_dec_ref(v___x_1840_);
lean_dec_ref(v_arg_1839_);
lean_dec_ref(v_arg_1836_);
lean_dec_ref(v_rhs_1730_);
v___y_1743_ = v_a_1731_;
v___y_1744_ = v_a_1732_;
v___y_1745_ = v_a_1733_;
v___y_1746_ = v_a_1734_;
v___y_1747_ = v_a_1735_;
v___y_1748_ = v_a_1736_;
v___y_1749_ = v_a_1737_;
v___y_1750_ = v_a_1738_;
v___y_1751_ = v___x_1835_;
v___y_1752_ = v_a_1740_;
goto v___jp_1742_;
}
else
{
lean_object* v_arg_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; 
v_arg_1842_ = lean_ctor_get(v___x_1840_, 1);
lean_inc_ref(v_arg_1842_);
v___x_1843_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1840_);
v___x_1844_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_1845_ = l_Lean_Expr_isConstOf(v___x_1843_, v___x_1844_);
if (v___x_1845_ == 0)
{
lean_dec_ref(v___x_1843_);
lean_dec_ref(v_arg_1842_);
lean_dec_ref(v_arg_1839_);
lean_dec_ref(v_arg_1836_);
lean_dec_ref(v_rhs_1730_);
v___y_1743_ = v_a_1731_;
v___y_1744_ = v_a_1732_;
v___y_1745_ = v_a_1733_;
v___y_1746_ = v_a_1734_;
v___y_1747_ = v_a_1735_;
v___y_1748_ = v_a_1736_;
v___y_1749_ = v_a_1737_;
v___y_1750_ = v_a_1738_;
v___y_1751_ = v___x_1835_;
v___y_1752_ = v_a_1740_;
goto v___jp_1742_;
}
else
{
lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1846_ = l_Lean_Expr_cleanupAnnotations(v_rhs_1730_);
v___x_1847_ = l_Lean_Expr_isApp(v___x_1846_);
if (v___x_1847_ == 0)
{
lean_dec_ref(v___x_1846_);
lean_dec_ref(v___x_1843_);
lean_dec_ref(v_arg_1842_);
lean_dec_ref(v_arg_1839_);
lean_dec_ref(v_arg_1836_);
v___y_1756_ = v_a_1731_;
v___y_1757_ = v_a_1732_;
v___y_1758_ = v_a_1733_;
v___y_1759_ = v_a_1734_;
v___y_1760_ = v_a_1735_;
v___y_1761_ = v_a_1736_;
v___y_1762_ = v_a_1737_;
v___y_1763_ = v_a_1738_;
v___y_1764_ = v___x_1835_;
v___y_1765_ = v_a_1740_;
goto v___jp_1755_;
}
else
{
lean_object* v_arg_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; 
v_arg_1848_ = lean_ctor_get(v___x_1846_, 1);
lean_inc_ref(v_arg_1848_);
v___x_1849_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1846_);
v___x_1850_ = l_Lean_Expr_isApp(v___x_1849_);
if (v___x_1850_ == 0)
{
lean_dec_ref(v___x_1849_);
lean_dec_ref(v_arg_1848_);
lean_dec_ref(v___x_1843_);
lean_dec_ref(v_arg_1842_);
lean_dec_ref(v_arg_1839_);
lean_dec_ref(v_arg_1836_);
v___y_1756_ = v_a_1731_;
v___y_1757_ = v_a_1732_;
v___y_1758_ = v_a_1733_;
v___y_1759_ = v_a_1734_;
v___y_1760_ = v_a_1735_;
v___y_1761_ = v_a_1736_;
v___y_1762_ = v_a_1737_;
v___y_1763_ = v_a_1738_;
v___y_1764_ = v___x_1835_;
v___y_1765_ = v_a_1740_;
goto v___jp_1755_;
}
else
{
lean_object* v_arg_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; 
v_arg_1851_ = lean_ctor_get(v___x_1849_, 1);
lean_inc_ref(v_arg_1851_);
v___x_1852_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1849_);
v___x_1853_ = l_Lean_Expr_isApp(v___x_1852_);
if (v___x_1853_ == 0)
{
lean_dec_ref(v___x_1852_);
lean_dec_ref(v_arg_1851_);
lean_dec_ref(v_arg_1848_);
lean_dec_ref(v___x_1843_);
lean_dec_ref(v_arg_1842_);
lean_dec_ref(v_arg_1839_);
lean_dec_ref(v_arg_1836_);
v___y_1756_ = v_a_1731_;
v___y_1757_ = v_a_1732_;
v___y_1758_ = v_a_1733_;
v___y_1759_ = v_a_1734_;
v___y_1760_ = v_a_1735_;
v___y_1761_ = v_a_1736_;
v___y_1762_ = v_a_1737_;
v___y_1763_ = v_a_1738_;
v___y_1764_ = v___x_1835_;
v___y_1765_ = v_a_1740_;
goto v___jp_1755_;
}
else
{
lean_object* v_arg_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v_arg_1854_ = lean_ctor_get(v___x_1852_, 1);
lean_inc_ref(v_arg_1854_);
v___x_1855_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1852_);
v___x_1856_ = l_Lean_Expr_isConstOf(v___x_1855_, v___x_1844_);
lean_dec_ref(v___x_1855_);
if (v___x_1856_ == 0)
{
lean_dec_ref(v_arg_1854_);
lean_dec_ref(v_arg_1851_);
lean_dec_ref(v_arg_1848_);
lean_dec_ref(v___x_1843_);
lean_dec_ref(v_arg_1842_);
lean_dec_ref(v_arg_1839_);
lean_dec_ref(v_arg_1836_);
v___y_1756_ = v_a_1731_;
v___y_1757_ = v_a_1732_;
v___y_1758_ = v_a_1733_;
v___y_1759_ = v_a_1734_;
v___y_1760_ = v_a_1735_;
v___y_1761_ = v_a_1736_;
v___y_1762_ = v_a_1737_;
v___y_1763_ = v_a_1738_;
v___y_1764_ = v___x_1835_;
v___y_1765_ = v_a_1740_;
goto v___jp_1755_;
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1857_ = lean_st_ref_get(v_a_1731_);
v___x_1858_ = lean_st_ref_get(v_a_1731_);
v___x_1859_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1857_, v_arg_1839_, v_arg_1851_);
lean_dec(v___x_1857_);
if (v___x_1859_ == 0)
{
lean_dec(v___x_1858_);
v___y_1769_ = v_arg_1836_;
v___y_1770_ = v___x_1843_;
v___y_1771_ = v_arg_1854_;
v___y_1772_ = v_arg_1848_;
v___y_1773_ = v___x_1856_;
v___y_1774_ = v_arg_1839_;
v___y_1775_ = v_arg_1851_;
v___y_1776_ = v_arg_1842_;
v___y_1777_ = v___x_1835_;
v___y_1778_ = v___x_1859_;
goto v___jp_1768_;
}
else
{
uint8_t v___x_1860_; 
v___x_1860_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1858_, v_arg_1836_, v_arg_1848_);
lean_dec(v___x_1858_);
v___y_1769_ = v_arg_1836_;
v___y_1770_ = v___x_1843_;
v___y_1771_ = v_arg_1854_;
v___y_1772_ = v_arg_1848_;
v___y_1773_ = v___x_1856_;
v___y_1774_ = v_arg_1839_;
v___y_1775_ = v_arg_1851_;
v___y_1776_ = v_arg_1842_;
v___y_1777_ = v___x_1835_;
v___y_1778_ = v___x_1860_;
goto v___jp_1768_;
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
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1875_ = lean_box(0);
v___x_1876_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3));
v___x_1877_ = l_Lean_mkConst(v___x_1876_, v___x_1875_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(lean_object* v_lhs_1878_, lean_object* v_rhs_1879_, uint8_t v_heq_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v___x_1892_; lean_object* v_p_1893_; lean_object* v___x_1894_; lean_object* v_q_1895_; uint8_t v___x_1896_; lean_object* v___x_1897_; 
v___x_1892_ = l_Lean_Expr_appFn_x21(v_lhs_1878_);
v_p_1893_ = l_Lean_Expr_appArg_x21(v___x_1892_);
lean_dec_ref(v___x_1892_);
v___x_1894_ = l_Lean_Expr_appFn_x21(v_rhs_1879_);
v_q_1895_ = l_Lean_Expr_appArg_x21(v___x_1894_);
lean_dec_ref(v___x_1894_);
v___x_1896_ = 0;
lean_inc_ref(v_q_1895_);
lean_inc_ref(v_p_1893_);
v___x_1897_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_p_1893_, v_q_1895_, v___x_1896_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v_hp_1899_; lean_object* v_hq_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v___x_1897_, 1);
v_hp_1899_ = l_Lean_Expr_appArg_x21(v_lhs_1878_);
v_hq_1900_ = l_Lean_Expr_appArg_x21(v_rhs_1879_);
v___x_1901_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4);
v___x_1902_ = l_Lean_mkApp5(v___x_1901_, v_p_1893_, v_q_1895_, v_a_1898_, v_hp_1899_, v_hq_1900_);
v___x_1903_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v___x_1902_, v_heq_1880_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
return v___x_1903_;
}
else
{
lean_dec_ref(v_q_1895_);
lean_dec_ref(v_p_1893_);
return v___x_1897_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = lean_box(0);
v___x_1915_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1));
v___x_1916_ = l_Lean_mkConst(v___x_1915_, v___x_1914_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(lean_object* v_lhs_1917_, lean_object* v_rhs_1918_, uint8_t v_heq_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_){
_start:
{
lean_object* v___x_1931_; lean_object* v_p_1932_; lean_object* v___x_1933_; lean_object* v_q_1934_; uint8_t v___x_1935_; lean_object* v___x_1936_; 
v___x_1931_ = l_Lean_Expr_appFn_x21(v_lhs_1917_);
v_p_1932_ = l_Lean_Expr_appArg_x21(v___x_1931_);
lean_dec_ref(v___x_1931_);
v___x_1933_ = l_Lean_Expr_appFn_x21(v_rhs_1918_);
v_q_1934_ = l_Lean_Expr_appArg_x21(v___x_1933_);
lean_dec_ref(v___x_1933_);
v___x_1935_ = 0;
lean_inc_ref(v_q_1934_);
lean_inc_ref(v_p_1932_);
v___x_1936_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_p_1932_, v_q_1934_, v___x_1935_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v_hp_1938_; lean_object* v_hq_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref_known(v___x_1936_, 1);
v_hp_1938_ = l_Lean_Expr_appArg_x21(v_lhs_1917_);
v_hq_1939_ = l_Lean_Expr_appArg_x21(v_rhs_1918_);
v___x_1940_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2);
v___x_1941_ = l_Lean_mkApp5(v___x_1940_, v_p_1932_, v_q_1934_, v_a_1937_, v_hp_1938_, v_hq_1939_);
v___x_1942_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v___x_1941_, v_heq_1919_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
return v___x_1942_;
}
else
{
lean_dec_ref(v_q_1934_);
lean_dec_ref(v_p_1932_);
return v___x_1936_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(lean_object* v_lhs_1943_, lean_object* v_rhs_1944_, uint8_t v_heq_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
if (lean_obj_tag(v_lhs_1943_) == 7)
{
if (lean_obj_tag(v_rhs_1944_) == 7)
{
lean_object* v_binderType_1957_; lean_object* v_body_1958_; lean_object* v_binderType_1959_; lean_object* v_body_1960_; lean_object* v___y_1962_; lean_object* v_a_1963_; lean_object* v_keyedConfig_1982_; uint8_t v_trackZetaDelta_1983_; lean_object* v_zetaDeltaSet_1984_; lean_object* v_lctx_1985_; lean_object* v_localInstances_1986_; lean_object* v_defEqCtx_x3f_1987_; lean_object* v_synthPendingDepth_1988_; lean_object* v_customCanUnfoldPredicate_x3f_1989_; uint8_t v_univApprox_1990_; uint8_t v_inTypeClassResolution_1991_; uint8_t v_cacheInferType_1992_; lean_object* v_a_1994_; uint8_t v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_binderType_1957_ = lean_ctor_get(v_lhs_1943_, 1);
lean_inc_ref_n(v_binderType_1957_, 2);
v_body_1958_ = lean_ctor_get(v_lhs_1943_, 2);
lean_inc_ref(v_body_1958_);
lean_dec_ref_known(v_lhs_1943_, 3);
v_binderType_1959_ = lean_ctor_get(v_rhs_1944_, 1);
lean_inc_ref(v_binderType_1959_);
v_body_1960_ = lean_ctor_get(v_rhs_1944_, 2);
lean_inc_ref(v_body_1960_);
lean_dec_ref_known(v_rhs_1944_, 3);
v_keyedConfig_1982_ = lean_ctor_get(v_a_1952_, 0);
v_trackZetaDelta_1983_ = lean_ctor_get_uint8(v_a_1952_, sizeof(void*)*7);
v_zetaDeltaSet_1984_ = lean_ctor_get(v_a_1952_, 1);
v_lctx_1985_ = lean_ctor_get(v_a_1952_, 2);
v_localInstances_1986_ = lean_ctor_get(v_a_1952_, 3);
v_defEqCtx_x3f_1987_ = lean_ctor_get(v_a_1952_, 4);
v_synthPendingDepth_1988_ = lean_ctor_get(v_a_1952_, 5);
v_customCanUnfoldPredicate_x3f_1989_ = lean_ctor_get(v_a_1952_, 6);
v_univApprox_1990_ = lean_ctor_get_uint8(v_a_1952_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1991_ = lean_ctor_get_uint8(v_a_1952_, sizeof(void*)*7 + 2);
v_cacheInferType_1992_ = lean_ctor_get_uint8(v_a_1952_, sizeof(void*)*7 + 3);
v___x_2009_ = 1;
lean_inc_ref(v_keyedConfig_1982_);
v___x_2010_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2009_, v_keyedConfig_1982_);
lean_inc(v_customCanUnfoldPredicate_x3f_1989_);
lean_inc(v_synthPendingDepth_1988_);
lean_inc(v_defEqCtx_x3f_1987_);
lean_inc_ref(v_localInstances_1986_);
lean_inc_ref(v_lctx_1985_);
lean_inc(v_zetaDeltaSet_1984_);
v___x_2011_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
lean_ctor_set(v___x_2011_, 1, v_zetaDeltaSet_1984_);
lean_ctor_set(v___x_2011_, 2, v_lctx_1985_);
lean_ctor_set(v___x_2011_, 3, v_localInstances_1986_);
lean_ctor_set(v___x_2011_, 4, v_defEqCtx_x3f_1987_);
lean_ctor_set(v___x_2011_, 5, v_synthPendingDepth_1988_);
lean_ctor_set(v___x_2011_, 6, v_customCanUnfoldPredicate_x3f_1989_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*7, v_trackZetaDelta_1983_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*7 + 1, v_univApprox_1990_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1991_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*7 + 3, v_cacheInferType_1992_);
v___x_2012_ = l_Lean_Meta_getLevel(v_binderType_1957_, v___x_2011_, v_a_1953_, v_a_1954_, v_a_1955_);
lean_dec_ref_known(v___x_2011_, 7);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v___x_2012_, 1);
v_a_1994_ = v_a_2013_;
goto v___jp_1993_;
}
else
{
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2014_; 
v_a_2014_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2012_, 1);
v_a_1994_ = v_a_2014_;
goto v___jp_1993_;
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec_ref(v_body_1960_);
lean_dec_ref(v_binderType_1959_);
lean_dec_ref(v_body_1958_);
lean_dec_ref(v_binderType_1957_);
v_a_2015_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_2012_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2012_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
v___jp_1961_:
{
uint8_t v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = 0;
lean_inc_ref(v_binderType_1959_);
lean_inc_ref(v_binderType_1957_);
v___x_1965_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_binderType_1957_, v_binderType_1959_, v___x_1964_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1967_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref_known(v___x_1965_, 1);
lean_inc_ref(v_body_1960_);
lean_inc_ref(v_body_1958_);
v___x_1967_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_body_1958_, v_body_1960_, v___x_1964_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1981_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1970_ = v___x_1967_;
v_isShared_1971_ = v_isSharedCheck_1981_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1967_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1981_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1972_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__1));
v___x_1973_ = lean_box(0);
v___x_1974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1974_, 0, v_a_1963_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___x_1975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___y_1962_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = l_Lean_mkConst(v___x_1972_, v___x_1975_);
v___x_1977_ = l_Lean_mkApp6(v___x_1976_, v_binderType_1957_, v_binderType_1959_, v_body_1958_, v_body_1960_, v_a_1966_, v_a_1968_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1977_);
v___x_1979_ = v___x_1970_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
else
{
lean_dec(v_a_1966_);
lean_dec(v_a_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v_body_1960_);
lean_dec_ref(v_binderType_1959_);
lean_dec_ref(v_body_1958_);
lean_dec_ref(v_binderType_1957_);
return v___x_1967_;
}
}
else
{
lean_dec(v_a_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v_body_1960_);
lean_dec_ref(v_binderType_1959_);
lean_dec_ref(v_body_1958_);
lean_dec_ref(v_binderType_1957_);
return v___x_1965_;
}
}
v___jp_1993_:
{
uint8_t v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1995_ = 1;
lean_inc_ref(v_keyedConfig_1982_);
v___x_1996_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1995_, v_keyedConfig_1982_);
lean_inc(v_customCanUnfoldPredicate_x3f_1989_);
lean_inc(v_synthPendingDepth_1988_);
lean_inc(v_defEqCtx_x3f_1987_);
lean_inc_ref(v_localInstances_1986_);
lean_inc_ref(v_lctx_1985_);
lean_inc(v_zetaDeltaSet_1984_);
v___x_1997_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
lean_ctor_set(v___x_1997_, 1, v_zetaDeltaSet_1984_);
lean_ctor_set(v___x_1997_, 2, v_lctx_1985_);
lean_ctor_set(v___x_1997_, 3, v_localInstances_1986_);
lean_ctor_set(v___x_1997_, 4, v_defEqCtx_x3f_1987_);
lean_ctor_set(v___x_1997_, 5, v_synthPendingDepth_1988_);
lean_ctor_set(v___x_1997_, 6, v_customCanUnfoldPredicate_x3f_1989_);
lean_ctor_set_uint8(v___x_1997_, sizeof(void*)*7, v_trackZetaDelta_1983_);
lean_ctor_set_uint8(v___x_1997_, sizeof(void*)*7 + 1, v_univApprox_1990_);
lean_ctor_set_uint8(v___x_1997_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1991_);
lean_ctor_set_uint8(v___x_1997_, sizeof(void*)*7 + 3, v_cacheInferType_1992_);
lean_inc_ref(v_body_1958_);
v___x_1998_ = l_Lean_Meta_getLevel(v_body_1958_, v___x_1997_, v_a_1953_, v_a_1954_, v_a_1955_);
lean_dec_ref_known(v___x_1997_, 7);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
v___y_1962_ = v_a_1994_;
v_a_1963_ = v_a_1999_;
goto v___jp_1961_;
}
else
{
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_2000_; 
v_a_2000_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1998_, 1);
v___y_1962_ = v_a_1994_;
v_a_1963_ = v_a_2000_;
goto v___jp_1961_;
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec(v_a_1994_);
lean_dec_ref(v_body_1960_);
lean_dec_ref(v_binderType_1959_);
lean_dec_ref(v_body_1958_);
lean_dec_ref(v_binderType_1957_);
v_a_2001_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1998_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1998_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
}
else
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
lean_dec_ref_known(v_lhs_1943_, 3);
lean_dec_ref(v_rhs_1944_);
v___x_2023_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3);
v___x_2024_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2023_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
return v___x_2024_;
}
}
else
{
lean_object* v___x_2025_; 
lean_inc_ref(v_lhs_1943_);
v___x_2025_ = l_Lean_Meta_Grind_useFunCC___redArg(v_lhs_1943_, v_a_1946_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; uint8_t v___x_2027_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2025_, 1);
v___x_2027_ = lean_unbox(v_a_2026_);
lean_dec(v_a_2026_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
v___x_2028_ = l_Lean_Expr_getAppNumArgs(v_lhs_1943_);
v___x_2029_ = l_Lean_Expr_getAppNumArgs(v_rhs_1944_);
v___x_2030_ = lean_nat_dec_eq(v___x_2029_, v___x_2028_);
lean_dec(v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
lean_dec(v___x_2028_);
lean_dec_ref(v_rhs_1944_);
lean_dec_ref(v_lhs_1943_);
v___x_2031_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5);
v___x_2032_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2031_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
return v___x_2032_;
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___y_2050_; uint8_t v___y_2062_; lean_object* v___x_2066_; uint8_t v___x_2067_; uint8_t v___y_2072_; 
v___x_2033_ = l_Lean_Expr_getAppFn(v_lhs_1943_);
v___x_2034_ = l_Lean_Expr_getAppFn(v_rhs_1944_);
v___x_2066_ = lean_unsigned_to_nat(2u);
v___x_2067_ = lean_nat_dec_eq(v___x_2028_, v___x_2066_);
if (v___x_2067_ == 0)
{
v___y_2072_ = v___x_2067_;
goto v___jp_2071_;
}
else
{
lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2076_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9));
v___x_2077_ = l_Lean_Expr_isConstOf(v___x_2033_, v___x_2076_);
v___y_2072_ = v___x_2077_;
goto v___jp_2071_;
}
v___jp_2035_:
{
lean_object* v___x_2036_; 
lean_inc_ref(v_rhs_1944_);
lean_inc_ref(v_lhs_1943_);
v___x_2036_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(v_lhs_1943_, v_rhs_1944_, v___x_2033_, v___x_2034_, v___x_2028_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
lean_dec_ref(v___x_2034_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; uint8_t v___x_2038_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2036_, 1);
v___x_2038_ = lean_unbox(v_a_2037_);
lean_dec(v_a_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; 
v___x_2039_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_1943_, v_rhs_1944_, v_heq_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
return v___x_2039_;
}
else
{
lean_object* v___x_2040_; 
v___x_2040_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_1943_, v_rhs_1944_, v_heq_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
lean_dec_ref(v_rhs_1944_);
lean_dec_ref(v_lhs_1943_);
return v___x_2040_;
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec_ref(v_rhs_1944_);
lean_dec_ref(v_lhs_1943_);
v_a_2041_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2036_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2036_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
v___jp_2049_:
{
if (v___y_2050_ == 0)
{
goto v___jp_2035_;
}
else
{
lean_object* v___x_2051_; uint8_t v___x_2052_; 
v___x_2051_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_2052_ = l_Lean_Expr_isConstOf(v___x_2034_, v___x_2051_);
if (v___x_2052_ == 0)
{
goto v___jp_2035_;
}
else
{
lean_object* v___x_2053_; 
lean_dec_ref(v___x_2034_);
lean_dec_ref(v___x_2033_);
lean_dec(v___x_2028_);
v___x_2053_ = l_Lean_Meta_Grind_mkEqCongrProof(v_lhs_1943_, v_rhs_1944_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
if (lean_obj_tag(v___x_2053_) == 0)
{
if (v_heq_1945_ == 0)
{
return v___x_2053_;
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2055_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref_known(v___x_2053_, 1);
v___x_2055_ = l_Lean_Meta_mkHEqOfEq(v_a_2054_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
return v___x_2055_;
}
}
else
{
return v___x_2053_;
}
}
}
}
v___jp_2056_:
{
lean_object* v___x_2057_; uint8_t v___x_2058_; 
v___x_2057_ = lean_unsigned_to_nat(3u);
v___x_2058_ = lean_nat_dec_eq(v___x_2028_, v___x_2057_);
if (v___x_2058_ == 0)
{
v___y_2050_ = v___x_2058_;
goto v___jp_2049_;
}
else
{
lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2059_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_2060_ = l_Lean_Expr_isConstOf(v___x_2033_, v___x_2059_);
v___y_2050_ = v___x_2060_;
goto v___jp_2049_;
}
}
v___jp_2061_:
{
if (v___y_2062_ == 0)
{
goto v___jp_2056_;
}
else
{
lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2063_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7));
v___x_2064_ = l_Lean_Expr_isConstOf(v___x_2034_, v___x_2063_);
if (v___x_2064_ == 0)
{
goto v___jp_2056_;
}
else
{
lean_object* v___x_2065_; 
lean_dec_ref(v___x_2034_);
lean_dec_ref(v___x_2033_);
lean_dec(v___x_2028_);
v___x_2065_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_1943_, v_rhs_1944_, v_heq_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
lean_dec_ref(v_rhs_1944_);
lean_dec_ref(v_lhs_1943_);
return v___x_2065_;
}
}
}
v___jp_2068_:
{
if (v___x_2067_ == 0)
{
v___y_2062_ = v___x_2067_;
goto v___jp_2061_;
}
else
{
lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2069_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7));
v___x_2070_ = l_Lean_Expr_isConstOf(v___x_2033_, v___x_2069_);
v___y_2062_ = v___x_2070_;
goto v___jp_2061_;
}
}
v___jp_2071_:
{
if (v___y_2072_ == 0)
{
goto v___jp_2068_;
}
else
{
lean_object* v___x_2073_; uint8_t v___x_2074_; 
v___x_2073_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9));
v___x_2074_ = l_Lean_Expr_isConstOf(v___x_2034_, v___x_2073_);
if (v___x_2074_ == 0)
{
goto v___jp_2068_;
}
else
{
lean_object* v___x_2075_; 
lean_dec_ref(v___x_2034_);
lean_dec_ref(v___x_2033_);
lean_dec(v___x_2028_);
v___x_2075_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_1943_, v_rhs_1944_, v_heq_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
lean_dec_ref(v_rhs_1944_);
lean_dec_ref(v_lhs_1943_);
return v___x_2075_;
}
}
}
}
}
else
{
lean_object* v___x_2078_; 
v___x_2078_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_1943_, v_rhs_1944_, v_heq_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
return v___x_2078_;
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec_ref(v_rhs_1944_);
lean_dec_ref(v_lhs_1943_);
v_a_2079_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2025_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2025_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(lean_object* v_lhs_2087_, lean_object* v_rhs_2088_, lean_object* v_h_2089_, uint8_t v_flipped_2090_, uint8_t v_heq_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2103_ = l_Lean_Meta_Grind_congrPlaceholderProof;
v___x_2104_ = lean_expr_eqv(v_h_2089_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2105_ = l_Lean_Meta_Grind_eqCongrSymmPlaceholderProof;
v___x_2106_ = lean_expr_eqv(v_h_2089_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; 
lean_dec_ref(v_rhs_2088_);
lean_dec_ref(v_lhs_2087_);
v___x_2107_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(v_h_2089_, v_flipped_2090_, v_heq_2091_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
return v___x_2107_;
}
else
{
lean_object* v___x_2108_; 
lean_dec_ref(v_h_2089_);
v___x_2108_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(v_lhs_2087_, v_rhs_2088_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
if (lean_obj_tag(v___x_2108_) == 0)
{
if (v_heq_2091_ == 0)
{
return v___x_2108_;
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2110_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v___x_2108_, 1);
v___x_2110_ = l_Lean_Meta_mkHEqOfEq(v_a_2109_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
return v___x_2110_;
}
}
else
{
return v___x_2108_;
}
}
}
else
{
lean_object* v___x_2111_; 
lean_dec_ref(v_h_2089_);
v___x_2111_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(v_lhs_2087_, v_rhs_2088_, v_heq_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
return v___x_2111_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1(void){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2113_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2114_ = lean_unsigned_to_nat(29u);
v___x_2115_ = lean_unsigned_to_nat(288u);
v___x_2116_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0));
v___x_2117_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2118_ = l_mkPanicMessageWithDecl(v___x_2117_, v___x_2116_, v___x_2115_, v___x_2114_, v___x_2113_);
return v___x_2118_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2119_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2120_ = lean_unsigned_to_nat(35u);
v___x_2121_ = lean_unsigned_to_nat(287u);
v___x_2122_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0));
v___x_2123_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2124_ = l_mkPanicMessageWithDecl(v___x_2123_, v___x_2122_, v___x_2121_, v___x_2120_, v___x_2119_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(lean_object* v_lhs_2125_, lean_object* v_common_2126_, lean_object* v_acc_2127_, uint8_t v_heq_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
size_t v___x_2140_; size_t v___x_2141_; uint8_t v___x_2142_; 
v___x_2140_ = lean_ptr_addr(v_lhs_2125_);
v___x_2141_ = lean_ptr_addr(v_common_2126_);
v___x_2142_ = lean_usize_dec_eq(v___x_2140_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = lean_st_ref_get(v_a_2129_);
lean_inc_ref(v_lhs_2125_);
v___x_2144_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2143_, v_lhs_2125_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
lean_dec(v___x_2143_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v_target_x3f_2146_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v_target_x3f_2146_ = lean_ctor_get(v_a_2145_, 4);
lean_inc(v_target_x3f_2146_);
if (lean_obj_tag(v_target_x3f_2146_) == 1)
{
lean_object* v_proof_x3f_2147_; 
v_proof_x3f_2147_ = lean_ctor_get(v_a_2145_, 5);
lean_inc(v_proof_x3f_2147_);
if (lean_obj_tag(v_proof_x3f_2147_) == 1)
{
uint8_t v_flipped_2148_; lean_object* v_val_2149_; lean_object* v_val_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2178_; 
v_flipped_2148_ = lean_ctor_get_uint8(v_a_2145_, sizeof(void*)*12);
lean_dec(v_a_2145_);
v_val_2149_ = lean_ctor_get(v_target_x3f_2146_, 0);
lean_inc(v_val_2149_);
lean_dec_ref_known(v_target_x3f_2146_, 1);
v_val_2150_ = lean_ctor_get(v_proof_x3f_2147_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_proof_x3f_2147_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2152_ = v_proof_x3f_2147_;
v_isShared_2153_ = v_isSharedCheck_2178_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_val_2150_);
lean_dec(v_proof_x3f_2147_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2178_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; 
lean_inc(v_val_2149_);
v___x_2154_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_lhs_2125_, v_val_2149_, v_val_2150_, v_flipped_2148_, v_heq_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2156_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v___x_2154_, 1);
v___x_2156_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_acc_2127_, v_a_2155_, v_heq_2128_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2159_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref_known(v___x_2156_, 1);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v_a_2157_);
v___x_2159_ = v___x_2152_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2157_);
v___x_2159_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
v_lhs_2125_ = v_val_2149_;
v_acc_2127_ = v___x_2159_;
goto _start;
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_del_object(v___x_2152_);
lean_dec(v_val_2149_);
v_a_2162_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2156_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2156_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
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
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_del_object(v___x_2152_);
lean_dec(v_val_2149_);
lean_dec(v_acc_2127_);
v_a_2170_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2154_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2154_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
}
else
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
lean_dec(v_proof_x3f_2147_);
lean_dec_ref_known(v_target_x3f_2146_, 1);
lean_dec(v_a_2145_);
lean_dec(v_acc_2127_);
lean_dec_ref(v_lhs_2125_);
v___x_2179_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1);
v___x_2180_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2179_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
return v___x_2180_;
}
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
lean_dec(v_target_x3f_2146_);
lean_dec(v_a_2145_);
lean_dec(v_acc_2127_);
lean_dec_ref(v_lhs_2125_);
v___x_2181_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2);
v___x_2182_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2181_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
return v___x_2182_;
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_dec(v_acc_2127_);
lean_dec_ref(v_lhs_2125_);
v_a_2183_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2144_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2144_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
else
{
lean_object* v___x_2191_; 
lean_dec_ref(v_lhs_2125_);
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v_acc_2127_);
return v___x_2191_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2193_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2194_ = lean_unsigned_to_nat(29u);
v___x_2195_ = lean_unsigned_to_nat(300u);
v___x_2196_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0));
v___x_2197_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2198_ = l_mkPanicMessageWithDecl(v___x_2197_, v___x_2196_, v___x_2195_, v___x_2194_, v___x_2193_);
return v___x_2198_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2(void){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2199_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2200_ = lean_unsigned_to_nat(35u);
v___x_2201_ = lean_unsigned_to_nat(299u);
v___x_2202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0));
v___x_2203_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2204_ = l_mkPanicMessageWithDecl(v___x_2203_, v___x_2202_, v___x_2201_, v___x_2200_, v___x_2199_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(lean_object* v_rhs_2205_, lean_object* v_common_2206_, lean_object* v_lhsEqCommon_x3f_2207_, uint8_t v_heq_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
size_t v___x_2220_; size_t v___x_2221_; uint8_t v___x_2222_; 
v___x_2220_ = lean_ptr_addr(v_rhs_2205_);
v___x_2221_ = lean_ptr_addr(v_common_2206_);
v___x_2222_ = lean_usize_dec_eq(v___x_2220_, v___x_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = lean_st_ref_get(v_a_2209_);
lean_inc_ref(v_rhs_2205_);
v___x_2224_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2223_, v_rhs_2205_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
lean_dec(v___x_2223_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v_target_x3f_2226_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref_known(v___x_2224_, 1);
v_target_x3f_2226_ = lean_ctor_get(v_a_2225_, 4);
lean_inc(v_target_x3f_2226_);
if (lean_obj_tag(v_target_x3f_2226_) == 1)
{
lean_object* v_proof_x3f_2227_; 
v_proof_x3f_2227_ = lean_ctor_get(v_a_2225_, 5);
lean_inc(v_proof_x3f_2227_);
if (lean_obj_tag(v_proof_x3f_2227_) == 1)
{
uint8_t v_flipped_2228_; lean_object* v_val_2229_; lean_object* v_val_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2269_; 
v_flipped_2228_ = lean_ctor_get_uint8(v_a_2225_, sizeof(void*)*12);
lean_dec(v_a_2225_);
v_val_2229_ = lean_ctor_get(v_target_x3f_2226_, 0);
lean_inc(v_val_2229_);
lean_dec_ref_known(v_target_x3f_2226_, 1);
v_val_2230_ = lean_ctor_get(v_proof_x3f_2227_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_proof_x3f_2227_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2232_ = v_proof_x3f_2227_;
v_isShared_2233_ = v_isSharedCheck_2269_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_val_2230_);
lean_dec(v_proof_x3f_2227_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2269_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
uint8_t v___y_2235_; 
if (v_flipped_2228_ == 0)
{
uint8_t v___x_2268_; 
v___x_2268_ = 1;
v___y_2235_ = v___x_2268_;
goto v___jp_2234_;
}
else
{
v___y_2235_ = v___x_2222_;
goto v___jp_2234_;
}
v___jp_2234_:
{
lean_object* v___x_2236_; 
lean_inc(v_val_2229_);
v___x_2236_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_val_2229_, v_rhs_2205_, v_val_2230_, v___y_2235_, v_heq_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2238_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___x_2236_, 1);
v___x_2238_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_val_2229_, v_common_2206_, v_lhsEqCommon_x3f_2207_, v_heq_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2240_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2238_, 1);
v___x_2240_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_a_2239_, v_a_2237_, v_heq_2208_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2251_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2251_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2251_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v_a_2241_);
v___x_2246_ = v___x_2232_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
lean_object* v___x_2248_; 
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v___x_2246_);
v___x_2248_ = v___x_2243_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
lean_del_object(v___x_2232_);
v_a_2252_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___x_2240_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2240_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
else
{
lean_dec(v_a_2237_);
lean_del_object(v___x_2232_);
return v___x_2238_;
}
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
lean_del_object(v___x_2232_);
lean_dec(v_val_2229_);
lean_dec(v_lhsEqCommon_x3f_2207_);
v_a_2260_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2236_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2236_);
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
}
}
else
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
lean_dec(v_proof_x3f_2227_);
lean_dec_ref_known(v_target_x3f_2226_, 1);
lean_dec(v_a_2225_);
lean_dec(v_lhsEqCommon_x3f_2207_);
lean_dec_ref(v_rhs_2205_);
v___x_2270_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1);
v___x_2271_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2270_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
return v___x_2271_;
}
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_dec(v_target_x3f_2226_);
lean_dec(v_a_2225_);
lean_dec(v_lhsEqCommon_x3f_2207_);
lean_dec_ref(v_rhs_2205_);
v___x_2272_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2);
v___x_2273_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2272_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
return v___x_2273_;
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec(v_lhsEqCommon_x3f_2207_);
lean_dec_ref(v_rhs_2205_);
v_a_2274_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2224_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2224_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
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
else
{
lean_object* v___x_2282_; 
lean_dec_ref(v_rhs_2205_);
v___x_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2282_, 0, v_lhsEqCommon_x3f_2207_);
return v___x_2282_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3(void){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2283_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2284_ = lean_unsigned_to_nat(72u);
v___x_2285_ = lean_unsigned_to_nat(321u);
v___x_2286_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0));
v___x_2287_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2288_ = l_mkPanicMessageWithDecl(v___x_2287_, v___x_2286_, v___x_2285_, v___x_2284_, v___x_2283_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(lean_object* v_lhs_2289_, lean_object* v_rhs_2290_, uint8_t v_heq_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
size_t v___x_2303_; size_t v___x_2304_; uint8_t v___x_2305_; 
v___x_2303_ = lean_ptr_addr(v_lhs_2289_);
v___x_2304_ = lean_ptr_addr(v_rhs_2290_);
v___x_2305_ = lean_usize_dec_eq(v___x_2303_, v___x_2304_);
if (v___x_2305_ == 0)
{
lean_object* v___x_2306_; 
lean_inc_ref(v_lhs_2289_);
v___x_2306_ = l_Lean_Meta_Grind_getRootENode___redArg(v_lhs_2289_, v_a_2292_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2308_ = lean_st_ref_get(v_a_2292_);
lean_inc_ref(v_lhs_2289_);
v___x_2309_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2308_, v_lhs_2289_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
lean_dec(v___x_2308_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
lean_dec_ref_known(v___x_2309_, 1);
v___x_2311_ = lean_st_ref_get(v_a_2292_);
lean_inc_ref(v_rhs_2290_);
v___x_2312_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2311_, v_rhs_2290_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
lean_dec(v___x_2311_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v_root_2314_; lean_object* v_root_2315_; size_t v___x_2316_; size_t v___x_2317_; uint8_t v___x_2318_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
lean_dec_ref_known(v___x_2312_, 1);
v_root_2314_ = lean_ctor_get(v_a_2310_, 2);
lean_inc_ref(v_root_2314_);
lean_dec(v_a_2310_);
v_root_2315_ = lean_ctor_get(v_a_2313_, 2);
lean_inc_ref(v_root_2315_);
lean_dec(v_a_2313_);
v___x_2316_ = lean_ptr_addr(v_root_2314_);
lean_dec_ref(v_root_2314_);
v___x_2317_ = lean_ptr_addr(v_root_2315_);
lean_dec_ref(v_root_2315_);
v___x_2318_ = lean_usize_dec_eq(v___x_2316_, v___x_2317_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
lean_dec(v_a_2307_);
lean_dec_ref(v_rhs_2290_);
lean_dec_ref(v_lhs_2289_);
v___x_2319_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2);
v___x_2320_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2319_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
return v___x_2320_;
}
else
{
lean_object* v___x_2321_; 
lean_inc_ref(v_rhs_2290_);
lean_inc_ref(v_lhs_2289_);
v___x_2321_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(v_lhs_2289_, v_rhs_2290_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; uint8_t v_heqProofs_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref_known(v___x_2321_, 1);
v_heqProofs_2323_ = lean_ctor_get_uint8(v_a_2307_, sizeof(void*)*12 + 4);
lean_dec(v_a_2307_);
v___x_2324_ = lean_box(0);
v___x_2325_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_2289_, v_a_2322_, v___x_2324_, v_heqProofs_2323_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2327_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref_known(v___x_2325_, 1);
v___x_2327_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_2290_, v_a_2322_, v_a_2326_, v_heqProofs_2323_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
lean_dec(v_a_2322_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2343_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2330_ = v___x_2327_;
v_isShared_2331_ = v_isSharedCheck_2343_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2327_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2343_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
if (lean_obj_tag(v_a_2328_) == 1)
{
lean_object* v_val_2332_; uint8_t v___y_2337_; 
v_val_2332_ = lean_ctor_get(v_a_2328_, 0);
lean_inc(v_val_2332_);
lean_dec_ref_known(v_a_2328_, 1);
if (v_heq_2291_ == 0)
{
if (v_heqProofs_2323_ == 0)
{
v___y_2337_ = v___x_2318_;
goto v___jp_2336_;
}
else
{
lean_del_object(v___x_2330_);
goto v___jp_2333_;
}
}
else
{
v___y_2337_ = v_heqProofs_2323_;
goto v___jp_2336_;
}
v___jp_2333_:
{
if (v_heq_2291_ == 0)
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Lean_Meta_mkEqOfHEq(v_val_2332_, v_heq_2291_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
return v___x_2334_;
}
else
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Lean_Meta_mkHEqOfEq(v_val_2332_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
return v___x_2335_;
}
}
v___jp_2336_:
{
if (v___y_2337_ == 0)
{
lean_del_object(v___x_2330_);
goto v___jp_2333_;
}
else
{
lean_object* v___x_2339_; 
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 0, v_val_2332_);
v___x_2339_ = v___x_2330_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_val_2332_);
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
lean_object* v___x_2341_; lean_object* v___x_2342_; 
lean_del_object(v___x_2330_);
lean_dec(v_a_2328_);
v___x_2341_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3);
v___x_2342_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2341_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
return v___x_2342_;
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
v_a_2344_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2327_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2327_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec(v_a_2322_);
lean_dec_ref(v_rhs_2290_);
v_a_2352_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2325_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2325_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
else
{
lean_dec(v_a_2307_);
lean_dec_ref(v_rhs_2290_);
lean_dec_ref(v_lhs_2289_);
return v___x_2321_;
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v_a_2310_);
lean_dec(v_a_2307_);
lean_dec_ref(v_rhs_2290_);
lean_dec_ref(v_lhs_2289_);
v_a_2360_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2312_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2312_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v_a_2307_);
lean_dec_ref(v_rhs_2290_);
lean_dec_ref(v_lhs_2289_);
v_a_2368_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2309_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2309_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec_ref(v_rhs_2290_);
lean_dec_ref(v_lhs_2289_);
v_a_2376_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2306_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2306_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
else
{
lean_object* v___x_2384_; 
lean_dec_ref(v_rhs_2290_);
v___x_2384_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(v_lhs_2289_, v_heq_2291_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
return v___x_2384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(lean_object* v_thm_2385_, lean_object* v_lhs_2386_, lean_object* v_rhs_2387_, lean_object* v_i_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v___x_2400_; uint8_t v___x_2401_; 
v___x_2400_ = lean_unsigned_to_nat(0u);
v___x_2401_ = lean_nat_dec_lt(v___x_2400_, v_i_2388_);
if (v___x_2401_ == 0)
{
lean_object* v_proof_2402_; lean_object* v___x_2403_; 
v_proof_2402_ = lean_ctor_get(v_thm_2385_, 1);
lean_inc_ref(v_proof_2402_);
v___x_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2403_, 0, v_proof_2402_);
return v___x_2403_;
}
else
{
lean_object* v___x_2404_; lean_object* v_i_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2404_ = lean_unsigned_to_nat(1u);
v_i_2405_ = lean_nat_sub(v_i_2388_, v___x_2404_);
v___x_2406_ = l_Lean_Expr_appFn_x21(v_lhs_2386_);
v___x_2407_ = l_Lean_Expr_appFn_x21(v_rhs_2387_);
v___x_2408_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_2385_, v___x_2406_, v___x_2407_, v_i_2405_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
lean_dec_ref(v___x_2407_);
lean_dec_ref(v___x_2406_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v_argKinds_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___y_2414_; uint8_t v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2408_, 1);
v_argKinds_2410_ = lean_ctor_get(v_thm_2385_, 2);
v___x_2411_ = l_Lean_Expr_appArg_x21(v_lhs_2386_);
v___x_2412_ = l_Lean_Expr_appArg_x21(v_rhs_2387_);
v___x_2425_ = 0;
v___x_2426_ = lean_box(v___x_2425_);
v___x_2427_ = lean_array_get(v___x_2426_, v_argKinds_2410_, v_i_2405_);
lean_dec(v_i_2405_);
lean_dec(v___x_2426_);
v___x_2428_ = lean_unbox(v___x_2427_);
lean_dec(v___x_2427_);
if (v___x_2428_ == 4)
{
v___y_2414_ = v___x_2401_;
goto v___jp_2413_;
}
else
{
uint8_t v___x_2429_; 
v___x_2429_ = 0;
v___y_2414_ = v___x_2429_;
goto v___jp_2413_;
}
v___jp_2413_:
{
lean_object* v___x_2415_; 
lean_inc_ref(v___x_2412_);
lean_inc_ref(v___x_2411_);
v___x_2415_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___x_2411_, v___x_2412_, v___y_2414_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2424_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2420_ = l_Lean_mkApp3(v_a_2409_, v___x_2411_, v___x_2412_, v_a_2416_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2420_);
v___x_2422_ = v___x_2418_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
else
{
lean_dec_ref(v___x_2412_);
lean_dec_ref(v___x_2411_);
lean_dec(v_a_2409_);
return v___x_2415_;
}
}
}
else
{
lean_dec(v_i_2405_);
return v___x_2408_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(lean_object* v_f_2433_, lean_object* v_g_2434_, lean_object* v_numArgs_2435_, lean_object* v_lhs_2436_, lean_object* v_rhs_2437_, uint8_t v_heq_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v___x_2450_; 
lean_inc(v_numArgs_2435_);
lean_inc_ref(v_f_2433_);
v___x_2450_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(v_f_2433_, v_numArgs_2435_, v_a_2442_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v_argKinds_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2451_);
lean_dec_ref_known(v___x_2450_, 1);
v_argKinds_2452_ = lean_ctor_get(v_a_2451_, 2);
v___x_2453_ = lean_array_get_size(v_argKinds_2452_);
v___x_2454_ = lean_nat_dec_eq(v___x_2453_, v_numArgs_2435_);
if (v___x_2454_ == 0)
{
lean_object* v___x_2455_; lean_object* v___x_2456_; 
lean_dec(v_a_2451_);
lean_dec_ref(v_rhs_2437_);
lean_dec_ref(v_lhs_2436_);
lean_dec(v_numArgs_2435_);
lean_dec_ref(v_g_2434_);
lean_dec_ref(v_f_2433_);
v___x_2455_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2);
v___x_2456_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2455_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
return v___x_2456_;
}
else
{
lean_object* v___x_2457_; 
v___x_2457_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_2451_, v_lhs_2436_, v_rhs_2437_, v_numArgs_2435_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
lean_dec(v_a_2451_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; size_t v___x_2459_; size_t v___x_2460_; uint8_t v___x_2461_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref_known(v___x_2457_, 1);
v___x_2459_ = lean_ptr_addr(v_f_2433_);
v___x_2460_ = lean_ptr_addr(v_g_2434_);
v___x_2461_ = lean_usize_dec_eq(v___x_2459_, v___x_2460_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__4));
v___x_2463_ = l_Lean_Core_mkFreshUserName(v___x_2462_, v_a_2447_, v_a_2448_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2465_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2464_);
lean_dec_ref_known(v___x_2463_, 1);
lean_inc(v_a_2448_);
lean_inc_ref(v_a_2447_);
lean_inc(v_a_2446_);
lean_inc_ref(v_a_2445_);
lean_inc_ref(v_f_2433_);
v___x_2465_ = lean_infer_type(v_f_2433_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___f_2469_; lean_object* v___x_2470_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___x_2465_, 1);
v___x_2467_ = lean_box(v___x_2461_);
v___x_2468_ = lean_box(v___x_2454_);
v___f_2469_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___boxed), 17, 5);
lean_closure_set(v___f_2469_, 0, v_numArgs_2435_);
lean_closure_set(v___f_2469_, 1, v_rhs_2437_);
lean_closure_set(v___f_2469_, 2, v_lhs_2436_);
lean_closure_set(v___f_2469_, 3, v___x_2467_);
lean_closure_set(v___f_2469_, 4, v___x_2468_);
v___x_2470_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_a_2464_, v_a_2466_, v___f_2469_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; lean_object* v___x_2472_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2471_);
lean_dec_ref_known(v___x_2470_, 1);
v___x_2472_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_f_2433_, v_g_2434_, v___x_2461_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; lean_object* v___x_2474_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_a_2473_);
lean_dec_ref_known(v___x_2472_, 1);
v___x_2474_ = l_Lean_Meta_mkEqNDRec(v_a_2471_, v_a_2458_, v_a_2473_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v___x_2476_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref_known(v___x_2474_, 1);
v___x_2476_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_2475_, v_heq_2438_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
return v___x_2476_;
}
else
{
return v___x_2474_;
}
}
else
{
lean_dec(v_a_2471_);
lean_dec(v_a_2458_);
return v___x_2472_;
}
}
else
{
lean_dec(v_a_2458_);
lean_dec_ref(v_g_2434_);
lean_dec_ref(v_f_2433_);
return v___x_2470_;
}
}
else
{
lean_dec(v_a_2464_);
lean_dec(v_a_2458_);
lean_dec_ref(v_rhs_2437_);
lean_dec_ref(v_lhs_2436_);
lean_dec(v_numArgs_2435_);
lean_dec_ref(v_g_2434_);
lean_dec_ref(v_f_2433_);
return v___x_2465_;
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec(v_a_2458_);
lean_dec_ref(v_rhs_2437_);
lean_dec_ref(v_lhs_2436_);
lean_dec(v_numArgs_2435_);
lean_dec_ref(v_g_2434_);
lean_dec_ref(v_f_2433_);
v_a_2477_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2463_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2463_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
else
{
lean_object* v___x_2485_; 
lean_dec_ref(v_rhs_2437_);
lean_dec_ref(v_lhs_2436_);
lean_dec(v_numArgs_2435_);
lean_dec_ref(v_g_2434_);
lean_dec_ref(v_f_2433_);
v___x_2485_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_2458_, v_heq_2438_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
return v___x_2485_;
}
}
else
{
lean_dec_ref(v_rhs_2437_);
lean_dec_ref(v_lhs_2436_);
lean_dec(v_numArgs_2435_);
lean_dec_ref(v_g_2434_);
lean_dec_ref(v_f_2433_);
return v___x_2457_;
}
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec_ref(v_rhs_2437_);
lean_dec_ref(v_lhs_2436_);
lean_dec(v_numArgs_2435_);
lean_dec_ref(v_g_2434_);
lean_dec_ref(v_f_2433_);
v_a_2486_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2450_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2450_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1(void){
_start:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2495_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2496_ = lean_unsigned_to_nat(27u);
v___x_2497_ = lean_unsigned_to_nat(237u);
v___x_2498_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0));
v___x_2499_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2500_ = l_mkPanicMessageWithDecl(v___x_2499_, v___x_2498_, v___x_2497_, v___x_2496_, v___x_2495_);
return v___x_2500_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2(void){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2501_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2502_ = lean_unsigned_to_nat(27u);
v___x_2503_ = lean_unsigned_to_nat(236u);
v___x_2504_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0));
v___x_2505_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2506_ = l_mkPanicMessageWithDecl(v___x_2505_, v___x_2504_, v___x_2503_, v___x_2502_, v___x_2501_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(lean_object* v_lhs_2507_, lean_object* v_rhs_2508_, uint8_t v_heq_2509_, lean_object* v_e_u2081_2510_, lean_object* v_e_u2082_2511_, lean_object* v_numArgs_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_){
_start:
{
if (lean_obj_tag(v_e_u2081_2510_) == 5)
{
if (lean_obj_tag(v_e_u2082_2511_) == 5)
{
lean_object* v_fn_2524_; lean_object* v_fn_2525_; lean_object* v___x_2526_; lean_object* v_numArgs_2527_; size_t v___x_2528_; size_t v___x_2529_; uint8_t v___x_2530_; 
v_fn_2524_ = lean_ctor_get(v_e_u2081_2510_, 0);
lean_inc_ref(v_fn_2524_);
lean_dec_ref_known(v_e_u2081_2510_, 2);
v_fn_2525_ = lean_ctor_get(v_e_u2082_2511_, 0);
lean_inc_ref(v_fn_2525_);
lean_dec_ref_known(v_e_u2082_2511_, 2);
v___x_2526_ = lean_unsigned_to_nat(1u);
v_numArgs_2527_ = lean_nat_add(v_numArgs_2512_, v___x_2526_);
lean_dec(v_numArgs_2512_);
v___x_2528_ = lean_ptr_addr(v_fn_2524_);
v___x_2529_ = lean_ptr_addr(v_fn_2525_);
v___x_2530_ = lean_usize_dec_eq(v___x_2528_, v___x_2529_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; 
lean_inc_ref(v_fn_2525_);
lean_inc_ref(v_fn_2524_);
v___x_2531_ = l_Lean_Meta_Grind_hasSameType(v_fn_2524_, v_fn_2525_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; uint8_t v___x_2533_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2532_);
lean_dec_ref_known(v___x_2531_, 1);
v___x_2533_ = lean_unbox(v_a_2532_);
lean_dec(v_a_2532_);
if (v___x_2533_ == 0)
{
v_e_u2081_2510_ = v_fn_2524_;
v_e_u2082_2511_ = v_fn_2525_;
v_numArgs_2512_ = v_numArgs_2527_;
goto _start;
}
else
{
lean_object* v___x_2535_; 
v___x_2535_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_2524_, v_fn_2525_, v_numArgs_2527_, v_lhs_2507_, v_rhs_2508_, v_heq_2509_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_);
return v___x_2535_;
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec(v_numArgs_2527_);
lean_dec_ref(v_fn_2525_);
lean_dec_ref(v_fn_2524_);
lean_dec_ref(v_rhs_2508_);
lean_dec_ref(v_lhs_2507_);
v_a_2536_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2531_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2531_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
else
{
lean_object* v___x_2544_; 
v___x_2544_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_2524_, v_fn_2525_, v_numArgs_2527_, v_lhs_2507_, v_rhs_2508_, v_heq_2509_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_);
return v___x_2544_;
}
}
else
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
lean_dec_ref_known(v_e_u2081_2510_, 2);
lean_dec(v_numArgs_2512_);
lean_dec_ref(v_e_u2082_2511_);
lean_dec_ref(v_rhs_2508_);
lean_dec_ref(v_lhs_2507_);
v___x_2545_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1);
v___x_2546_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2545_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_);
return v___x_2546_;
}
}
else
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
lean_dec(v_numArgs_2512_);
lean_dec_ref(v_e_u2082_2511_);
lean_dec_ref(v_e_u2081_2510_);
lean_dec_ref(v_rhs_2508_);
lean_dec_ref(v_lhs_2507_);
v___x_2547_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2);
v___x_2548_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2547_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_);
return v___x_2548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(lean_object* v_lhs_2549_, lean_object* v_rhs_2550_, uint8_t v_heq_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_rhs_2550_);
lean_inc_ref(v_lhs_2549_);
v___x_2564_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(v_lhs_2549_, v_rhs_2550_, v_heq_2551_, v_lhs_2549_, v_rhs_2550_, v___x_2563_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC___boxed(lean_object* v_lhs_2565_, lean_object* v_rhs_2566_, lean_object* v_heq_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_){
_start:
{
uint8_t v_heq_boxed_2579_; lean_object* v_res_2580_; 
v_heq_boxed_2579_ = lean_unbox(v_heq_2567_);
v_res_2580_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_2565_, v_rhs_2566_, v_heq_boxed_2579_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
lean_dec(v_a_2568_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___boxed(lean_object* v_lhs_2581_, lean_object* v_rhs_2582_, lean_object* v_heq_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_){
_start:
{
uint8_t v_heq_boxed_2595_; lean_object* v_res_2596_; 
v_heq_boxed_2595_ = lean_unbox(v_heq_2583_);
v_res_2596_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_2581_, v_rhs_2582_, v_heq_boxed_2595_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_);
lean_dec(v_a_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_a_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_a_2589_);
lean_dec_ref(v_a_2588_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2585_);
lean_dec(v_a_2584_);
lean_dec_ref(v_rhs_2582_);
lean_dec_ref(v_lhs_2581_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___boxed(lean_object* v_lhs_2597_, lean_object* v_rhs_2598_, lean_object* v_heq_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
uint8_t v_heq_boxed_2611_; lean_object* v_res_2612_; 
v_heq_boxed_2611_ = lean_unbox(v_heq_2599_);
v_res_2612_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_2597_, v_rhs_2598_, v_heq_boxed_2611_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_);
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
lean_dec_ref(v_rhs_2598_);
lean_dec_ref(v_lhs_2597_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof___boxed(lean_object* v_lhs_2613_, lean_object* v_rhs_2614_, lean_object* v_h_2615_, lean_object* v_flipped_2616_, lean_object* v_heq_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
uint8_t v_flipped_boxed_2629_; uint8_t v_heq_boxed_2630_; lean_object* v_res_2631_; 
v_flipped_boxed_2629_ = lean_unbox(v_flipped_2616_);
v_heq_boxed_2630_ = lean_unbox(v_heq_2617_);
v_res_2631_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_lhs_2613_, v_rhs_2614_, v_h_2615_, v_flipped_boxed_2629_, v_heq_boxed_2630_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec(v_a_2625_);
lean_dec_ref(v_a_2624_);
lean_dec(v_a_2623_);
lean_dec_ref(v_a_2622_);
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec(v_a_2619_);
lean_dec(v_a_2618_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___boxed(lean_object* v_lhs_2632_, lean_object* v_rhs_2633_, lean_object* v_heq_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_){
_start:
{
uint8_t v_heq_boxed_2646_; lean_object* v_res_2647_; 
v_heq_boxed_2646_ = lean_unbox(v_heq_2634_);
v_res_2647_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_2632_, v_rhs_2633_, v_heq_boxed_2646_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
lean_dec(v_a_2640_);
lean_dec_ref(v_a_2639_);
lean_dec(v_a_2638_);
lean_dec_ref(v_a_2637_);
lean_dec(v_a_2636_);
lean_dec(v_a_2635_);
lean_dec_ref(v_rhs_2633_);
lean_dec_ref(v_lhs_2632_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper___boxed(lean_object* v_thm_2648_, lean_object* v_lhs_2649_, lean_object* v_rhs_2650_, lean_object* v_i_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_2648_, v_lhs_2649_, v_rhs_2650_, v_i_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
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
lean_dec(v_i_2651_);
lean_dec_ref(v_rhs_2650_);
lean_dec_ref(v_lhs_2649_);
lean_dec_ref(v_thm_2648_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___boxed(lean_object** _args){
lean_object* v_lhs_2664_ = _args[0];
lean_object* v_rhs_2665_ = _args[1];
lean_object* v_heq_2666_ = _args[2];
lean_object* v_e_u2081_2667_ = _args[3];
lean_object* v_e_u2082_2668_ = _args[4];
lean_object* v_numArgs_2669_ = _args[5];
lean_object* v_a_2670_ = _args[6];
lean_object* v_a_2671_ = _args[7];
lean_object* v_a_2672_ = _args[8];
lean_object* v_a_2673_ = _args[9];
lean_object* v_a_2674_ = _args[10];
lean_object* v_a_2675_ = _args[11];
lean_object* v_a_2676_ = _args[12];
lean_object* v_a_2677_ = _args[13];
lean_object* v_a_2678_ = _args[14];
lean_object* v_a_2679_ = _args[15];
lean_object* v_a_2680_ = _args[16];
_start:
{
uint8_t v_heq_boxed_2681_; lean_object* v_res_2682_; 
v_heq_boxed_2681_ = lean_unbox(v_heq_2666_);
v_res_2682_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(v_lhs_2664_, v_rhs_2665_, v_heq_boxed_2681_, v_e_u2081_2667_, v_e_u2082_2668_, v_numArgs_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
lean_dec(v_a_2673_);
lean_dec_ref(v_a_2672_);
lean_dec(v_a_2671_);
lean_dec(v_a_2670_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___boxed(lean_object* v_lhs_2683_, lean_object* v_common_2684_, lean_object* v_acc_2685_, lean_object* v_heq_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
uint8_t v_heq_boxed_2698_; lean_object* v_res_2699_; 
v_heq_boxed_2698_ = lean_unbox(v_heq_2686_);
v_res_2699_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_2683_, v_common_2684_, v_acc_2685_, v_heq_boxed_2698_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
lean_dec(v_a_2694_);
lean_dec_ref(v_a_2693_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
lean_dec(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_common_2684_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___boxed(lean_object** _args){
lean_object* v_f_2700_ = _args[0];
lean_object* v_g_2701_ = _args[1];
lean_object* v_numArgs_2702_ = _args[2];
lean_object* v_lhs_2703_ = _args[3];
lean_object* v_rhs_2704_ = _args[4];
lean_object* v_heq_2705_ = _args[5];
lean_object* v_a_2706_ = _args[6];
lean_object* v_a_2707_ = _args[7];
lean_object* v_a_2708_ = _args[8];
lean_object* v_a_2709_ = _args[9];
lean_object* v_a_2710_ = _args[10];
lean_object* v_a_2711_ = _args[11];
lean_object* v_a_2712_ = _args[12];
lean_object* v_a_2713_ = _args[13];
lean_object* v_a_2714_ = _args[14];
lean_object* v_a_2715_ = _args[15];
lean_object* v_a_2716_ = _args[16];
_start:
{
uint8_t v_heq_boxed_2717_; lean_object* v_res_2718_; 
v_heq_boxed_2717_ = lean_unbox(v_heq_2705_);
v_res_2718_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_2700_, v_g_2701_, v_numArgs_2702_, v_lhs_2703_, v_rhs_2704_, v_heq_boxed_2717_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
lean_dec(v_a_2707_);
lean_dec(v_a_2706_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___boxed(lean_object* v_rhs_2719_, lean_object* v_common_2720_, lean_object* v_lhsEqCommon_x3f_2721_, lean_object* v_heq_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_){
_start:
{
uint8_t v_heq_boxed_2734_; lean_object* v_res_2735_; 
v_heq_boxed_2734_ = lean_unbox(v_heq_2722_);
v_res_2735_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_2719_, v_common_2720_, v_lhsEqCommon_x3f_2721_, v_heq_boxed_2734_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_);
lean_dec(v_a_2732_);
lean_dec_ref(v_a_2731_);
lean_dec(v_a_2730_);
lean_dec_ref(v_a_2729_);
lean_dec(v_a_2728_);
lean_dec_ref(v_a_2727_);
lean_dec(v_a_2726_);
lean_dec_ref(v_a_2725_);
lean_dec(v_a_2724_);
lean_dec(v_a_2723_);
lean_dec_ref(v_common_2720_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___boxed(lean_object* v_lhs_2736_, lean_object* v_rhs_2737_, lean_object* v_heq_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_){
_start:
{
uint8_t v_heq_boxed_2750_; lean_object* v_res_2751_; 
v_heq_boxed_2750_ = lean_unbox(v_heq_2738_);
v_res_2751_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_2736_, v_rhs_2737_, v_heq_boxed_2750_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
lean_dec(v_a_2746_);
lean_dec_ref(v_a_2745_);
lean_dec(v_a_2744_);
lean_dec_ref(v_a_2743_);
lean_dec(v_a_2742_);
lean_dec_ref(v_a_2741_);
lean_dec(v_a_2740_);
lean_dec(v_a_2739_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop___boxed(lean_object* v_lhs_2752_, lean_object* v_rhs_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_2752_, v_rhs_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
lean_dec(v_a_2763_);
lean_dec_ref(v_a_2762_);
lean_dec(v_a_2761_);
lean_dec_ref(v_a_2760_);
lean_dec(v_a_2759_);
lean_dec_ref(v_a_2758_);
lean_dec(v_a_2757_);
lean_dec_ref(v_a_2756_);
lean_dec(v_a_2755_);
lean_dec(v_a_2754_);
lean_dec_ref(v_rhs_2753_);
lean_dec_ref(v_lhs_2752_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___boxed(lean_object* v_lhs_2766_, lean_object* v_rhs_2767_, lean_object* v_heq_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
uint8_t v_heq_boxed_2780_; lean_object* v_res_2781_; 
v_heq_boxed_2780_ = lean_unbox(v_heq_2768_);
v_res_2781_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_lhs_2766_, v_rhs_2767_, v_heq_boxed_2780_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrProof___boxed(lean_object* v_lhs_2782_, lean_object* v_rhs_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lean_Meta_Grind_mkEqCongrProof(v_lhs_2782_, v_rhs_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___boxed(lean_object* v_lhs_2796_, lean_object* v_rhs_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(v_lhs_2796_, v_rhs_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
lean_dec(v_a_2807_);
lean_dec_ref(v_a_2806_);
lean_dec(v_a_2805_);
lean_dec_ref(v_a_2804_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
lean_dec(v_a_2801_);
lean_dec_ref(v_a_2800_);
lean_dec(v_a_2799_);
lean_dec(v_a_2798_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___boxed(lean_object* v_lhs_2810_, lean_object* v_rhs_2811_, lean_object* v_heq_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_){
_start:
{
uint8_t v_heq_boxed_2824_; lean_object* v_res_2825_; 
v_heq_boxed_2824_ = lean_unbox(v_heq_2812_);
v_res_2825_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(v_lhs_2810_, v_rhs_2811_, v_heq_boxed_2824_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
lean_dec(v_a_2814_);
lean_dec(v_a_2813_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(lean_object* v_00_u03b1_2826_, lean_object* v_ref_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_2827_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___boxed(lean_object* v_00_u03b1_2840_, lean_object* v_ref_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(v_00_u03b1_2840_, v_ref_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2842_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(lean_object* v_00_u03b1_2854_, lean_object* v_name_2855_, uint8_t v_bi_2856_, lean_object* v_type_2857_, lean_object* v_k_2858_, uint8_t v_kind_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_2855_, v_bi_2856_, v_type_2857_, v_k_2858_, v_kind_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___boxed(lean_object** _args){
lean_object* v_00_u03b1_2872_ = _args[0];
lean_object* v_name_2873_ = _args[1];
lean_object* v_bi_2874_ = _args[2];
lean_object* v_type_2875_ = _args[3];
lean_object* v_k_2876_ = _args[4];
lean_object* v_kind_2877_ = _args[5];
lean_object* v___y_2878_ = _args[6];
lean_object* v___y_2879_ = _args[7];
lean_object* v___y_2880_ = _args[8];
lean_object* v___y_2881_ = _args[9];
lean_object* v___y_2882_ = _args[10];
lean_object* v___y_2883_ = _args[11];
lean_object* v___y_2884_ = _args[12];
lean_object* v___y_2885_ = _args[13];
lean_object* v___y_2886_ = _args[14];
lean_object* v___y_2887_ = _args[15];
lean_object* v___y_2888_ = _args[16];
_start:
{
uint8_t v_bi_boxed_2889_; uint8_t v_kind_boxed_2890_; lean_object* v_res_2891_; 
v_bi_boxed_2889_ = lean_unbox(v_bi_2874_);
v_kind_boxed_2890_ = lean_unbox(v_kind_2877_);
v_res_2891_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(v_00_u03b1_2872_, v_name_2873_, v_bi_boxed_2889_, v_type_2875_, v_k_2876_, v_kind_boxed_2890_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec(v___y_2878_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(lean_object* v_00_u03b1_2892_, lean_object* v_name_2893_, lean_object* v_type_2894_, lean_object* v_k_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v___x_2907_; 
v___x_2907_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_name_2893_, v_type_2894_, v_k_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___boxed(lean_object* v_00_u03b1_2908_, lean_object* v_name_2909_, lean_object* v_type_2910_, lean_object* v_k_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(v_00_u03b1_2908_, v_name_2909_, v_type_2910_, v_k_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec(v___y_2912_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(lean_object* v_00_u03b1_2924_, lean_object* v_msg_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v___x_2937_; 
v___x_2937_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v_msg_2925_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___boxed(lean_object* v_00_u03b1_2938_, lean_object* v_msg_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(v_00_u03b1_2938_, v_msg_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec(v___y_2940_);
return v_res_2951_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__1(void){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__0));
v___x_2954_ = l_Lean_stringToMessageData(v___x_2953_);
return v___x_2954_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__3(void){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__2));
v___x_2957_ = l_Lean_stringToMessageData(v___x_2956_);
return v___x_2957_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__5(void){
_start:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2959_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__4));
v___x_2960_ = l_Lean_stringToMessageData(v___x_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* lean_grind_mk_eq_proof(lean_object* v_a_2961_, lean_object* v_b_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___x_2987_; 
lean_inc_ref(v_b_2962_);
lean_inc_ref(v_a_2961_);
v___x_2987_ = l_Lean_Meta_Grind_hasSameType(v_a_2961_, v_b_2962_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; uint8_t v___x_2989_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc(v_a_2988_);
lean_dec_ref_known(v___x_2987_, 1);
v___x_2989_ = lean_unbox(v_a_2988_);
lean_dec(v_a_2988_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; 
lean_dec(v_a_2968_);
lean_dec_ref(v_a_2967_);
lean_dec(v_a_2966_);
lean_dec_ref(v_a_2965_);
lean_dec(v_a_2964_);
lean_dec(v_a_2963_);
lean_inc(v_a_2972_);
lean_inc_ref(v_a_2971_);
lean_inc(v_a_2970_);
lean_inc_ref(v_a_2969_);
lean_inc_ref(v_a_2961_);
v___x_2990_ = lean_infer_type(v_a_2961_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2992_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref_known(v___x_2990_, 1);
lean_inc(v_a_2972_);
lean_inc_ref(v_a_2971_);
lean_inc(v_a_2970_);
lean_inc_ref(v_a_2969_);
lean_inc_ref(v_b_2962_);
v___x_2992_ = lean_infer_type(v_b_2962_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_a_2993_);
lean_dec_ref_known(v___x_2992_, 1);
v___x_2994_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__1, &l_Lean_Meta_Grind_mkEqProofImpl___closed__1_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__1);
v___x_2995_ = l_Lean_indentExpr(v_a_2961_);
v___x_2996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2994_);
lean_ctor_set(v___x_2996_, 1, v___x_2995_);
v___x_2997_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__3, &l_Lean_Meta_Grind_mkEqProofImpl___closed__3_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__3);
v___x_2998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2996_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
v___x_2999_ = l_Lean_indentExpr(v_a_2991_);
v___x_3000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2998_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
v___x_3001_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__5, &l_Lean_Meta_Grind_mkEqProofImpl___closed__5_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__5);
v___x_3002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3000_);
lean_ctor_set(v___x_3002_, 1, v___x_3001_);
v___x_3003_ = l_Lean_indentExpr(v_b_2962_);
v___x_3004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3002_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
v___x_3005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
lean_ctor_set(v___x_3005_, 1, v___x_2997_);
v___x_3006_ = l_Lean_indentExpr(v_a_2993_);
v___x_3007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3005_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
v___x_3008_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v___x_3007_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
lean_dec(v_a_2972_);
lean_dec_ref(v_a_2971_);
lean_dec(v_a_2970_);
lean_dec_ref(v_a_2969_);
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_3008_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_3008_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
else
{
lean_dec(v_a_2991_);
lean_dec(v_a_2972_);
lean_dec_ref(v_a_2971_);
lean_dec(v_a_2970_);
lean_dec_ref(v_a_2969_);
lean_dec_ref(v_b_2962_);
lean_dec_ref(v_a_2961_);
return v___x_2992_;
}
}
else
{
lean_dec(v_a_2972_);
lean_dec_ref(v_a_2971_);
lean_dec(v_a_2970_);
lean_dec_ref(v_a_2969_);
lean_dec_ref(v_b_2962_);
lean_dec_ref(v_a_2961_);
return v___x_2990_;
}
}
else
{
v___y_2975_ = v_a_2963_;
v___y_2976_ = v_a_2964_;
v___y_2977_ = v_a_2965_;
v___y_2978_ = v_a_2966_;
v___y_2979_ = v_a_2967_;
v___y_2980_ = v_a_2968_;
v___y_2981_ = v_a_2969_;
v___y_2982_ = v_a_2970_;
v___y_2983_ = v_a_2971_;
v___y_2984_ = v_a_2972_;
goto v___jp_2974_;
}
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
lean_dec(v_a_2972_);
lean_dec_ref(v_a_2971_);
lean_dec(v_a_2970_);
lean_dec_ref(v_a_2969_);
lean_dec(v_a_2968_);
lean_dec_ref(v_a_2967_);
lean_dec(v_a_2966_);
lean_dec_ref(v_a_2965_);
lean_dec(v_a_2964_);
lean_dec(v_a_2963_);
lean_dec_ref(v_b_2962_);
lean_dec_ref(v_a_2961_);
v_a_3017_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_2987_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_2987_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
v___jp_2974_:
{
uint8_t v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = 0;
v___x_2986_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_2961_, v_b_2962_, v___x_2985_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec(v___y_2976_);
lean_dec(v___y_2975_);
return v___x_2986_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqProofImpl___boxed(lean_object* v_a_3025_, lean_object* v_b_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = lean_grind_mk_eq_proof(v_a_3025_, v_b_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* lean_grind_mk_heq_proof(lean_object* v_a_3039_, lean_object* v_b_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_){
_start:
{
uint8_t v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = 1;
v___x_3053_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_3039_, v_b_3040_, v___x_3052_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
lean_dec(v_a_3044_);
lean_dec_ref(v_a_3043_);
lean_dec(v_a_3042_);
lean_dec(v_a_3041_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHEqProofImpl___boxed(lean_object* v_a_3054_, lean_object* v_b_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = lean_grind_mk_heq_proof(v_a_3054_, v_b_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
return v_res_3067_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Proof(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
