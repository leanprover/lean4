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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
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
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Meta.Tactic.Grind.Proof.0.Lean.Meta.Grind.mkCongrProof"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "assertion violation: rhs.getAppNumArgs == numArgs\n      "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6;
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "nestedDecidable"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7_value),LEAN_SCALAR_PTR_LITERAL(65, 76, 105, 85, 179, 183, 200, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "nestedDecidable_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(215, 141, 232, 33, 101, 236, 126, 130)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "nestedProof"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9_value),LEAN_SCALAR_PTR_LITERAL(182, 140, 29, 19, 223, 104, 218, 25)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_50_; uint8_t v___x_75_; 
v___x_75_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_47_, v_b_48_);
if (v___x_75_ == 0)
{
uint8_t v___x_76_; 
v___x_76_ = l_Lean_Expr_isApp(v_a_47_);
if (v___x_76_ == 0)
{
v___y_50_ = v___x_76_;
goto v___jp_49_;
}
else
{
uint8_t v___x_77_; 
v___x_77_ = l_Lean_Expr_isApp(v_b_48_);
v___y_50_ = v___x_77_;
goto v___jp_49_;
}
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_79_, 0, v_a_47_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
return v___x_80_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix___boxed(lean_object* v_a_81_, lean_object* v_b_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(v_a_81_, v_b_82_);
lean_dec_ref(v_b_82_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(lean_object* v_h_84_, uint8_t v_flipped_85_, uint8_t v_heq_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_h_x27_93_; lean_object* v___y_94_; lean_object* v___y_95_; lean_object* v___y_96_; lean_object* v___y_97_; 
if (v_heq_86_ == 0)
{
v_h_x27_93_ = v_h_84_;
v___y_94_ = v_a_87_;
v___y_95_ = v_a_88_;
v___y_96_ = v_a_89_;
v___y_97_ = v_a_90_;
goto v___jp_92_;
}
else
{
lean_object* v___x_101_; 
lean_inc_ref(v_h_84_);
v___x_101_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof(v_h_84_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; uint8_t v___x_103_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_a_102_);
lean_dec_ref_known(v___x_101_, 1);
v___x_103_ = lean_unbox(v_a_102_);
lean_dec(v_a_102_);
if (v___x_103_ == 0)
{
v_h_x27_93_ = v_h_84_;
v___y_94_ = v_a_87_;
v___y_95_ = v_a_88_;
v___y_96_ = v_a_89_;
v___y_97_ = v_a_90_;
goto v___jp_92_;
}
else
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_Meta_mkHEqOfEq(v_h_84_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
lean_dec_ref_known(v___x_104_, 1);
v_h_x27_93_ = v_a_105_;
v___y_94_ = v_a_87_;
v___y_95_ = v_a_88_;
v___y_96_ = v_a_89_;
v___y_97_ = v_a_90_;
goto v___jp_92_;
}
else
{
return v___x_104_;
}
}
}
else
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
lean_dec_ref(v_h_84_);
v_a_106_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___x_101_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_101_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
v___jp_92_:
{
if (v_flipped_85_ == 0)
{
lean_object* v___x_98_; 
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v_h_x27_93_);
return v___x_98_;
}
else
{
if (v_heq_86_ == 0)
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_Meta_mkEqSymm(v_h_x27_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
return v___x_99_;
}
else
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_Meta_mkHEqSymm(v_h_x27_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
return v___x_100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof___boxed(lean_object* v_h_114_, lean_object* v_flipped_115_, lean_object* v_heq_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
uint8_t v_flipped_boxed_122_; uint8_t v_heq_boxed_123_; lean_object* v_res_124_; 
v_flipped_boxed_122_ = lean_unbox(v_flipped_115_);
v_heq_boxed_123_ = lean_unbox(v_heq_116_);
v_res_124_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(v_h_114_, v_flipped_boxed_122_, v_heq_boxed_123_, v_a_117_, v_a_118_, v_a_119_, v_a_120_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(lean_object* v_a_125_, uint8_t v_heq_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
if (v_heq_126_ == 0)
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_Meta_mkEqRefl(v_a_125_, v_a_127_, v_a_128_, v_a_129_, v_a_130_);
return v___x_132_;
}
else
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Meta_mkHEqRefl(v_a_125_, v_a_127_, v_a_128_, v_a_129_, v_a_130_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl___boxed(lean_object* v_a_134_, lean_object* v_heq_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
uint8_t v_heq_boxed_141_; lean_object* v_res_142_; 
v_heq_boxed_141_ = lean_unbox(v_heq_135_);
v_res_142_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(v_a_134_, v_heq_boxed_141_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans(lean_object* v_h_u2081_143_, lean_object* v_h_u2082_144_, uint8_t v_heq_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
if (v_heq_145_ == 0)
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Meta_mkEqTrans(v_h_u2081_143_, v_h_u2082_144_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
return v___x_151_;
}
else
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_Meta_mkHEqTrans(v_h_u2081_143_, v_h_u2082_144_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans___boxed(lean_object* v_h_u2081_153_, lean_object* v_h_u2082_154_, lean_object* v_heq_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
uint8_t v_heq_boxed_161_; lean_object* v_res_162_; 
v_heq_boxed_161_ = lean_unbox(v_heq_155_);
v_res_162_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans(v_h_u2081_153_, v_h_u2082_154_, v_heq_boxed_161_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(lean_object* v_h_u2081_163_, lean_object* v_h_u2082_164_, uint8_t v_heq_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
if (lean_obj_tag(v_h_u2081_163_) == 1)
{
lean_object* v_val_171_; lean_object* v___x_172_; 
v_val_171_ = lean_ctor_get(v_h_u2081_163_, 0);
lean_inc(v_val_171_);
lean_dec_ref_known(v_h_u2081_163_, 1);
v___x_172_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans(v_val_171_, v_h_u2082_164_, v_heq_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_);
return v___x_172_;
}
else
{
lean_object* v___x_173_; 
lean_dec(v_h_u2081_163_);
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v_h_u2082_164_);
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27___boxed(lean_object* v_h_u2081_174_, lean_object* v_h_u2082_175_, lean_object* v_heq_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
uint8_t v_heq_boxed_182_; lean_object* v_res_183_; 
v_heq_boxed_182_ = lean_unbox(v_heq_176_);
v_res_183_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_h_u2081_174_, v_h_u2082_175_, v_heq_boxed_182_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(lean_object* v_h_184_, uint8_t v_heq_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
if (v_heq_185_ == 0)
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Meta_mkEqOfHEq(v_h_184_, v_heq_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_);
return v___x_191_;
}
else
{
lean_object* v___x_192_; 
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v_h_184_);
return v___x_192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded___boxed(lean_object* v_h_193_, lean_object* v_heq_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
uint8_t v_heq_boxed_200_; lean_object* v_res_201_; 
v_heq_boxed_200_ = lean_unbox(v_heq_194_);
v_res_201_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_h_193_, v_heq_boxed_200_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
return v_res_201_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0(void){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3(lean_object* v_msg_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_12097__overap_216_; lean_object* v___x_217_; 
v___x_215_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0);
v___x_12097__overap_216_ = lean_panic_fn_borrowed(v___x_215_, v_msg_203_);
lean_inc(v___y_213_);
lean_inc_ref(v___y_212_);
lean_inc(v___y_211_);
lean_inc_ref(v___y_210_);
lean_inc(v___y_209_);
lean_inc_ref(v___y_208_);
lean_inc(v___y_207_);
lean_inc_ref(v___y_206_);
lean_inc(v___y_205_);
lean_inc(v___y_204_);
v___x_217_ = lean_apply_11(v___x_12097__overap_216_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, lean_box(0));
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___boxed(lean_object* v_msg_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3(v_msg_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec(v___y_219_);
return v_res_230_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0(void){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(lean_object* v_msg_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_12895__overap_245_; lean_object* v___x_246_; 
v___x_244_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0);
v___x_12895__overap_245_ = lean_panic_fn_borrowed(v___x_244_, v_msg_232_);
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
v___x_246_ = lean_apply_11(v___x_12895__overap_245_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, lean_box(0));
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
lean_object* v___x_297_; lean_object* v_snd_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_345_; 
v___x_297_ = lean_st_ref_get(v___y_286_);
v_snd_298_ = lean_ctor_get(v_a_285_, 1);
v_isSharedCheck_345_ = !lean_is_exclusive(v_a_285_);
if (v_isSharedCheck_345_ == 0)
{
lean_object* v_unused_346_; 
v_unused_346_ = lean_ctor_get(v_a_285_, 0);
lean_dec(v_unused_346_);
v___x_300_ = v_a_285_;
v_isShared_301_ = v_isSharedCheck_345_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_snd_298_);
lean_dec(v_a_285_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_345_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; 
lean_inc(v_snd_298_);
v___x_302_ = l_Lean_Meta_Grind_Goal_getENode(v___x_297_, v_snd_298_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___x_297_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_336_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_336_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_336_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_336_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v_target_x3f_307_; lean_object* v_idx_308_; lean_object* v___x_309_; 
v_target_x3f_307_ = lean_ctor_get(v_a_303_, 4);
lean_inc(v_target_x3f_307_);
v_idx_308_ = lean_ctor_get(v_a_303_, 7);
lean_inc(v_idx_308_);
lean_dec(v_a_303_);
v___x_309_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(v___x_284_, v_idx_308_);
lean_dec(v_idx_308_);
if (lean_obj_tag(v___x_309_) == 1)
{
lean_object* v___x_311_; 
lean_dec(v_target_x3f_307_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v___x_309_);
v___x_311_ = v___x_300_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_snd_298_);
v___x_311_ = v_reuseFailAlloc_315_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_313_; 
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_311_);
v___x_313_ = v___x_305_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
else
{
lean_object* v___x_316_; 
lean_dec(v___x_309_);
lean_del_object(v___x_305_);
v___x_316_ = lean_box(0);
if (lean_obj_tag(v_target_x3f_307_) == 1)
{
lean_object* v_val_317_; lean_object* v___x_319_; 
lean_dec(v_snd_298_);
v_val_317_ = lean_ctor_get(v_target_x3f_307_, 0);
lean_inc(v_val_317_);
lean_dec_ref_known(v_target_x3f_307_, 1);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v_val_317_);
lean_ctor_set(v___x_300_, 0, v___x_316_);
v___x_319_ = v___x_300_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_316_);
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
lean_dec(v_target_x3f_307_);
v___x_322_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3);
v___x_323_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3(v___x_322_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v___x_325_; 
lean_dec_ref_known(v___x_323_, 1);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v___x_316_);
v___x_325_ = v___x_300_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_316_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_snd_298_);
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
lean_del_object(v___x_300_);
lean_dec(v_snd_298_);
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
lean_del_object(v___x_300_);
lean_dec(v_snd_298_);
v_a_337_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_302_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_302_);
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
lean_object* v___x_659_; lean_object* v_fst_660_; lean_object* v_snd_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_694_; 
v___x_659_ = lean_st_ref_get(v___y_653_);
v_fst_660_ = lean_ctor_get(v_a_652_, 0);
v_snd_661_ = lean_ctor_get(v_a_652_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_a_652_);
if (v_isSharedCheck_694_ == 0)
{
v___x_663_ = v_a_652_;
v_isShared_664_ = v_isSharedCheck_694_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_snd_661_);
lean_inc(v_fst_660_);
lean_dec(v_a_652_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_694_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; 
lean_inc(v_snd_661_);
v___x_665_ = l_Lean_Meta_Grind_Goal_getENode(v___x_659_, v_snd_661_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec(v___x_659_);
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
v___x_673_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_idx_672_, v_self_670_, v_fst_660_);
if (lean_obj_tag(v_target_x3f_671_) == 1)
{
lean_object* v_val_674_; lean_object* v___x_676_; 
lean_del_object(v___x_668_);
lean_dec(v_snd_661_);
v_val_674_ = lean_ctor_get(v_target_x3f_671_, 0);
lean_inc(v_val_674_);
lean_dec_ref_known(v_target_x3f_671_, 1);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v_val_674_);
lean_ctor_set(v___x_663_, 0, v___x_673_);
v___x_676_ = v___x_663_;
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
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_673_);
v___x_680_ = v___x_663_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_snd_661_);
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
lean_del_object(v___x_663_);
lean_dec(v_snd_661_);
lean_dec(v_fst_660_);
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
lean_object* v_a_u2081_870_; lean_object* v_a_u2082_871_; lean_object* v___x_872_; lean_object* v_i_873_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; uint8_t v___x_888_; 
v_a_u2081_870_ = l_Lean_Expr_appArg_x21(v_lhs_852_);
v_a_u2082_871_ = l_Lean_Expr_appArg_x21(v_rhs_853_);
v___x_872_ = lean_unsigned_to_nat(1u);
v_i_873_ = lean_nat_sub(v_i_854_, v___x_872_);
lean_dec(v_i_854_);
v___x_888_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_u2081_870_, v_a_u2082_871_);
lean_dec_ref(v_a_u2082_871_);
lean_dec_ref(v_a_u2081_870_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_889_ = lean_array_get_size(v_info_851_);
v___x_890_ = lean_nat_dec_lt(v_i_873_, v___x_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; lean_object* v___x_892_; 
lean_dec(v_i_873_);
lean_dec_ref(v_rhs_853_);
lean_dec_ref(v_lhs_852_);
v___x_891_ = lean_box(v___x_888_);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
else
{
lean_object* v___x_893_; uint8_t v_hasFwdDeps_894_; 
v___x_893_ = lean_array_fget_borrowed(v_info_851_, v_i_873_);
v_hasFwdDeps_894_ = lean_ctor_get_uint8(v___x_893_, sizeof(void*)*1 + 1);
if (v_hasFwdDeps_894_ == 0)
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
lean_object* v___x_895_; lean_object* v___x_896_; 
lean_dec(v_i_873_);
lean_dec_ref(v_rhs_853_);
lean_dec_ref(v_lhs_852_);
v___x_895_ = lean_box(v___x_888_);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop___boxed(lean_object* v_info_897_, lean_object* v_lhs_898_, lean_object* v_rhs_899_, lean_object* v_i_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(v_info_897_, v_lhs_898_, v_rhs_899_, v_i_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec(v_a_901_);
lean_dec_ref(v_info_897_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(lean_object* v_lhs_913_, lean_object* v_rhs_914_, lean_object* v_f_915_, lean_object* v_g_916_, lean_object* v_numArgs_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
uint8_t v___x_929_; 
v___x_929_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_f_915_, v_g_916_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; 
lean_dec(v_numArgs_917_);
lean_dec_ref(v_f_915_);
lean_dec_ref(v_rhs_914_);
lean_dec_ref(v_lhs_913_);
v___x_930_ = lean_box(v___x_929_);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = lean_box(0);
v___x_933_ = l_Lean_Meta_getFunInfo(v_f_915_, v___x_932_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v_paramInfo_935_; lean_object* v___x_936_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref_known(v___x_933_, 1);
v_paramInfo_935_ = lean_ctor_get(v_a_934_, 0);
lean_inc_ref(v_paramInfo_935_);
lean_dec(v_a_934_);
v___x_936_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(v_paramInfo_935_, v_lhs_913_, v_rhs_914_, v_numArgs_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
lean_dec_ref(v_paramInfo_935_);
return v___x_936_;
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec(v_numArgs_917_);
lean_dec_ref(v_rhs_914_);
lean_dec_ref(v_lhs_913_);
v_a_937_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_933_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_933_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget___boxed(lean_object* v_lhs_945_, lean_object* v_rhs_946_, lean_object* v_f_947_, lean_object* v_g_948_, lean_object* v_numArgs_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(v_lhs_945_, v_rhs_946_, v_f_947_, v_g_948_, v_numArgs_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_g_948_);
return v_res_961_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0(void){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(lean_object* v_msg_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; lean_object* v___x_125372__overap_976_; lean_object* v___x_977_; 
v___x_975_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0);
v___x_125372__overap_976_ = lean_panic_fn_borrowed(v___x_975_, v_msg_963_);
lean_inc(v___y_973_);
lean_inc_ref(v___y_972_);
lean_inc(v___y_971_);
lean_inc_ref(v___y_970_);
lean_inc(v___y_969_);
lean_inc_ref(v___y_968_);
lean_inc(v___y_967_);
lean_inc_ref(v___y_966_);
lean_inc(v___y_965_);
lean_inc(v___y_964_);
v___x_977_ = lean_apply_11(v___x_125372__overap_976_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, lean_box(0));
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___boxed(lean_object* v_msg_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v_msg_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec(v___y_979_);
return v_res_990_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = l_Lean_maxRecDepthErrorMessage;
v___x_997_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
return v___x_997_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3);
v___x_999_ = l_Lean_MessageData_ofFormat(v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4);
v___x_1001_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__2));
v___x_1002_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v___x_1000_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(lean_object* v_ref_1003_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5);
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v_ref_1003_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___boxed(lean_object* v_ref_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1008_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0(lean_object* v_k_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v_b_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; 
lean_inc(v___y_1022_);
lean_inc_ref(v___y_1021_);
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
lean_inc(v___y_1015_);
lean_inc_ref(v___y_1014_);
lean_inc(v___y_1013_);
lean_inc(v___y_1012_);
v___x_1024_ = lean_apply_12(v_k_1011_, v_b_1018_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, lean_box(0));
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0___boxed(lean_object* v_k_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v_b_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0(v_k_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v_b_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec(v___y_1026_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(lean_object* v_name_1039_, uint8_t v_bi_1040_, lean_object* v_type_1041_, lean_object* v_k_1042_, uint8_t v_kind_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v___f_1055_; lean_object* v___x_1056_; 
lean_inc(v___y_1049_);
lean_inc_ref(v___y_1048_);
lean_inc(v___y_1047_);
lean_inc_ref(v___y_1046_);
lean_inc(v___y_1045_);
lean_inc(v___y_1044_);
v___f_1055_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_1055_, 0, v_k_1042_);
lean_closure_set(v___f_1055_, 1, v___y_1044_);
lean_closure_set(v___f_1055_, 2, v___y_1045_);
lean_closure_set(v___f_1055_, 3, v___y_1046_);
lean_closure_set(v___f_1055_, 4, v___y_1047_);
lean_closure_set(v___f_1055_, 5, v___y_1048_);
lean_closure_set(v___f_1055_, 6, v___y_1049_);
v___x_1056_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1039_, v_bi_1040_, v_type_1041_, v___f_1055_, v_kind_1043_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
if (lean_obj_tag(v___x_1056_) == 0)
{
return v___x_1056_;
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1056_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___boxed(lean_object* v_name_1065_, lean_object* v_bi_1066_, lean_object* v_type_1067_, lean_object* v_k_1068_, lean_object* v_kind_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
uint8_t v_bi_boxed_1081_; uint8_t v_kind_boxed_1082_; lean_object* v_res_1083_; 
v_bi_boxed_1081_ = lean_unbox(v_bi_1066_);
v_kind_boxed_1082_ = lean_unbox(v_kind_1069_);
v_res_1083_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_1065_, v_bi_boxed_1081_, v_type_1067_, v_k_1068_, v_kind_boxed_1082_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec(v___y_1070_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(lean_object* v_name_1084_, lean_object* v_type_1085_, lean_object* v_k_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
uint8_t v___x_1098_; uint8_t v___x_1099_; lean_object* v___x_1100_; 
v___x_1098_ = 0;
v___x_1099_ = 0;
v___x_1100_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_1084_, v___x_1098_, v_type_1085_, v_k_1086_, v___x_1099_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg___boxed(lean_object* v_name_1101_, lean_object* v_type_1102_, lean_object* v_k_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_name_1101_, v_type_1102_, v_k_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec(v___y_1104_);
return v_res_1115_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1116_; lean_object* v_dummy_1117_; 
v___x_1116_ = lean_box(0);
v_dummy_1117_ = l_Lean_Expr_sort___override(v___x_1116_);
return v_dummy_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0(lean_object* v_numArgs_1118_, lean_object* v_rhs_1119_, lean_object* v_lhs_1120_, uint8_t v___x_1121_, uint8_t v___x_1122_, lean_object* v_x_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_dummy_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_dummy_1135_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0);
lean_inc(v_numArgs_1118_);
v___x_1136_ = lean_mk_array(v_numArgs_1118_, v_dummy_1135_);
v___x_1137_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_numArgs_1118_, v_rhs_1119_, v___x_1136_);
lean_inc_ref(v_x_1123_);
v___x_1138_ = l_Lean_mkAppN(v_x_1123_, v___x_1137_);
lean_dec_ref(v___x_1137_);
v___x_1139_ = l_Lean_Meta_mkHEq(v_lhs_1120_, v___x_1138_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1139_, 1);
v___x_1141_ = lean_unsigned_to_nat(1u);
v___x_1142_ = lean_mk_empty_array_with_capacity(v___x_1141_);
v___x_1143_ = lean_array_push(v___x_1142_, v_x_1123_);
v___x_1144_ = 1;
v___x_1145_ = l_Lean_Meta_mkLambdaFVars(v___x_1143_, v_a_1140_, v___x_1121_, v___x_1122_, v___x_1121_, v___x_1122_, v___x_1144_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec_ref(v___x_1143_);
return v___x_1145_;
}
else
{
lean_dec_ref(v_x_1123_);
return v___x_1139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___boxed(lean_object** _args){
lean_object* v_numArgs_1146_ = _args[0];
lean_object* v_rhs_1147_ = _args[1];
lean_object* v_lhs_1148_ = _args[2];
lean_object* v___x_1149_ = _args[3];
lean_object* v___x_1150_ = _args[4];
lean_object* v_x_1151_ = _args[5];
lean_object* v___y_1152_ = _args[6];
lean_object* v___y_1153_ = _args[7];
lean_object* v___y_1154_ = _args[8];
lean_object* v___y_1155_ = _args[9];
lean_object* v___y_1156_ = _args[10];
lean_object* v___y_1157_ = _args[11];
lean_object* v___y_1158_ = _args[12];
lean_object* v___y_1159_ = _args[13];
lean_object* v___y_1160_ = _args[14];
lean_object* v___y_1161_ = _args[15];
lean_object* v___y_1162_ = _args[16];
_start:
{
uint8_t v___x_133262__boxed_1163_; uint8_t v___x_133263__boxed_1164_; lean_object* v_res_1165_; 
v___x_133262__boxed_1163_ = lean_unbox(v___x_1149_);
v___x_133263__boxed_1164_ = lean_unbox(v___x_1150_);
v_res_1165_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0(v_numArgs_1146_, v_rhs_1147_, v_lhs_1148_, v___x_133262__boxed_1163_, v___x_133263__boxed_1164_, v_x_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec(v___y_1152_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_spec__13(lean_object* v_msg_1166_){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = l_Lean_instInhabitedExpr;
v___x_1168_ = lean_panic_fn_borrowed(v___x_1167_, v_msg_1166_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(lean_object* v_msgData_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; lean_object* v_env_1176_; lean_object* v___x_1177_; lean_object* v_mctx_1178_; lean_object* v_lctx_1179_; lean_object* v_options_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1175_ = lean_st_ref_get(v___y_1173_);
v_env_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc_ref(v_env_1176_);
lean_dec(v___x_1175_);
v___x_1177_ = lean_st_ref_get(v___y_1171_);
v_mctx_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc_ref(v_mctx_1178_);
lean_dec(v___x_1177_);
v_lctx_1179_ = lean_ctor_get(v___y_1170_, 2);
v_options_1180_ = lean_ctor_get(v___y_1172_, 2);
lean_inc_ref(v_options_1180_);
lean_inc_ref(v_lctx_1179_);
v___x_1181_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1181_, 0, v_env_1176_);
lean_ctor_set(v___x_1181_, 1, v_mctx_1178_);
lean_ctor_set(v___x_1181_, 2, v_lctx_1179_);
lean_ctor_set(v___x_1181_, 3, v_options_1180_);
v___x_1182_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
lean_ctor_set(v___x_1182_, 1, v_msgData_1169_);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16___boxed(lean_object* v_msgData_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(v_msgData_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(lean_object* v_msg_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_ref_1197_; lean_object* v___x_1198_; lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1207_; 
v_ref_1197_ = lean_ctor_get(v___y_1194_, 5);
v___x_1198_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(v_msg_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1207_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1207_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
lean_inc(v_ref_1197_);
v___x_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1203_, 0, v_ref_1197_);
lean_ctor_set(v___x_1203_, 1, v_a_1199_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set_tag(v___x_1201_, 1);
lean_ctor_set(v___x_1201_, 0, v___x_1203_);
v___x_1205_ = v___x_1201_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg___boxed(lean_object* v_msg_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v_msg_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
return v_res_1214_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__0));
v___x_1217_ = l_Lean_stringToMessageData(v___x_1216_);
return v___x_1217_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__2));
v___x_1220_ = l_Lean_stringToMessageData(v___x_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(lean_object* v_lhs_1221_, lean_object* v_rhs_1222_, lean_object* v_00_u03b1_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1235_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1);
v___x_1236_ = l_Lean_indentExpr(v_lhs_1221_);
v___x_1237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3);
v___x_1239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = l_Lean_indentExpr(v_rhs_1222_);
v___x_1241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v___x_1241_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___boxed(lean_object* v_lhs_1243_, lean_object* v_rhs_1244_, lean_object* v_00_u03b1_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1243_, v_rhs_1244_, v_00_u03b1_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec(v___y_1246_);
return v_res_1257_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__1));
v___x_1261_ = lean_unsigned_to_nat(4u);
v___x_1262_ = lean_unsigned_to_nat(198u);
v___x_1263_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__0));
v___x_1264_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1265_ = l_mkPanicMessageWithDecl(v___x_1264_, v___x_1263_, v___x_1262_, v___x_1261_, v___x_1260_);
return v___x_1265_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1268_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__1));
v___x_1269_ = lean_unsigned_to_nat(4u);
v___x_1270_ = lean_unsigned_to_nat(318u);
v___x_1271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0));
v___x_1272_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1273_ = l_mkPanicMessageWithDecl(v___x_1272_, v___x_1271_, v___x_1270_, v___x_1269_, v___x_1268_);
return v___x_1273_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1275_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1276_ = lean_unsigned_to_nat(36u);
v___x_1277_ = lean_unsigned_to_nat(153u);
v___x_1278_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0));
v___x_1279_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1280_ = l_mkPanicMessageWithDecl(v___x_1279_, v___x_1278_, v___x_1277_, v___x_1276_, v___x_1275_);
return v___x_1280_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1281_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1282_ = lean_unsigned_to_nat(34u);
v___x_1283_ = lean_unsigned_to_nat(154u);
v___x_1284_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0));
v___x_1285_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1286_ = l_mkPanicMessageWithDecl(v___x_1285_, v___x_1284_, v___x_1283_, v___x_1282_, v___x_1281_);
return v___x_1286_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1288_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__3));
v___x_1289_ = lean_unsigned_to_nat(4u);
v___x_1290_ = lean_unsigned_to_nat(155u);
v___x_1291_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0));
v___x_1292_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1293_ = l_mkPanicMessageWithDecl(v___x_1292_, v___x_1291_, v___x_1290_, v___x_1289_, v___x_1288_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof(lean_object* v_lhs_1306_, lean_object* v_rhs_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; uint8_t v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; uint8_t v___y_1355_; lean_object* v_fileName_1389_; lean_object* v_fileMap_1390_; lean_object* v_options_1391_; lean_object* v_currRecDepth_1392_; lean_object* v_maxRecDepth_1393_; lean_object* v_ref_1394_; lean_object* v_currNamespace_1395_; lean_object* v_openDecls_1396_; lean_object* v_initHeartbeats_1397_; lean_object* v_maxHeartbeats_1398_; lean_object* v_quotContext_1399_; lean_object* v_currMacroScope_1400_; uint8_t v_diag_1401_; lean_object* v_cancelTk_x3f_1402_; uint8_t v_suppressElabErrors_1403_; lean_object* v_inheritedTraceOptions_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v_fileName_1389_ = lean_ctor_get(v_a_1316_, 0);
v_fileMap_1390_ = lean_ctor_get(v_a_1316_, 1);
v_options_1391_ = lean_ctor_get(v_a_1316_, 2);
v_currRecDepth_1392_ = lean_ctor_get(v_a_1316_, 3);
v_maxRecDepth_1393_ = lean_ctor_get(v_a_1316_, 4);
v_ref_1394_ = lean_ctor_get(v_a_1316_, 5);
v_currNamespace_1395_ = lean_ctor_get(v_a_1316_, 6);
v_openDecls_1396_ = lean_ctor_get(v_a_1316_, 7);
v_initHeartbeats_1397_ = lean_ctor_get(v_a_1316_, 8);
v_maxHeartbeats_1398_ = lean_ctor_get(v_a_1316_, 9);
v_quotContext_1399_ = lean_ctor_get(v_a_1316_, 10);
v_currMacroScope_1400_ = lean_ctor_get(v_a_1316_, 11);
v_diag_1401_ = lean_ctor_get_uint8(v_a_1316_, sizeof(void*)*14);
v_cancelTk_x3f_1402_ = lean_ctor_get(v_a_1316_, 12);
v_suppressElabErrors_1403_ = lean_ctor_get_uint8(v_a_1316_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1404_ = lean_ctor_get(v_a_1316_, 13);
v___x_1405_ = l_Lean_Expr_cleanupAnnotations(v_lhs_1306_);
v___x_1406_ = l_Lean_Expr_isApp(v___x_1405_);
v___x_1436_ = lean_unsigned_to_nat(0u);
v___x_1437_ = lean_nat_dec_eq(v_maxRecDepth_1393_, v___x_1436_);
if (v___x_1437_ == 0)
{
uint8_t v___x_1438_; 
v___x_1438_ = lean_nat_dec_eq(v_currRecDepth_1392_, v_maxRecDepth_1393_);
if (v___x_1438_ == 0)
{
goto v___jp_1407_;
}
else
{
lean_object* v___x_1439_; 
lean_dec_ref(v___x_1405_);
lean_dec_ref(v_rhs_1307_);
lean_inc(v_ref_1394_);
v___x_1439_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1394_);
return v___x_1439_;
}
}
else
{
goto v___jp_1407_;
}
v___jp_1319_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1);
v___x_1331_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1330_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec_ref(v___y_1328_);
return v___x_1331_;
}
v___jp_1332_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2);
v___x_1344_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1343_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec_ref(v___y_1341_);
return v___x_1344_;
}
v___jp_1345_:
{
if (v___y_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec_ref(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec_ref(v___y_1346_);
v___x_1356_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4);
v___x_1357_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1356_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v___y_1350_, v_a_1317_);
lean_dec_ref(v___y_1350_);
return v___x_1357_;
}
else
{
lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1358_ = l_Lean_Expr_constLevels_x21(v___y_1353_);
lean_dec_ref(v___y_1353_);
v___x_1359_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___y_1349_, v___y_1348_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; 
lean_inc_ref(v___y_1347_);
lean_inc_ref(v___y_1352_);
v___x_1360_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1352_, v___y_1347_, v___y_1351_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v___y_1350_, v_a_1317_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1362_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref_known(v___x_1360_, 1);
lean_inc_ref(v___y_1354_);
lean_inc_ref(v___y_1346_);
v___x_1362_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1346_, v___y_1354_, v___y_1351_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v___y_1350_, v_a_1317_);
lean_dec_ref(v___y_1350_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1373_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1365_ = v___x_1362_;
v_isShared_1366_ = v_isSharedCheck_1373_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1362_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1373_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1367_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6));
v___x_1368_ = l_Lean_mkConst(v___x_1367_, v___x_1358_);
v___x_1369_ = l_Lean_mkApp8(v___x_1368_, v___y_1349_, v___y_1348_, v___y_1352_, v___y_1346_, v___y_1354_, v___y_1347_, v_a_1361_, v_a_1363_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1369_);
v___x_1371_ = v___x_1365_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
else
{
lean_dec(v_a_1361_);
lean_dec(v___x_1358_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1352_);
lean_dec_ref(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec_ref(v___y_1346_);
return v___x_1362_;
}
}
else
{
lean_dec(v___x_1358_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1352_);
lean_dec_ref(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec_ref(v___y_1346_);
return v___x_1360_;
}
}
else
{
uint8_t v___x_1374_; lean_object* v___x_1375_; 
lean_dec_ref(v___y_1348_);
v___x_1374_ = 0;
lean_inc_ref(v___y_1347_);
lean_inc_ref(v___y_1352_);
v___x_1375_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1352_, v___y_1347_, v___x_1374_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v___y_1350_, v_a_1317_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1377_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1375_, 1);
lean_inc_ref(v___y_1354_);
lean_inc_ref(v___y_1346_);
v___x_1377_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1346_, v___y_1354_, v___x_1374_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v___y_1350_, v_a_1317_);
lean_dec_ref(v___y_1350_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1388_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1380_ = v___x_1377_;
v_isShared_1381_ = v_isSharedCheck_1388_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1377_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1388_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1382_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8));
v___x_1383_ = l_Lean_mkConst(v___x_1382_, v___x_1358_);
v___x_1384_ = l_Lean_mkApp7(v___x_1383_, v___y_1349_, v___y_1352_, v___y_1346_, v___y_1354_, v___y_1347_, v_a_1376_, v_a_1378_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1384_);
v___x_1386_ = v___x_1380_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
else
{
lean_dec(v_a_1376_);
lean_dec(v___x_1358_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1352_);
lean_dec_ref(v___y_1349_);
lean_dec_ref(v___y_1347_);
lean_dec_ref(v___y_1346_);
return v___x_1377_;
}
}
else
{
lean_dec(v___x_1358_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1352_);
lean_dec_ref(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec_ref(v___y_1347_);
lean_dec_ref(v___y_1346_);
return v___x_1375_;
}
}
}
}
v___jp_1407_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1408_ = lean_unsigned_to_nat(1u);
v___x_1409_ = lean_nat_add(v_currRecDepth_1392_, v___x_1408_);
lean_inc_ref(v_inheritedTraceOptions_1404_);
lean_inc(v_cancelTk_x3f_1402_);
lean_inc(v_currMacroScope_1400_);
lean_inc(v_quotContext_1399_);
lean_inc(v_maxHeartbeats_1398_);
lean_inc(v_initHeartbeats_1397_);
lean_inc(v_openDecls_1396_);
lean_inc(v_currNamespace_1395_);
lean_inc(v_ref_1394_);
lean_inc(v_maxRecDepth_1393_);
lean_inc_ref(v_options_1391_);
lean_inc_ref(v_fileMap_1390_);
lean_inc_ref(v_fileName_1389_);
v___x_1410_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1410_, 0, v_fileName_1389_);
lean_ctor_set(v___x_1410_, 1, v_fileMap_1390_);
lean_ctor_set(v___x_1410_, 2, v_options_1391_);
lean_ctor_set(v___x_1410_, 3, v___x_1409_);
lean_ctor_set(v___x_1410_, 4, v_maxRecDepth_1393_);
lean_ctor_set(v___x_1410_, 5, v_ref_1394_);
lean_ctor_set(v___x_1410_, 6, v_currNamespace_1395_);
lean_ctor_set(v___x_1410_, 7, v_openDecls_1396_);
lean_ctor_set(v___x_1410_, 8, v_initHeartbeats_1397_);
lean_ctor_set(v___x_1410_, 9, v_maxHeartbeats_1398_);
lean_ctor_set(v___x_1410_, 10, v_quotContext_1399_);
lean_ctor_set(v___x_1410_, 11, v_currMacroScope_1400_);
lean_ctor_set(v___x_1410_, 12, v_cancelTk_x3f_1402_);
lean_ctor_set(v___x_1410_, 13, v_inheritedTraceOptions_1404_);
lean_ctor_set_uint8(v___x_1410_, sizeof(void*)*14, v_diag_1401_);
lean_ctor_set_uint8(v___x_1410_, sizeof(void*)*14 + 1, v_suppressElabErrors_1403_);
if (v___x_1406_ == 0)
{
lean_dec_ref(v___x_1405_);
lean_dec_ref(v_rhs_1307_);
v___y_1320_ = v_a_1308_;
v___y_1321_ = v_a_1309_;
v___y_1322_ = v_a_1310_;
v___y_1323_ = v_a_1311_;
v___y_1324_ = v_a_1312_;
v___y_1325_ = v_a_1313_;
v___y_1326_ = v_a_1314_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v___x_1410_;
v___y_1329_ = v_a_1317_;
goto v___jp_1319_;
}
else
{
lean_object* v_arg_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v_arg_1411_ = lean_ctor_get(v___x_1405_, 1);
lean_inc_ref(v_arg_1411_);
v___x_1412_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1405_);
v___x_1413_ = l_Lean_Expr_isApp(v___x_1412_);
if (v___x_1413_ == 0)
{
lean_dec_ref(v___x_1412_);
lean_dec_ref(v_arg_1411_);
lean_dec_ref(v_rhs_1307_);
v___y_1320_ = v_a_1308_;
v___y_1321_ = v_a_1309_;
v___y_1322_ = v_a_1310_;
v___y_1323_ = v_a_1311_;
v___y_1324_ = v_a_1312_;
v___y_1325_ = v_a_1313_;
v___y_1326_ = v_a_1314_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v___x_1410_;
v___y_1329_ = v_a_1317_;
goto v___jp_1319_;
}
else
{
lean_object* v_arg_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; 
v_arg_1414_ = lean_ctor_get(v___x_1412_, 1);
lean_inc_ref(v_arg_1414_);
v___x_1415_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1412_);
v___x_1416_ = l_Lean_Expr_isApp(v___x_1415_);
if (v___x_1416_ == 0)
{
lean_dec_ref(v___x_1415_);
lean_dec_ref(v_arg_1414_);
lean_dec_ref(v_arg_1411_);
lean_dec_ref(v_rhs_1307_);
v___y_1320_ = v_a_1308_;
v___y_1321_ = v_a_1309_;
v___y_1322_ = v_a_1310_;
v___y_1323_ = v_a_1311_;
v___y_1324_ = v_a_1312_;
v___y_1325_ = v_a_1313_;
v___y_1326_ = v_a_1314_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v___x_1410_;
v___y_1329_ = v_a_1317_;
goto v___jp_1319_;
}
else
{
lean_object* v_arg_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; uint8_t v___x_1420_; 
v_arg_1417_ = lean_ctor_get(v___x_1415_, 1);
lean_inc_ref(v_arg_1417_);
v___x_1418_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1415_);
v___x_1419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_1420_ = l_Lean_Expr_isConstOf(v___x_1418_, v___x_1419_);
if (v___x_1420_ == 0)
{
lean_dec_ref(v___x_1418_);
lean_dec_ref(v_arg_1417_);
lean_dec_ref(v_arg_1414_);
lean_dec_ref(v_arg_1411_);
lean_dec_ref(v_rhs_1307_);
v___y_1320_ = v_a_1308_;
v___y_1321_ = v_a_1309_;
v___y_1322_ = v_a_1310_;
v___y_1323_ = v_a_1311_;
v___y_1324_ = v_a_1312_;
v___y_1325_ = v_a_1313_;
v___y_1326_ = v_a_1314_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v___x_1410_;
v___y_1329_ = v_a_1317_;
goto v___jp_1319_;
}
else
{
lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1421_ = l_Lean_Expr_cleanupAnnotations(v_rhs_1307_);
v___x_1422_ = l_Lean_Expr_isApp(v___x_1421_);
if (v___x_1422_ == 0)
{
lean_dec_ref(v___x_1421_);
lean_dec_ref(v___x_1418_);
lean_dec_ref(v_arg_1417_);
lean_dec_ref(v_arg_1414_);
lean_dec_ref(v_arg_1411_);
v___y_1333_ = v_a_1308_;
v___y_1334_ = v_a_1309_;
v___y_1335_ = v_a_1310_;
v___y_1336_ = v_a_1311_;
v___y_1337_ = v_a_1312_;
v___y_1338_ = v_a_1313_;
v___y_1339_ = v_a_1314_;
v___y_1340_ = v_a_1315_;
v___y_1341_ = v___x_1410_;
v___y_1342_ = v_a_1317_;
goto v___jp_1332_;
}
else
{
lean_object* v_arg_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v_arg_1423_ = lean_ctor_get(v___x_1421_, 1);
lean_inc_ref(v_arg_1423_);
v___x_1424_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1421_);
v___x_1425_ = l_Lean_Expr_isApp(v___x_1424_);
if (v___x_1425_ == 0)
{
lean_dec_ref(v___x_1424_);
lean_dec_ref(v_arg_1423_);
lean_dec_ref(v___x_1418_);
lean_dec_ref(v_arg_1417_);
lean_dec_ref(v_arg_1414_);
lean_dec_ref(v_arg_1411_);
v___y_1333_ = v_a_1308_;
v___y_1334_ = v_a_1309_;
v___y_1335_ = v_a_1310_;
v___y_1336_ = v_a_1311_;
v___y_1337_ = v_a_1312_;
v___y_1338_ = v_a_1313_;
v___y_1339_ = v_a_1314_;
v___y_1340_ = v_a_1315_;
v___y_1341_ = v___x_1410_;
v___y_1342_ = v_a_1317_;
goto v___jp_1332_;
}
else
{
lean_object* v_arg_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v_arg_1426_ = lean_ctor_get(v___x_1424_, 1);
lean_inc_ref(v_arg_1426_);
v___x_1427_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1424_);
v___x_1428_ = l_Lean_Expr_isApp(v___x_1427_);
if (v___x_1428_ == 0)
{
lean_dec_ref(v___x_1427_);
lean_dec_ref(v_arg_1426_);
lean_dec_ref(v_arg_1423_);
lean_dec_ref(v___x_1418_);
lean_dec_ref(v_arg_1417_);
lean_dec_ref(v_arg_1414_);
lean_dec_ref(v_arg_1411_);
v___y_1333_ = v_a_1308_;
v___y_1334_ = v_a_1309_;
v___y_1335_ = v_a_1310_;
v___y_1336_ = v_a_1311_;
v___y_1337_ = v_a_1312_;
v___y_1338_ = v_a_1313_;
v___y_1339_ = v_a_1314_;
v___y_1340_ = v_a_1315_;
v___y_1341_ = v___x_1410_;
v___y_1342_ = v_a_1317_;
goto v___jp_1332_;
}
else
{
lean_object* v_arg_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v_arg_1429_ = lean_ctor_get(v___x_1427_, 1);
lean_inc_ref(v_arg_1429_);
v___x_1430_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1427_);
v___x_1431_ = l_Lean_Expr_isConstOf(v___x_1430_, v___x_1419_);
lean_dec_ref(v___x_1430_);
if (v___x_1431_ == 0)
{
lean_dec_ref(v_arg_1429_);
lean_dec_ref(v_arg_1426_);
lean_dec_ref(v_arg_1423_);
lean_dec_ref(v___x_1418_);
lean_dec_ref(v_arg_1417_);
lean_dec_ref(v_arg_1414_);
lean_dec_ref(v_arg_1411_);
v___y_1333_ = v_a_1308_;
v___y_1334_ = v_a_1309_;
v___y_1335_ = v_a_1310_;
v___y_1336_ = v_a_1311_;
v___y_1337_ = v_a_1312_;
v___y_1338_ = v_a_1313_;
v___y_1339_ = v_a_1314_;
v___y_1340_ = v_a_1315_;
v___y_1341_ = v___x_1410_;
v___y_1342_ = v_a_1317_;
goto v___jp_1332_;
}
else
{
lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1432_ = lean_st_ref_get(v_a_1308_);
v___x_1433_ = lean_st_ref_get(v_a_1308_);
v___x_1434_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1432_, v_arg_1414_, v_arg_1423_);
lean_dec(v___x_1432_);
if (v___x_1434_ == 0)
{
lean_dec(v___x_1433_);
v___y_1346_ = v_arg_1411_;
v___y_1347_ = v_arg_1423_;
v___y_1348_ = v_arg_1429_;
v___y_1349_ = v_arg_1417_;
v___y_1350_ = v___x_1410_;
v___y_1351_ = v___x_1431_;
v___y_1352_ = v_arg_1414_;
v___y_1353_ = v___x_1418_;
v___y_1354_ = v_arg_1426_;
v___y_1355_ = v___x_1434_;
goto v___jp_1345_;
}
else
{
uint8_t v___x_1435_; 
v___x_1435_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1433_, v_arg_1411_, v_arg_1426_);
lean_dec(v___x_1433_);
v___y_1346_ = v_arg_1411_;
v___y_1347_ = v_arg_1423_;
v___y_1348_ = v_arg_1429_;
v___y_1349_ = v_arg_1417_;
v___y_1350_ = v___x_1410_;
v___y_1351_ = v___x_1431_;
v___y_1352_ = v_arg_1414_;
v___y_1353_ = v___x_1418_;
v___y_1354_ = v_arg_1426_;
v___y_1355_ = v___x_1435_;
goto v___jp_1345_;
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
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2(void){
_start:
{
uint8_t v___x_1443_; uint64_t v___x_1444_; 
v___x_1443_ = 1;
v___x_1444_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1443_);
return v___x_1444_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4(void){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1446_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1447_ = lean_unsigned_to_nat(38u);
v___x_1448_ = lean_unsigned_to_nat(250u);
v___x_1449_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3));
v___x_1450_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1451_ = l_mkPanicMessageWithDecl(v___x_1450_, v___x_1449_, v___x_1448_, v___x_1447_, v___x_1446_);
return v___x_1451_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6(void){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1453_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5));
v___x_1454_ = lean_unsigned_to_nat(6u);
v___x_1455_ = lean_unsigned_to_nat(260u);
v___x_1456_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3));
v___x_1457_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1458_ = l_mkPanicMessageWithDecl(v___x_1457_, v___x_1456_, v___x_1455_, v___x_1454_, v___x_1453_);
return v___x_1458_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2(void){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1461_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__1));
v___x_1462_ = lean_unsigned_to_nat(4u);
v___x_1463_ = lean_unsigned_to_nat(219u);
v___x_1464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__0));
v___x_1465_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1466_ = l_mkPanicMessageWithDecl(v___x_1465_, v___x_1464_, v___x_1463_, v___x_1462_, v___x_1461_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(lean_object* v_lhs_1467_, lean_object* v_rhs_1468_, uint8_t v_heq_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_){
_start:
{
lean_object* v_numArgs_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; 
v_numArgs_1481_ = l_Lean_Expr_getAppNumArgs(v_lhs_1467_);
v___x_1482_ = l_Lean_Expr_getAppNumArgs(v_rhs_1468_);
v___x_1483_ = lean_nat_dec_eq(v___x_1482_, v_numArgs_1481_);
lean_dec(v___x_1482_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_dec(v_numArgs_1481_);
lean_dec_ref(v_rhs_1468_);
lean_dec_ref(v_lhs_1467_);
v___x_1484_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2);
v___x_1485_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1484_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_);
return v___x_1485_;
}
else
{
lean_object* v_f_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v_f_1486_ = l_Lean_Expr_getAppFn(v_lhs_1467_);
v___x_1487_ = lean_box(0);
lean_inc_ref(v_f_1486_);
v___x_1488_ = l_Lean_Meta_getFunInfo(v_f_1486_, v___x_1487_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v___x_1488_, 1);
v___x_1490_ = l_Lean_Meta_FunInfo_getArity(v_a_1489_);
lean_dec(v_a_1489_);
v___x_1491_ = lean_nat_dec_lt(v___x_1490_, v_numArgs_1481_);
lean_dec(v___x_1490_);
if (v___x_1491_ == 0)
{
lean_object* v_g_1492_; lean_object* v___x_1493_; 
v_g_1492_ = l_Lean_Expr_getAppFn(v_rhs_1468_);
v___x_1493_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_1486_, v_g_1492_, v_numArgs_1481_, v_lhs_1467_, v_rhs_1468_, v_heq_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_);
return v___x_1493_;
}
else
{
lean_object* v___x_1494_; 
lean_dec_ref(v_f_1486_);
lean_dec(v_numArgs_1481_);
lean_inc_ref(v_lhs_1467_);
v___x_1494_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(v_lhs_1467_, v_rhs_1468_);
if (lean_obj_tag(v___x_1494_) == 1)
{
lean_object* v_val_1495_; lean_object* v_fst_1496_; lean_object* v_snd_1497_; lean_object* v___y_1499_; lean_object* v___x_1512_; 
v_val_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_val_1495_);
lean_dec_ref_known(v___x_1494_, 1);
v_fst_1496_ = lean_ctor_get(v_val_1495_, 0);
lean_inc(v_fst_1496_);
v_snd_1497_ = lean_ctor_get(v_val_1495_, 1);
lean_inc_n(v_snd_1497_, 2);
lean_dec(v_val_1495_);
v___x_1512_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(v_fst_1496_, v_snd_1497_, v_a_1473_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_);
if (lean_obj_tag(v___x_1512_) == 0)
{
v___y_1499_ = v___x_1512_;
goto v___jp_1498_;
}
else
{
lean_object* v_a_1513_; uint8_t v___y_1515_; uint8_t v___x_1517_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
v___x_1517_ = l_Lean_Exception_isInterrupt(v_a_1513_);
if (v___x_1517_ == 0)
{
uint8_t v___x_1518_; 
v___x_1518_ = l_Lean_Exception_isRuntime(v_a_1513_);
v___y_1515_ = v___x_1518_;
goto v___jp_1514_;
}
else
{
lean_dec(v_a_1513_);
v___y_1515_ = v___x_1517_;
goto v___jp_1514_;
}
v___jp_1514_:
{
if (v___y_1515_ == 0)
{
lean_object* v___x_1516_; 
lean_dec_ref_known(v___x_1512_, 1);
lean_inc_ref(v_rhs_1468_);
lean_inc_ref(v_lhs_1467_);
v___x_1516_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1467_, v_rhs_1468_, lean_box(0), v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_);
v___y_1499_ = v___x_1516_;
goto v___jp_1498_;
}
else
{
v___y_1499_ = v___x_1512_;
goto v___jp_1498_;
}
}
}
v___jp_1498_:
{
if (lean_obj_tag(v___y_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1501_; 
v_a_1500_ = lean_ctor_get(v___y_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___y_1499_, 1);
v___x_1501_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_1500_, v_lhs_1467_, v_rhs_1468_, v_snd_1497_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_);
lean_dec(v_snd_1497_);
lean_dec_ref(v_rhs_1468_);
lean_dec_ref(v_lhs_1467_);
lean_dec(v_a_1500_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1503_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1501_, 1);
v___x_1503_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_1502_, v_heq_1469_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_);
return v___x_1503_;
}
else
{
return v___x_1501_;
}
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_dec(v_snd_1497_);
lean_dec_ref(v_rhs_1468_);
lean_dec_ref(v_lhs_1467_);
v_a_1504_ = lean_ctor_get(v___y_1499_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___y_1499_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___y_1499_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___y_1499_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
else
{
lean_object* v___x_1519_; 
lean_dec(v___x_1494_);
v___x_1519_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1467_, v_rhs_1468_, lean_box(0), v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_);
return v___x_1519_;
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec_ref(v_f_1486_);
lean_dec(v_numArgs_1481_);
lean_dec_ref(v_rhs_1468_);
lean_dec_ref(v_lhs_1467_);
v_a_1520_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1488_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1488_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(lean_object* v_lhs_1528_, lean_object* v_rhs_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
uint8_t v___x_1541_; 
v___x_1541_ = l_Lean_Expr_isApp(v_lhs_1528_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = lean_box(0);
v___x_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
return v___x_1543_;
}
else
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1544_ = l_Lean_Expr_appFn_x21(v_lhs_1528_);
v___x_1545_ = l_Lean_Expr_appFn_x21(v_rhs_1529_);
v___x_1546_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v___x_1544_, v___x_1545_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
lean_dec_ref(v___x_1545_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1642_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1549_ = v___x_1546_;
v_isShared_1550_ = v_isSharedCheck_1642_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1642_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v_a_u2081_1551_; lean_object* v_a_u2082_1552_; 
v_a_u2081_1551_ = l_Lean_Expr_appArg_x21(v_lhs_1528_);
v_a_u2082_1552_ = l_Lean_Expr_appArg_x21(v_rhs_1529_);
if (lean_obj_tag(v_a_1547_) == 1)
{
lean_object* v_val_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1608_; 
lean_del_object(v___x_1549_);
lean_dec_ref(v___x_1544_);
v_val_1553_ = lean_ctor_get(v_a_1547_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_a_1547_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1555_ = v_a_1547_;
v_isShared_1556_ = v_isSharedCheck_1608_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_val_1553_);
lean_dec(v_a_1547_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1608_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
uint8_t v___x_1557_; 
v___x_1557_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_u2081_1551_, v_a_u2082_1552_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; 
v___x_1558_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_1551_, v_a_u2082_1552_, v___x_1557_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1560_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1558_, 1);
v___x_1560_ = l_Lean_Meta_mkCongr(v_val_1553_, v_a_1559_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1571_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1563_ = v___x_1560_;
v_isShared_1564_ = v_isSharedCheck_1571_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1571_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v_a_1561_);
v___x_1566_ = v___x_1555_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1568_; 
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v___x_1566_);
v___x_1568_ = v___x_1563_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_del_object(v___x_1555_);
v_a_1572_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1560_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1560_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_del_object(v___x_1555_);
lean_dec(v_val_1553_);
v_a_1580_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1558_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1558_);
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
lean_object* v___x_1588_; 
lean_dec_ref(v_a_u2082_1552_);
v___x_1588_ = l_Lean_Meta_mkCongrFun(v_val_1553_, v_a_u2081_1551_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1599_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1599_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1599_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v_a_1589_);
v___x_1594_ = v___x_1555_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1596_; 
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1594_);
v___x_1596_ = v___x_1591_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_del_object(v___x_1555_);
v_a_1600_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1588_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1588_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
}
else
{
uint8_t v___x_1609_; 
lean_dec(v_a_1547_);
v___x_1609_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_u2081_1551_, v_a_u2082_1552_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; 
lean_del_object(v___x_1549_);
v___x_1610_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_1551_, v_a_u2082_1552_, v___x_1609_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1612_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1610_, 1);
v___x_1612_ = l_Lean_Meta_mkCongrArg(v___x_1544_, v_a_1611_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
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
lean_dec_ref(v___x_1544_);
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
lean_dec_ref(v_a_u2082_1552_);
lean_dec_ref(v_a_u2081_1551_);
lean_dec_ref(v___x_1544_);
v___x_1638_ = lean_box(0);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1638_);
v___x_1640_ = v___x_1549_;
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
lean_dec_ref(v___x_1544_);
return v___x_1546_;
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
lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; uint8_t v___y_1766_; lean_object* v___y_1767_; uint8_t v___y_1768_; lean_object* v_fileName_1802_; lean_object* v_fileMap_1803_; lean_object* v_options_1804_; lean_object* v_currRecDepth_1805_; lean_object* v_maxRecDepth_1806_; lean_object* v_ref_1807_; lean_object* v_currNamespace_1808_; lean_object* v_openDecls_1809_; lean_object* v_initHeartbeats_1810_; lean_object* v_maxHeartbeats_1811_; lean_object* v_quotContext_1812_; lean_object* v_currMacroScope_1813_; uint8_t v_diag_1814_; lean_object* v_cancelTk_x3f_1815_; uint8_t v_suppressElabErrors_1816_; lean_object* v_inheritedTraceOptions_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; lean_object* v___x_1849_; uint8_t v___x_1850_; 
v_fileName_1802_ = lean_ctor_get(v_a_1729_, 0);
v_fileMap_1803_ = lean_ctor_get(v_a_1729_, 1);
v_options_1804_ = lean_ctor_get(v_a_1729_, 2);
v_currRecDepth_1805_ = lean_ctor_get(v_a_1729_, 3);
v_maxRecDepth_1806_ = lean_ctor_get(v_a_1729_, 4);
v_ref_1807_ = lean_ctor_get(v_a_1729_, 5);
v_currNamespace_1808_ = lean_ctor_get(v_a_1729_, 6);
v_openDecls_1809_ = lean_ctor_get(v_a_1729_, 7);
v_initHeartbeats_1810_ = lean_ctor_get(v_a_1729_, 8);
v_maxHeartbeats_1811_ = lean_ctor_get(v_a_1729_, 9);
v_quotContext_1812_ = lean_ctor_get(v_a_1729_, 10);
v_currMacroScope_1813_ = lean_ctor_get(v_a_1729_, 11);
v_diag_1814_ = lean_ctor_get_uint8(v_a_1729_, sizeof(void*)*14);
v_cancelTk_x3f_1815_ = lean_ctor_get(v_a_1729_, 12);
v_suppressElabErrors_1816_ = lean_ctor_get_uint8(v_a_1729_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1817_ = lean_ctor_get(v_a_1729_, 13);
v___x_1818_ = l_Lean_Expr_cleanupAnnotations(v_lhs_1719_);
v___x_1819_ = l_Lean_Expr_isApp(v___x_1818_);
v___x_1849_ = lean_unsigned_to_nat(0u);
v___x_1850_ = lean_nat_dec_eq(v_maxRecDepth_1806_, v___x_1849_);
if (v___x_1850_ == 0)
{
uint8_t v___x_1851_; 
v___x_1851_ = lean_nat_dec_eq(v_currRecDepth_1805_, v_maxRecDepth_1806_);
if (v___x_1851_ == 0)
{
goto v___jp_1820_;
}
else
{
lean_object* v___x_1852_; 
lean_dec_ref(v___x_1818_);
lean_dec_ref(v_rhs_1720_);
lean_inc(v_ref_1807_);
v___x_1852_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1807_);
return v___x_1852_;
}
}
else
{
goto v___jp_1820_;
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
lean_dec_ref(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec_ref(v___y_1759_);
v___x_1769_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__4, &l_Lean_Meta_Grind_mkEqCongrProof___closed__4_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__4);
v___x_1770_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1769_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v___y_1763_, v_a_1730_);
lean_dec_ref(v___y_1763_);
return v___x_1770_;
}
else
{
lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = l_Lean_Expr_constLevels_x21(v___y_1760_);
lean_dec_ref(v___y_1760_);
v___x_1772_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___y_1762_, v___y_1759_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; 
lean_inc_ref(v___y_1765_);
lean_inc_ref(v___y_1767_);
v___x_1773_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1767_, v___y_1765_, v___y_1766_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v___y_1763_, v_a_1730_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1775_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref_known(v___x_1773_, 1);
lean_inc_ref(v___y_1761_);
lean_inc_ref(v___y_1764_);
v___x_1775_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1764_, v___y_1761_, v___y_1766_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v___y_1763_, v_a_1730_);
lean_dec_ref(v___y_1763_);
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
v___x_1781_ = l_Lean_mkConst(v___x_1780_, v___x_1771_);
v___x_1782_ = l_Lean_mkApp8(v___x_1781_, v___y_1762_, v___y_1759_, v___y_1767_, v___y_1764_, v___y_1765_, v___y_1761_, v_a_1774_, v_a_1776_);
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
lean_dec(v___x_1771_);
lean_dec_ref(v___y_1767_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v___y_1759_);
return v___x_1775_;
}
}
else
{
lean_dec(v___x_1771_);
lean_dec_ref(v___y_1767_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v___y_1759_);
return v___x_1773_;
}
}
else
{
uint8_t v___x_1787_; lean_object* v___x_1788_; 
lean_dec_ref(v___y_1759_);
v___x_1787_ = 0;
lean_inc_ref(v___y_1765_);
lean_inc_ref(v___y_1767_);
v___x_1788_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1767_, v___y_1765_, v___x_1787_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v___y_1763_, v_a_1730_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1790_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
lean_inc_ref(v___y_1761_);
lean_inc_ref(v___y_1764_);
v___x_1790_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1764_, v___y_1761_, v___x_1787_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v___y_1763_, v_a_1730_);
lean_dec_ref(v___y_1763_);
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
v___x_1796_ = l_Lean_mkConst(v___x_1795_, v___x_1771_);
v___x_1797_ = l_Lean_mkApp7(v___x_1796_, v___y_1762_, v___y_1767_, v___y_1764_, v___y_1765_, v___y_1761_, v_a_1789_, v_a_1791_);
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
lean_dec(v___x_1771_);
lean_dec_ref(v___y_1767_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v___y_1761_);
return v___x_1790_;
}
}
else
{
lean_dec(v___x_1771_);
lean_dec_ref(v___y_1767_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v___y_1761_);
return v___x_1788_;
}
}
}
}
v___jp_1820_:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = lean_unsigned_to_nat(1u);
v___x_1822_ = lean_nat_add(v_currRecDepth_1805_, v___x_1821_);
lean_inc_ref(v_inheritedTraceOptions_1817_);
lean_inc(v_cancelTk_x3f_1815_);
lean_inc(v_currMacroScope_1813_);
lean_inc(v_quotContext_1812_);
lean_inc(v_maxHeartbeats_1811_);
lean_inc(v_initHeartbeats_1810_);
lean_inc(v_openDecls_1809_);
lean_inc(v_currNamespace_1808_);
lean_inc(v_ref_1807_);
lean_inc(v_maxRecDepth_1806_);
lean_inc_ref(v_options_1804_);
lean_inc_ref(v_fileMap_1803_);
lean_inc_ref(v_fileName_1802_);
v___x_1823_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1823_, 0, v_fileName_1802_);
lean_ctor_set(v___x_1823_, 1, v_fileMap_1803_);
lean_ctor_set(v___x_1823_, 2, v_options_1804_);
lean_ctor_set(v___x_1823_, 3, v___x_1822_);
lean_ctor_set(v___x_1823_, 4, v_maxRecDepth_1806_);
lean_ctor_set(v___x_1823_, 5, v_ref_1807_);
lean_ctor_set(v___x_1823_, 6, v_currNamespace_1808_);
lean_ctor_set(v___x_1823_, 7, v_openDecls_1809_);
lean_ctor_set(v___x_1823_, 8, v_initHeartbeats_1810_);
lean_ctor_set(v___x_1823_, 9, v_maxHeartbeats_1811_);
lean_ctor_set(v___x_1823_, 10, v_quotContext_1812_);
lean_ctor_set(v___x_1823_, 11, v_currMacroScope_1813_);
lean_ctor_set(v___x_1823_, 12, v_cancelTk_x3f_1815_);
lean_ctor_set(v___x_1823_, 13, v_inheritedTraceOptions_1817_);
lean_ctor_set_uint8(v___x_1823_, sizeof(void*)*14, v_diag_1814_);
lean_ctor_set_uint8(v___x_1823_, sizeof(void*)*14 + 1, v_suppressElabErrors_1816_);
if (v___x_1819_ == 0)
{
lean_dec_ref(v___x_1818_);
lean_dec_ref(v_rhs_1720_);
v___y_1733_ = v_a_1721_;
v___y_1734_ = v_a_1722_;
v___y_1735_ = v_a_1723_;
v___y_1736_ = v_a_1724_;
v___y_1737_ = v_a_1725_;
v___y_1738_ = v_a_1726_;
v___y_1739_ = v_a_1727_;
v___y_1740_ = v_a_1728_;
v___y_1741_ = v___x_1823_;
v___y_1742_ = v_a_1730_;
goto v___jp_1732_;
}
else
{
lean_object* v_arg_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v_arg_1824_ = lean_ctor_get(v___x_1818_, 1);
lean_inc_ref(v_arg_1824_);
v___x_1825_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1818_);
v___x_1826_ = l_Lean_Expr_isApp(v___x_1825_);
if (v___x_1826_ == 0)
{
lean_dec_ref(v___x_1825_);
lean_dec_ref(v_arg_1824_);
lean_dec_ref(v_rhs_1720_);
v___y_1733_ = v_a_1721_;
v___y_1734_ = v_a_1722_;
v___y_1735_ = v_a_1723_;
v___y_1736_ = v_a_1724_;
v___y_1737_ = v_a_1725_;
v___y_1738_ = v_a_1726_;
v___y_1739_ = v_a_1727_;
v___y_1740_ = v_a_1728_;
v___y_1741_ = v___x_1823_;
v___y_1742_ = v_a_1730_;
goto v___jp_1732_;
}
else
{
lean_object* v_arg_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v_arg_1827_ = lean_ctor_get(v___x_1825_, 1);
lean_inc_ref(v_arg_1827_);
v___x_1828_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1825_);
v___x_1829_ = l_Lean_Expr_isApp(v___x_1828_);
if (v___x_1829_ == 0)
{
lean_dec_ref(v___x_1828_);
lean_dec_ref(v_arg_1827_);
lean_dec_ref(v_arg_1824_);
lean_dec_ref(v_rhs_1720_);
v___y_1733_ = v_a_1721_;
v___y_1734_ = v_a_1722_;
v___y_1735_ = v_a_1723_;
v___y_1736_ = v_a_1724_;
v___y_1737_ = v_a_1725_;
v___y_1738_ = v_a_1726_;
v___y_1739_ = v_a_1727_;
v___y_1740_ = v_a_1728_;
v___y_1741_ = v___x_1823_;
v___y_1742_ = v_a_1730_;
goto v___jp_1732_;
}
else
{
lean_object* v_arg_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v_arg_1830_ = lean_ctor_get(v___x_1828_, 1);
lean_inc_ref(v_arg_1830_);
v___x_1831_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1828_);
v___x_1832_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_1833_ = l_Lean_Expr_isConstOf(v___x_1831_, v___x_1832_);
if (v___x_1833_ == 0)
{
lean_dec_ref(v___x_1831_);
lean_dec_ref(v_arg_1830_);
lean_dec_ref(v_arg_1827_);
lean_dec_ref(v_arg_1824_);
lean_dec_ref(v_rhs_1720_);
v___y_1733_ = v_a_1721_;
v___y_1734_ = v_a_1722_;
v___y_1735_ = v_a_1723_;
v___y_1736_ = v_a_1724_;
v___y_1737_ = v_a_1725_;
v___y_1738_ = v_a_1726_;
v___y_1739_ = v_a_1727_;
v___y_1740_ = v_a_1728_;
v___y_1741_ = v___x_1823_;
v___y_1742_ = v_a_1730_;
goto v___jp_1732_;
}
else
{
lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1834_ = l_Lean_Expr_cleanupAnnotations(v_rhs_1720_);
v___x_1835_ = l_Lean_Expr_isApp(v___x_1834_);
if (v___x_1835_ == 0)
{
lean_dec_ref(v___x_1834_);
lean_dec_ref(v___x_1831_);
lean_dec_ref(v_arg_1830_);
lean_dec_ref(v_arg_1827_);
lean_dec_ref(v_arg_1824_);
v___y_1746_ = v_a_1721_;
v___y_1747_ = v_a_1722_;
v___y_1748_ = v_a_1723_;
v___y_1749_ = v_a_1724_;
v___y_1750_ = v_a_1725_;
v___y_1751_ = v_a_1726_;
v___y_1752_ = v_a_1727_;
v___y_1753_ = v_a_1728_;
v___y_1754_ = v___x_1823_;
v___y_1755_ = v_a_1730_;
goto v___jp_1745_;
}
else
{
lean_object* v_arg_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; 
v_arg_1836_ = lean_ctor_get(v___x_1834_, 1);
lean_inc_ref(v_arg_1836_);
v___x_1837_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1834_);
v___x_1838_ = l_Lean_Expr_isApp(v___x_1837_);
if (v___x_1838_ == 0)
{
lean_dec_ref(v___x_1837_);
lean_dec_ref(v_arg_1836_);
lean_dec_ref(v___x_1831_);
lean_dec_ref(v_arg_1830_);
lean_dec_ref(v_arg_1827_);
lean_dec_ref(v_arg_1824_);
v___y_1746_ = v_a_1721_;
v___y_1747_ = v_a_1722_;
v___y_1748_ = v_a_1723_;
v___y_1749_ = v_a_1724_;
v___y_1750_ = v_a_1725_;
v___y_1751_ = v_a_1726_;
v___y_1752_ = v_a_1727_;
v___y_1753_ = v_a_1728_;
v___y_1754_ = v___x_1823_;
v___y_1755_ = v_a_1730_;
goto v___jp_1745_;
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
lean_dec_ref(v___x_1831_);
lean_dec_ref(v_arg_1830_);
lean_dec_ref(v_arg_1827_);
lean_dec_ref(v_arg_1824_);
v___y_1746_ = v_a_1721_;
v___y_1747_ = v_a_1722_;
v___y_1748_ = v_a_1723_;
v___y_1749_ = v_a_1724_;
v___y_1750_ = v_a_1725_;
v___y_1751_ = v_a_1726_;
v___y_1752_ = v_a_1727_;
v___y_1753_ = v_a_1728_;
v___y_1754_ = v___x_1823_;
v___y_1755_ = v_a_1730_;
goto v___jp_1745_;
}
else
{
lean_object* v_arg_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; 
v_arg_1842_ = lean_ctor_get(v___x_1840_, 1);
lean_inc_ref(v_arg_1842_);
v___x_1843_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1840_);
v___x_1844_ = l_Lean_Expr_isConstOf(v___x_1843_, v___x_1832_);
lean_dec_ref(v___x_1843_);
if (v___x_1844_ == 0)
{
lean_dec_ref(v_arg_1842_);
lean_dec_ref(v_arg_1839_);
lean_dec_ref(v_arg_1836_);
lean_dec_ref(v___x_1831_);
lean_dec_ref(v_arg_1830_);
lean_dec_ref(v_arg_1827_);
lean_dec_ref(v_arg_1824_);
v___y_1746_ = v_a_1721_;
v___y_1747_ = v_a_1722_;
v___y_1748_ = v_a_1723_;
v___y_1749_ = v_a_1724_;
v___y_1750_ = v_a_1725_;
v___y_1751_ = v_a_1726_;
v___y_1752_ = v_a_1727_;
v___y_1753_ = v_a_1728_;
v___y_1754_ = v___x_1823_;
v___y_1755_ = v_a_1730_;
goto v___jp_1745_;
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1845_ = lean_st_ref_get(v_a_1721_);
v___x_1846_ = lean_st_ref_get(v_a_1721_);
v___x_1847_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1845_, v_arg_1827_, v_arg_1839_);
lean_dec(v___x_1845_);
if (v___x_1847_ == 0)
{
lean_dec(v___x_1846_);
v___y_1759_ = v_arg_1842_;
v___y_1760_ = v___x_1831_;
v___y_1761_ = v_arg_1836_;
v___y_1762_ = v_arg_1830_;
v___y_1763_ = v___x_1823_;
v___y_1764_ = v_arg_1824_;
v___y_1765_ = v_arg_1839_;
v___y_1766_ = v___x_1844_;
v___y_1767_ = v_arg_1827_;
v___y_1768_ = v___x_1847_;
goto v___jp_1758_;
}
else
{
uint8_t v___x_1848_; 
v___x_1848_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1846_, v_arg_1824_, v_arg_1836_);
lean_dec(v___x_1846_);
v___y_1759_ = v_arg_1842_;
v___y_1760_ = v___x_1831_;
v___y_1761_ = v_arg_1836_;
v___y_1762_ = v_arg_1830_;
v___y_1763_ = v___x_1823_;
v___y_1764_ = v_arg_1824_;
v___y_1765_ = v_arg_1839_;
v___y_1766_ = v___x_1844_;
v___y_1767_ = v_arg_1827_;
v___y_1768_ = v___x_1848_;
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
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1863_ = lean_box(0);
v___x_1864_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3));
v___x_1865_ = l_Lean_mkConst(v___x_1864_, v___x_1863_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(lean_object* v_lhs_1866_, lean_object* v_rhs_1867_, uint8_t v_heq_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
lean_object* v___x_1880_; lean_object* v_p_1881_; lean_object* v___x_1882_; lean_object* v_q_1883_; uint8_t v___x_1884_; lean_object* v___x_1885_; 
v___x_1880_ = l_Lean_Expr_appFn_x21(v_lhs_1866_);
v_p_1881_ = l_Lean_Expr_appArg_x21(v___x_1880_);
lean_dec_ref(v___x_1880_);
v___x_1882_ = l_Lean_Expr_appFn_x21(v_rhs_1867_);
v_q_1883_ = l_Lean_Expr_appArg_x21(v___x_1882_);
lean_dec_ref(v___x_1882_);
v___x_1884_ = 0;
lean_inc_ref(v_q_1883_);
lean_inc_ref(v_p_1881_);
v___x_1885_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_p_1881_, v_q_1883_, v___x_1884_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v_hp_1887_; lean_object* v_hq_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v_hp_1887_ = l_Lean_Expr_appArg_x21(v_lhs_1866_);
v_hq_1888_ = l_Lean_Expr_appArg_x21(v_rhs_1867_);
v___x_1889_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4);
v___x_1890_ = l_Lean_mkApp5(v___x_1889_, v_p_1881_, v_q_1883_, v_a_1886_, v_hp_1887_, v_hq_1888_);
v___x_1891_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v___x_1890_, v_heq_1868_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
return v___x_1891_;
}
else
{
lean_dec_ref(v_q_1883_);
lean_dec_ref(v_p_1881_);
return v___x_1885_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = lean_box(0);
v___x_1903_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1));
v___x_1904_ = l_Lean_mkConst(v___x_1903_, v___x_1902_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(lean_object* v_lhs_1905_, lean_object* v_rhs_1906_, uint8_t v_heq_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v___x_1919_; lean_object* v_p_1920_; lean_object* v___x_1921_; lean_object* v_q_1922_; uint8_t v___x_1923_; lean_object* v___x_1924_; 
v___x_1919_ = l_Lean_Expr_appFn_x21(v_lhs_1905_);
v_p_1920_ = l_Lean_Expr_appArg_x21(v___x_1919_);
lean_dec_ref(v___x_1919_);
v___x_1921_ = l_Lean_Expr_appFn_x21(v_rhs_1906_);
v_q_1922_ = l_Lean_Expr_appArg_x21(v___x_1921_);
lean_dec_ref(v___x_1921_);
v___x_1923_ = 0;
lean_inc_ref(v_q_1922_);
lean_inc_ref(v_p_1920_);
v___x_1924_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_p_1920_, v_q_1922_, v___x_1923_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v_hp_1926_; lean_object* v_hq_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v___x_1924_, 1);
v_hp_1926_ = l_Lean_Expr_appArg_x21(v_lhs_1905_);
v_hq_1927_ = l_Lean_Expr_appArg_x21(v_rhs_1906_);
v___x_1928_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2);
v___x_1929_ = l_Lean_mkApp5(v___x_1928_, v_p_1920_, v_q_1922_, v_a_1925_, v_hp_1926_, v_hq_1927_);
v___x_1930_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v___x_1929_, v_heq_1907_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
return v___x_1930_;
}
else
{
lean_dec_ref(v_q_1922_);
lean_dec_ref(v_p_1920_);
return v___x_1924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(lean_object* v_lhs_1931_, lean_object* v_rhs_1932_, uint8_t v_heq_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
if (lean_obj_tag(v_lhs_1931_) == 7)
{
if (lean_obj_tag(v_rhs_1932_) == 7)
{
lean_object* v_binderType_1945_; lean_object* v_body_1946_; lean_object* v_binderType_1947_; lean_object* v_body_1948_; lean_object* v___y_1950_; lean_object* v_a_1951_; lean_object* v___x_1970_; uint8_t v_foApprox_1971_; uint8_t v_ctxApprox_1972_; uint8_t v_quasiPatternApprox_1973_; uint8_t v_constApprox_1974_; uint8_t v_isDefEqStuckEx_1975_; uint8_t v_unificationHints_1976_; uint8_t v_proofIrrelevance_1977_; uint8_t v_assignSyntheticOpaque_1978_; uint8_t v_offsetCnstrs_1979_; uint8_t v_etaStruct_1980_; uint8_t v_univApprox_1981_; uint8_t v_iota_1982_; uint8_t v_beta_1983_; uint8_t v_proj_1984_; uint8_t v_zeta_1985_; uint8_t v_zetaDelta_1986_; uint8_t v_zetaUnused_1987_; uint8_t v_zetaHave_1988_; uint8_t v_trackZetaDelta_1989_; lean_object* v_zetaDeltaSet_1990_; lean_object* v_lctx_1991_; lean_object* v_localInstances_1992_; lean_object* v_defEqCtx_x3f_1993_; lean_object* v_synthPendingDepth_1994_; lean_object* v_canUnfold_x3f_1995_; uint8_t v_univApprox_1996_; uint8_t v_inTypeClassResolution_1997_; uint8_t v_cacheInferType_1998_; lean_object* v_a_2000_; uint8_t v___x_2046_; lean_object* v_config_2047_; uint64_t v___x_2048_; uint64_t v___x_2049_; uint64_t v___x_2050_; uint64_t v___x_2051_; uint64_t v___x_2052_; uint64_t v_key_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v_binderType_1945_ = lean_ctor_get(v_lhs_1931_, 1);
lean_inc_ref_n(v_binderType_1945_, 2);
v_body_1946_ = lean_ctor_get(v_lhs_1931_, 2);
lean_inc_ref(v_body_1946_);
lean_dec_ref_known(v_lhs_1931_, 3);
v_binderType_1947_ = lean_ctor_get(v_rhs_1932_, 1);
lean_inc_ref(v_binderType_1947_);
v_body_1948_ = lean_ctor_get(v_rhs_1932_, 2);
lean_inc_ref(v_body_1948_);
lean_dec_ref_known(v_rhs_1932_, 3);
v___x_1970_ = l_Lean_Meta_Context_config(v_a_1940_);
v_foApprox_1971_ = lean_ctor_get_uint8(v___x_1970_, 0);
v_ctxApprox_1972_ = lean_ctor_get_uint8(v___x_1970_, 1);
v_quasiPatternApprox_1973_ = lean_ctor_get_uint8(v___x_1970_, 2);
v_constApprox_1974_ = lean_ctor_get_uint8(v___x_1970_, 3);
v_isDefEqStuckEx_1975_ = lean_ctor_get_uint8(v___x_1970_, 4);
v_unificationHints_1976_ = lean_ctor_get_uint8(v___x_1970_, 5);
v_proofIrrelevance_1977_ = lean_ctor_get_uint8(v___x_1970_, 6);
v_assignSyntheticOpaque_1978_ = lean_ctor_get_uint8(v___x_1970_, 7);
v_offsetCnstrs_1979_ = lean_ctor_get_uint8(v___x_1970_, 8);
v_etaStruct_1980_ = lean_ctor_get_uint8(v___x_1970_, 10);
v_univApprox_1981_ = lean_ctor_get_uint8(v___x_1970_, 11);
v_iota_1982_ = lean_ctor_get_uint8(v___x_1970_, 12);
v_beta_1983_ = lean_ctor_get_uint8(v___x_1970_, 13);
v_proj_1984_ = lean_ctor_get_uint8(v___x_1970_, 14);
v_zeta_1985_ = lean_ctor_get_uint8(v___x_1970_, 15);
v_zetaDelta_1986_ = lean_ctor_get_uint8(v___x_1970_, 16);
v_zetaUnused_1987_ = lean_ctor_get_uint8(v___x_1970_, 17);
v_zetaHave_1988_ = lean_ctor_get_uint8(v___x_1970_, 18);
v_trackZetaDelta_1989_ = lean_ctor_get_uint8(v_a_1940_, sizeof(void*)*7);
v_zetaDeltaSet_1990_ = lean_ctor_get(v_a_1940_, 1);
v_lctx_1991_ = lean_ctor_get(v_a_1940_, 2);
v_localInstances_1992_ = lean_ctor_get(v_a_1940_, 3);
v_defEqCtx_x3f_1993_ = lean_ctor_get(v_a_1940_, 4);
v_synthPendingDepth_1994_ = lean_ctor_get(v_a_1940_, 5);
v_canUnfold_x3f_1995_ = lean_ctor_get(v_a_1940_, 6);
v_univApprox_1996_ = lean_ctor_get_uint8(v_a_1940_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1997_ = lean_ctor_get_uint8(v_a_1940_, sizeof(void*)*7 + 2);
v_cacheInferType_1998_ = lean_ctor_get_uint8(v_a_1940_, sizeof(void*)*7 + 3);
v___x_2046_ = 1;
v_config_2047_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_config_2047_, 0, v_foApprox_1971_);
lean_ctor_set_uint8(v_config_2047_, 1, v_ctxApprox_1972_);
lean_ctor_set_uint8(v_config_2047_, 2, v_quasiPatternApprox_1973_);
lean_ctor_set_uint8(v_config_2047_, 3, v_constApprox_1974_);
lean_ctor_set_uint8(v_config_2047_, 4, v_isDefEqStuckEx_1975_);
lean_ctor_set_uint8(v_config_2047_, 5, v_unificationHints_1976_);
lean_ctor_set_uint8(v_config_2047_, 6, v_proofIrrelevance_1977_);
lean_ctor_set_uint8(v_config_2047_, 7, v_assignSyntheticOpaque_1978_);
lean_ctor_set_uint8(v_config_2047_, 8, v_offsetCnstrs_1979_);
lean_ctor_set_uint8(v_config_2047_, 9, v___x_2046_);
lean_ctor_set_uint8(v_config_2047_, 10, v_etaStruct_1980_);
lean_ctor_set_uint8(v_config_2047_, 11, v_univApprox_1981_);
lean_ctor_set_uint8(v_config_2047_, 12, v_iota_1982_);
lean_ctor_set_uint8(v_config_2047_, 13, v_beta_1983_);
lean_ctor_set_uint8(v_config_2047_, 14, v_proj_1984_);
lean_ctor_set_uint8(v_config_2047_, 15, v_zeta_1985_);
lean_ctor_set_uint8(v_config_2047_, 16, v_zetaDelta_1986_);
lean_ctor_set_uint8(v_config_2047_, 17, v_zetaUnused_1987_);
lean_ctor_set_uint8(v_config_2047_, 18, v_zetaHave_1988_);
v___x_2048_ = l_Lean_Meta_Context_configKey(v_a_1940_);
v___x_2049_ = 3ULL;
v___x_2050_ = lean_uint64_shift_right(v___x_2048_, v___x_2049_);
v___x_2051_ = lean_uint64_shift_left(v___x_2050_, v___x_2049_);
v___x_2052_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2);
v_key_2053_ = lean_uint64_lor(v___x_2051_, v___x_2052_);
v___x_2054_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2054_, 0, v_config_2047_);
lean_ctor_set_uint64(v___x_2054_, sizeof(void*)*1, v_key_2053_);
lean_inc(v_canUnfold_x3f_1995_);
lean_inc(v_synthPendingDepth_1994_);
lean_inc(v_defEqCtx_x3f_1993_);
lean_inc_ref(v_localInstances_1992_);
lean_inc_ref(v_lctx_1991_);
lean_inc(v_zetaDeltaSet_1990_);
v___x_2055_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
lean_ctor_set(v___x_2055_, 1, v_zetaDeltaSet_1990_);
lean_ctor_set(v___x_2055_, 2, v_lctx_1991_);
lean_ctor_set(v___x_2055_, 3, v_localInstances_1992_);
lean_ctor_set(v___x_2055_, 4, v_defEqCtx_x3f_1993_);
lean_ctor_set(v___x_2055_, 5, v_synthPendingDepth_1994_);
lean_ctor_set(v___x_2055_, 6, v_canUnfold_x3f_1995_);
lean_ctor_set_uint8(v___x_2055_, sizeof(void*)*7, v_trackZetaDelta_1989_);
lean_ctor_set_uint8(v___x_2055_, sizeof(void*)*7 + 1, v_univApprox_1996_);
lean_ctor_set_uint8(v___x_2055_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1997_);
lean_ctor_set_uint8(v___x_2055_, sizeof(void*)*7 + 3, v_cacheInferType_1998_);
v___x_2056_ = l_Lean_Meta_getLevel(v_binderType_1945_, v___x_2055_, v_a_1941_, v_a_1942_, v_a_1943_);
lean_dec_ref_known(v___x_2055_, 7);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v___x_2056_, 1);
v_a_2000_ = v_a_2057_;
goto v___jp_1999_;
}
else
{
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2058_; 
v_a_2058_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2058_);
lean_dec_ref_known(v___x_2056_, 1);
v_a_2000_ = v_a_2058_;
goto v___jp_1999_;
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec_ref(v___x_1970_);
lean_dec_ref(v_body_1948_);
lean_dec_ref(v_binderType_1947_);
lean_dec_ref(v_body_1946_);
lean_dec_ref(v_binderType_1945_);
v_a_2059_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2056_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2056_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
v___jp_1949_:
{
uint8_t v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = 0;
lean_inc_ref(v_binderType_1947_);
lean_inc_ref(v_binderType_1945_);
v___x_1953_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_binderType_1945_, v_binderType_1947_, v___x_1952_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v___x_1955_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref_known(v___x_1953_, 1);
lean_inc_ref(v_body_1948_);
lean_inc_ref(v_body_1946_);
v___x_1955_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_body_1946_, v_body_1948_, v___x_1952_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1969_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1958_ = v___x_1955_;
v_isShared_1959_ = v_isSharedCheck_1969_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1955_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1969_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1960_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__1));
v___x_1961_ = lean_box(0);
v___x_1962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1962_, 0, v_a_1951_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___y_1950_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = l_Lean_mkConst(v___x_1960_, v___x_1963_);
v___x_1965_ = l_Lean_mkApp6(v___x_1964_, v_binderType_1945_, v_binderType_1947_, v_body_1946_, v_body_1948_, v_a_1954_, v_a_1956_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1965_);
v___x_1967_ = v___x_1958_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
else
{
lean_dec(v_a_1954_);
lean_dec(v_a_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v_body_1948_);
lean_dec_ref(v_binderType_1947_);
lean_dec_ref(v_body_1946_);
lean_dec_ref(v_binderType_1945_);
return v___x_1955_;
}
}
else
{
lean_dec(v_a_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v_body_1948_);
lean_dec_ref(v_binderType_1947_);
lean_dec_ref(v_body_1946_);
lean_dec_ref(v_binderType_1945_);
return v___x_1953_;
}
}
v___jp_1999_:
{
uint8_t v_foApprox_2001_; uint8_t v_ctxApprox_2002_; uint8_t v_quasiPatternApprox_2003_; uint8_t v_constApprox_2004_; uint8_t v_isDefEqStuckEx_2005_; uint8_t v_unificationHints_2006_; uint8_t v_proofIrrelevance_2007_; uint8_t v_assignSyntheticOpaque_2008_; uint8_t v_offsetCnstrs_2009_; uint8_t v_etaStruct_2010_; uint8_t v_univApprox_2011_; uint8_t v_iota_2012_; uint8_t v_beta_2013_; uint8_t v_proj_2014_; uint8_t v_zeta_2015_; uint8_t v_zetaDelta_2016_; uint8_t v_zetaUnused_2017_; uint8_t v_zetaHave_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2045_; 
v_foApprox_2001_ = lean_ctor_get_uint8(v___x_1970_, 0);
v_ctxApprox_2002_ = lean_ctor_get_uint8(v___x_1970_, 1);
v_quasiPatternApprox_2003_ = lean_ctor_get_uint8(v___x_1970_, 2);
v_constApprox_2004_ = lean_ctor_get_uint8(v___x_1970_, 3);
v_isDefEqStuckEx_2005_ = lean_ctor_get_uint8(v___x_1970_, 4);
v_unificationHints_2006_ = lean_ctor_get_uint8(v___x_1970_, 5);
v_proofIrrelevance_2007_ = lean_ctor_get_uint8(v___x_1970_, 6);
v_assignSyntheticOpaque_2008_ = lean_ctor_get_uint8(v___x_1970_, 7);
v_offsetCnstrs_2009_ = lean_ctor_get_uint8(v___x_1970_, 8);
v_etaStruct_2010_ = lean_ctor_get_uint8(v___x_1970_, 10);
v_univApprox_2011_ = lean_ctor_get_uint8(v___x_1970_, 11);
v_iota_2012_ = lean_ctor_get_uint8(v___x_1970_, 12);
v_beta_2013_ = lean_ctor_get_uint8(v___x_1970_, 13);
v_proj_2014_ = lean_ctor_get_uint8(v___x_1970_, 14);
v_zeta_2015_ = lean_ctor_get_uint8(v___x_1970_, 15);
v_zetaDelta_2016_ = lean_ctor_get_uint8(v___x_1970_, 16);
v_zetaUnused_2017_ = lean_ctor_get_uint8(v___x_1970_, 17);
v_zetaHave_2018_ = lean_ctor_get_uint8(v___x_1970_, 18);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2020_ = v___x_1970_;
v_isShared_2021_ = v_isSharedCheck_2045_;
goto v_resetjp_2019_;
}
else
{
lean_dec(v___x_1970_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2045_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
uint8_t v___x_2022_; lean_object* v_config_2024_; 
v___x_2022_ = 1;
if (v_isShared_2021_ == 0)
{
v_config_2024_ = v___x_2020_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, 0, v_foApprox_2001_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, 1, v_ctxApprox_2002_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, 2, v_quasiPatternApprox_2003_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, 3, v_constApprox_2004_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, 4, v_isDefEqStuckEx_2005_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, 5, v_unificationHints_2006_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, 6, v_proofIrrelevance_2007_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, 7, v_assignSyntheticOpaque_2008_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, 8, v_offsetCnstrs_2009_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, 10, v_etaStruct_2010_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, 11, v_univApprox_2011_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, 12, v_iota_2012_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, 13, v_beta_2013_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, 14, v_proj_2014_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, 15, v_zeta_2015_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, 16, v_zetaDelta_2016_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, 17, v_zetaUnused_2017_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, 18, v_zetaHave_2018_);
v_config_2024_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
uint64_t v___x_2025_; uint64_t v___x_2026_; uint64_t v___x_2027_; uint64_t v___x_2028_; uint64_t v___x_2029_; uint64_t v_key_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
lean_ctor_set_uint8(v_config_2024_, 9, v___x_2022_);
v___x_2025_ = l_Lean_Meta_Context_configKey(v_a_1940_);
v___x_2026_ = 3ULL;
v___x_2027_ = lean_uint64_shift_right(v___x_2025_, v___x_2026_);
v___x_2028_ = lean_uint64_shift_left(v___x_2027_, v___x_2026_);
v___x_2029_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2);
v_key_2030_ = lean_uint64_lor(v___x_2028_, v___x_2029_);
v___x_2031_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2031_, 0, v_config_2024_);
lean_ctor_set_uint64(v___x_2031_, sizeof(void*)*1, v_key_2030_);
lean_inc(v_canUnfold_x3f_1995_);
lean_inc(v_synthPendingDepth_1994_);
lean_inc(v_defEqCtx_x3f_1993_);
lean_inc_ref(v_localInstances_1992_);
lean_inc_ref(v_lctx_1991_);
lean_inc(v_zetaDeltaSet_1990_);
v___x_2032_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
lean_ctor_set(v___x_2032_, 1, v_zetaDeltaSet_1990_);
lean_ctor_set(v___x_2032_, 2, v_lctx_1991_);
lean_ctor_set(v___x_2032_, 3, v_localInstances_1992_);
lean_ctor_set(v___x_2032_, 4, v_defEqCtx_x3f_1993_);
lean_ctor_set(v___x_2032_, 5, v_synthPendingDepth_1994_);
lean_ctor_set(v___x_2032_, 6, v_canUnfold_x3f_1995_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*7, v_trackZetaDelta_1989_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*7 + 1, v_univApprox_1996_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1997_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*7 + 3, v_cacheInferType_1998_);
lean_inc_ref(v_body_1946_);
v___x_2033_ = l_Lean_Meta_getLevel(v_body_1946_, v___x_2032_, v_a_1941_, v_a_1942_, v_a_1943_);
lean_dec_ref_known(v___x_2032_, 7);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___x_2033_, 1);
v___y_1950_ = v_a_2000_;
v_a_1951_ = v_a_2034_;
goto v___jp_1949_;
}
else
{
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2035_; 
v_a_2035_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2033_, 1);
v___y_1950_ = v_a_2000_;
v_a_1951_ = v_a_2035_;
goto v___jp_1949_;
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_dec(v_a_2000_);
lean_dec_ref(v_body_1948_);
lean_dec_ref(v_binderType_1947_);
lean_dec_ref(v_body_1946_);
lean_dec_ref(v_binderType_1945_);
v_a_2036_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2033_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2033_);
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
}
}
}
}
else
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
lean_dec_ref_known(v_lhs_1931_, 3);
lean_dec_ref(v_rhs_1932_);
v___x_2067_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4);
v___x_2068_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2067_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
return v___x_2068_;
}
}
else
{
lean_object* v___x_2069_; 
lean_inc_ref(v_lhs_1931_);
v___x_2069_ = l_Lean_Meta_Grind_useFunCC___redArg(v_lhs_1931_, v_a_1934_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; uint8_t v___x_2071_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref_known(v___x_2069_, 1);
v___x_2071_ = lean_unbox(v_a_2070_);
lean_dec(v_a_2070_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v___x_2072_ = l_Lean_Expr_getAppNumArgs(v_lhs_1931_);
v___x_2073_ = l_Lean_Expr_getAppNumArgs(v_rhs_1932_);
v___x_2074_ = lean_nat_dec_eq(v___x_2073_, v___x_2072_);
lean_dec(v___x_2073_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
lean_dec(v___x_2072_);
lean_dec_ref(v_rhs_1932_);
lean_dec_ref(v_lhs_1931_);
v___x_2075_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6);
v___x_2076_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2075_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
return v___x_2076_;
}
else
{
lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___y_2094_; uint8_t v___y_2106_; lean_object* v___x_2110_; uint8_t v___x_2111_; uint8_t v___y_2116_; 
v___x_2077_ = l_Lean_Expr_getAppFn(v_lhs_1931_);
v___x_2078_ = l_Lean_Expr_getAppFn(v_rhs_1932_);
v___x_2110_ = lean_unsigned_to_nat(2u);
v___x_2111_ = lean_nat_dec_eq(v___x_2072_, v___x_2110_);
if (v___x_2111_ == 0)
{
v___y_2116_ = v___x_2111_;
goto v___jp_2115_;
}
else
{
lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10));
v___x_2121_ = l_Lean_Expr_isConstOf(v___x_2077_, v___x_2120_);
v___y_2116_ = v___x_2121_;
goto v___jp_2115_;
}
v___jp_2079_:
{
lean_object* v___x_2080_; 
lean_inc_ref(v_rhs_1932_);
lean_inc_ref(v_lhs_1931_);
v___x_2080_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(v_lhs_1931_, v_rhs_1932_, v___x_2077_, v___x_2078_, v___x_2072_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
lean_dec_ref(v___x_2078_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; uint8_t v___x_2082_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_a_2081_);
lean_dec_ref_known(v___x_2080_, 1);
v___x_2082_ = lean_unbox(v_a_2081_);
lean_dec(v_a_2081_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; 
v___x_2083_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_1931_, v_rhs_1932_, v_heq_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
return v___x_2083_;
}
else
{
lean_object* v___x_2084_; 
v___x_2084_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_1931_, v_rhs_1932_, v_heq_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
lean_dec_ref(v_rhs_1932_);
lean_dec_ref(v_lhs_1931_);
return v___x_2084_;
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec_ref(v_rhs_1932_);
lean_dec_ref(v_lhs_1931_);
v_a_2085_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2080_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2080_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
v___jp_2093_:
{
if (v___y_2094_ == 0)
{
goto v___jp_2079_;
}
else
{
lean_object* v___x_2095_; uint8_t v___x_2096_; 
v___x_2095_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_2096_ = l_Lean_Expr_isConstOf(v___x_2078_, v___x_2095_);
if (v___x_2096_ == 0)
{
goto v___jp_2079_;
}
else
{
lean_object* v___x_2097_; 
lean_dec_ref(v___x_2078_);
lean_dec_ref(v___x_2077_);
lean_dec(v___x_2072_);
v___x_2097_ = l_Lean_Meta_Grind_mkEqCongrProof(v_lhs_1931_, v_rhs_1932_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
if (lean_obj_tag(v___x_2097_) == 0)
{
if (v_heq_1933_ == 0)
{
return v___x_2097_;
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2099_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref_known(v___x_2097_, 1);
v___x_2099_ = l_Lean_Meta_mkHEqOfEq(v_a_2098_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
return v___x_2099_;
}
}
else
{
return v___x_2097_;
}
}
}
}
v___jp_2100_:
{
lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2101_ = lean_unsigned_to_nat(3u);
v___x_2102_ = lean_nat_dec_eq(v___x_2072_, v___x_2101_);
if (v___x_2102_ == 0)
{
v___y_2094_ = v___x_2102_;
goto v___jp_2093_;
}
else
{
lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2103_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_2104_ = l_Lean_Expr_isConstOf(v___x_2077_, v___x_2103_);
v___y_2094_ = v___x_2104_;
goto v___jp_2093_;
}
}
v___jp_2105_:
{
if (v___y_2106_ == 0)
{
goto v___jp_2100_;
}
else
{
lean_object* v___x_2107_; uint8_t v___x_2108_; 
v___x_2107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8));
v___x_2108_ = l_Lean_Expr_isConstOf(v___x_2078_, v___x_2107_);
if (v___x_2108_ == 0)
{
goto v___jp_2100_;
}
else
{
lean_object* v___x_2109_; 
lean_dec_ref(v___x_2078_);
lean_dec_ref(v___x_2077_);
lean_dec(v___x_2072_);
v___x_2109_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_1931_, v_rhs_1932_, v_heq_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
lean_dec_ref(v_rhs_1932_);
lean_dec_ref(v_lhs_1931_);
return v___x_2109_;
}
}
}
v___jp_2112_:
{
if (v___x_2111_ == 0)
{
v___y_2106_ = v___x_2111_;
goto v___jp_2105_;
}
else
{
lean_object* v___x_2113_; uint8_t v___x_2114_; 
v___x_2113_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8));
v___x_2114_ = l_Lean_Expr_isConstOf(v___x_2077_, v___x_2113_);
v___y_2106_ = v___x_2114_;
goto v___jp_2105_;
}
}
v___jp_2115_:
{
if (v___y_2116_ == 0)
{
goto v___jp_2112_;
}
else
{
lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10));
v___x_2118_ = l_Lean_Expr_isConstOf(v___x_2078_, v___x_2117_);
if (v___x_2118_ == 0)
{
goto v___jp_2112_;
}
else
{
lean_object* v___x_2119_; 
lean_dec_ref(v___x_2078_);
lean_dec_ref(v___x_2077_);
lean_dec(v___x_2072_);
v___x_2119_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_1931_, v_rhs_1932_, v_heq_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
lean_dec_ref(v_rhs_1932_);
lean_dec_ref(v_lhs_1931_);
return v___x_2119_;
}
}
}
}
}
else
{
lean_object* v___x_2122_; 
v___x_2122_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_1931_, v_rhs_1932_, v_heq_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
return v___x_2122_;
}
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec_ref(v_rhs_1932_);
lean_dec_ref(v_lhs_1931_);
v_a_2123_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2069_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2069_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(lean_object* v_lhs_2131_, lean_object* v_rhs_2132_, lean_object* v_h_2133_, uint8_t v_flipped_2134_, uint8_t v_heq_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_){
_start:
{
lean_object* v___x_2147_; uint8_t v___x_2148_; 
v___x_2147_ = l_Lean_Meta_Grind_congrPlaceholderProof;
v___x_2148_ = lean_expr_eqv(v_h_2133_, v___x_2147_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; uint8_t v___x_2150_; 
v___x_2149_ = l_Lean_Meta_Grind_eqCongrSymmPlaceholderProof;
v___x_2150_ = lean_expr_eqv(v_h_2133_, v___x_2149_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; 
lean_dec_ref(v_rhs_2132_);
lean_dec_ref(v_lhs_2131_);
v___x_2151_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(v_h_2133_, v_flipped_2134_, v_heq_2135_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_);
return v___x_2151_;
}
else
{
lean_object* v___x_2152_; 
lean_dec_ref(v_h_2133_);
v___x_2152_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(v_lhs_2131_, v_rhs_2132_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_);
if (lean_obj_tag(v___x_2152_) == 0)
{
if (v_heq_2135_ == 0)
{
return v___x_2152_;
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2154_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2153_);
lean_dec_ref_known(v___x_2152_, 1);
v___x_2154_ = l_Lean_Meta_mkHEqOfEq(v_a_2153_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_);
return v___x_2154_;
}
}
else
{
return v___x_2152_;
}
}
}
else
{
lean_object* v___x_2155_; 
lean_dec_ref(v_h_2133_);
v___x_2155_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(v_lhs_2131_, v_rhs_2132_, v_heq_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_);
return v___x_2155_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1(void){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2157_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2158_ = lean_unsigned_to_nat(29u);
v___x_2159_ = lean_unsigned_to_nat(288u);
v___x_2160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0));
v___x_2161_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2162_ = l_mkPanicMessageWithDecl(v___x_2161_, v___x_2160_, v___x_2159_, v___x_2158_, v___x_2157_);
return v___x_2162_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2(void){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2163_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2164_ = lean_unsigned_to_nat(35u);
v___x_2165_ = lean_unsigned_to_nat(287u);
v___x_2166_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0));
v___x_2167_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2168_ = l_mkPanicMessageWithDecl(v___x_2167_, v___x_2166_, v___x_2165_, v___x_2164_, v___x_2163_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(lean_object* v_lhs_2169_, lean_object* v_common_2170_, lean_object* v_acc_2171_, uint8_t v_heq_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_){
_start:
{
uint8_t v___x_2184_; 
v___x_2184_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_lhs_2169_, v_common_2170_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = lean_st_ref_get(v_a_2173_);
lean_inc_ref(v_lhs_2169_);
v___x_2186_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2185_, v_lhs_2169_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
lean_dec(v___x_2185_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v_target_x3f_2188_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2186_, 1);
v_target_x3f_2188_ = lean_ctor_get(v_a_2187_, 4);
lean_inc(v_target_x3f_2188_);
if (lean_obj_tag(v_target_x3f_2188_) == 1)
{
lean_object* v_proof_x3f_2189_; 
v_proof_x3f_2189_ = lean_ctor_get(v_a_2187_, 5);
lean_inc(v_proof_x3f_2189_);
if (lean_obj_tag(v_proof_x3f_2189_) == 1)
{
uint8_t v_flipped_2190_; lean_object* v_val_2191_; lean_object* v_val_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2220_; 
v_flipped_2190_ = lean_ctor_get_uint8(v_a_2187_, sizeof(void*)*12);
lean_dec(v_a_2187_);
v_val_2191_ = lean_ctor_get(v_target_x3f_2188_, 0);
lean_inc(v_val_2191_);
lean_dec_ref_known(v_target_x3f_2188_, 1);
v_val_2192_ = lean_ctor_get(v_proof_x3f_2189_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_proof_x3f_2189_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2194_ = v_proof_x3f_2189_;
v_isShared_2195_ = v_isSharedCheck_2220_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_val_2192_);
lean_dec(v_proof_x3f_2189_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2220_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; 
lean_inc(v_val_2191_);
v___x_2196_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_lhs_2169_, v_val_2191_, v_val_2192_, v_flipped_2190_, v_heq_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2198_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2196_, 1);
v___x_2198_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_acc_2171_, v_a_2197_, v_heq_2172_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2201_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref_known(v___x_2198_, 1);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v_a_2199_);
v___x_2201_ = v___x_2194_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2199_);
v___x_2201_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
v_lhs_2169_ = v_val_2191_;
v_acc_2171_ = v___x_2201_;
goto _start;
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_del_object(v___x_2194_);
lean_dec(v_val_2191_);
v_a_2204_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2198_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2198_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_del_object(v___x_2194_);
lean_dec(v_val_2191_);
lean_dec(v_acc_2171_);
v_a_2212_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2196_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2196_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
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
else
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
lean_dec(v_proof_x3f_2189_);
lean_dec_ref_known(v_target_x3f_2188_, 1);
lean_dec(v_a_2187_);
lean_dec(v_acc_2171_);
lean_dec_ref(v_lhs_2169_);
v___x_2221_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1);
v___x_2222_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2221_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
return v___x_2222_;
}
}
else
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
lean_dec(v_target_x3f_2188_);
lean_dec(v_a_2187_);
lean_dec(v_acc_2171_);
lean_dec_ref(v_lhs_2169_);
v___x_2223_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2);
v___x_2224_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2223_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
return v___x_2224_;
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec(v_acc_2171_);
lean_dec_ref(v_lhs_2169_);
v_a_2225_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2186_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2186_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
else
{
lean_object* v___x_2233_; 
lean_dec_ref(v_lhs_2169_);
v___x_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2233_, 0, v_acc_2171_);
return v___x_2233_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2235_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2236_ = lean_unsigned_to_nat(29u);
v___x_2237_ = lean_unsigned_to_nat(300u);
v___x_2238_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0));
v___x_2239_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2240_ = l_mkPanicMessageWithDecl(v___x_2239_, v___x_2238_, v___x_2237_, v___x_2236_, v___x_2235_);
return v___x_2240_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2241_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2242_ = lean_unsigned_to_nat(35u);
v___x_2243_ = lean_unsigned_to_nat(299u);
v___x_2244_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0));
v___x_2245_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2246_ = l_mkPanicMessageWithDecl(v___x_2245_, v___x_2244_, v___x_2243_, v___x_2242_, v___x_2241_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(lean_object* v_rhs_2247_, lean_object* v_common_2248_, lean_object* v_lhsEqCommon_x3f_2249_, uint8_t v_heq_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_){
_start:
{
uint8_t v___x_2262_; 
v___x_2262_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_rhs_2247_, v_common_2248_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = lean_st_ref_get(v_a_2251_);
lean_inc_ref(v_rhs_2247_);
v___x_2264_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2263_, v_rhs_2247_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
lean_dec(v___x_2263_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v_target_x3f_2266_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2264_, 1);
v_target_x3f_2266_ = lean_ctor_get(v_a_2265_, 4);
lean_inc(v_target_x3f_2266_);
if (lean_obj_tag(v_target_x3f_2266_) == 1)
{
lean_object* v_proof_x3f_2267_; 
v_proof_x3f_2267_ = lean_ctor_get(v_a_2265_, 5);
lean_inc(v_proof_x3f_2267_);
if (lean_obj_tag(v_proof_x3f_2267_) == 1)
{
uint8_t v_flipped_2268_; lean_object* v_val_2269_; lean_object* v_val_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2309_; 
v_flipped_2268_ = lean_ctor_get_uint8(v_a_2265_, sizeof(void*)*12);
lean_dec(v_a_2265_);
v_val_2269_ = lean_ctor_get(v_target_x3f_2266_, 0);
lean_inc(v_val_2269_);
lean_dec_ref_known(v_target_x3f_2266_, 1);
v_val_2270_ = lean_ctor_get(v_proof_x3f_2267_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_proof_x3f_2267_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2272_ = v_proof_x3f_2267_;
v_isShared_2273_ = v_isSharedCheck_2309_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_val_2270_);
lean_dec(v_proof_x3f_2267_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2309_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
uint8_t v___y_2275_; 
if (v_flipped_2268_ == 0)
{
uint8_t v___x_2308_; 
v___x_2308_ = 1;
v___y_2275_ = v___x_2308_;
goto v___jp_2274_;
}
else
{
v___y_2275_ = v___x_2262_;
goto v___jp_2274_;
}
v___jp_2274_:
{
lean_object* v___x_2276_; 
lean_inc(v_val_2269_);
v___x_2276_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_val_2269_, v_rhs_2247_, v_val_2270_, v___y_2275_, v_heq_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2278_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref_known(v___x_2276_, 1);
v___x_2278_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_val_2269_, v_common_2248_, v_lhsEqCommon_x3f_2249_, v_heq_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2280_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2278_, 1);
v___x_2280_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_a_2279_, v_a_2277_, v_heq_2250_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2291_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2283_ = v___x_2280_;
v_isShared_2284_ = v_isSharedCheck_2291_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2280_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2291_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v_a_2281_);
v___x_2286_ = v___x_2272_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
lean_object* v___x_2288_; 
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v___x_2286_);
v___x_2288_ = v___x_2283_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_del_object(v___x_2272_);
v_a_2292_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2280_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2280_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
else
{
lean_dec(v_a_2277_);
lean_del_object(v___x_2272_);
return v___x_2278_;
}
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
lean_del_object(v___x_2272_);
lean_dec(v_val_2269_);
lean_dec(v_lhsEqCommon_x3f_2249_);
v_a_2300_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2276_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2276_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
}
else
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
lean_dec_ref_known(v_target_x3f_2266_, 1);
lean_dec(v_proof_x3f_2267_);
lean_dec(v_a_2265_);
lean_dec(v_lhsEqCommon_x3f_2249_);
lean_dec_ref(v_rhs_2247_);
v___x_2310_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1);
v___x_2311_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2310_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
return v___x_2311_;
}
}
else
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
lean_dec(v_target_x3f_2266_);
lean_dec(v_a_2265_);
lean_dec(v_lhsEqCommon_x3f_2249_);
lean_dec_ref(v_rhs_2247_);
v___x_2312_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2);
v___x_2313_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2312_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
return v___x_2313_;
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec(v_lhsEqCommon_x3f_2249_);
lean_dec_ref(v_rhs_2247_);
v_a_2314_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2264_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2264_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
else
{
lean_object* v___x_2322_; 
lean_dec_ref(v_rhs_2247_);
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v_lhsEqCommon_x3f_2249_);
return v___x_2322_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3(void){
_start:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2323_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2324_ = lean_unsigned_to_nat(72u);
v___x_2325_ = lean_unsigned_to_nat(321u);
v___x_2326_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0));
v___x_2327_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2328_ = l_mkPanicMessageWithDecl(v___x_2327_, v___x_2326_, v___x_2325_, v___x_2324_, v___x_2323_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(lean_object* v_lhs_2329_, lean_object* v_rhs_2330_, uint8_t v_heq_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
uint8_t v___x_2343_; 
v___x_2343_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_lhs_2329_, v_rhs_2330_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; 
lean_inc_ref(v_lhs_2329_);
v___x_2344_ = l_Lean_Meta_Grind_getRootENode___redArg(v_lhs_2329_, v_a_2332_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_a_2345_);
lean_dec_ref_known(v___x_2344_, 1);
v___x_2346_ = lean_st_ref_get(v_a_2332_);
lean_inc_ref(v_lhs_2329_);
v___x_2347_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2346_, v_lhs_2329_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
lean_dec(v___x_2346_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
lean_dec_ref_known(v___x_2347_, 1);
v___x_2349_ = lean_st_ref_get(v_a_2332_);
lean_inc_ref(v_rhs_2330_);
v___x_2350_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2349_, v_rhs_2330_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
lean_dec(v___x_2349_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v_root_2352_; lean_object* v_root_2353_; uint8_t v___x_2354_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref_known(v___x_2350_, 1);
v_root_2352_ = lean_ctor_get(v_a_2348_, 2);
lean_inc_ref(v_root_2352_);
lean_dec(v_a_2348_);
v_root_2353_ = lean_ctor_get(v_a_2351_, 2);
lean_inc_ref(v_root_2353_);
lean_dec(v_a_2351_);
v___x_2354_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_root_2352_, v_root_2353_);
lean_dec_ref(v_root_2353_);
lean_dec_ref(v_root_2352_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
lean_dec(v_a_2345_);
lean_dec_ref(v_rhs_2330_);
lean_dec_ref(v_lhs_2329_);
v___x_2355_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2);
v___x_2356_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2355_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
return v___x_2356_;
}
else
{
lean_object* v___x_2357_; 
lean_inc_ref(v_rhs_2330_);
lean_inc_ref(v_lhs_2329_);
v___x_2357_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(v_lhs_2329_, v_rhs_2330_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; uint8_t v_heqProofs_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref_known(v___x_2357_, 1);
v_heqProofs_2359_ = lean_ctor_get_uint8(v_a_2345_, sizeof(void*)*12 + 4);
lean_dec(v_a_2345_);
v___x_2360_ = lean_box(0);
v___x_2361_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_2329_, v_a_2358_, v___x_2360_, v_heqProofs_2359_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_2330_, v_a_2358_, v_a_2362_, v_heqProofs_2359_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
lean_dec(v_a_2358_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2379_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2366_ = v___x_2363_;
v_isShared_2367_ = v_isSharedCheck_2379_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2363_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2379_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
if (lean_obj_tag(v_a_2364_) == 1)
{
lean_object* v_val_2368_; uint8_t v___y_2373_; 
v_val_2368_ = lean_ctor_get(v_a_2364_, 0);
lean_inc(v_val_2368_);
lean_dec_ref_known(v_a_2364_, 1);
if (v_heq_2331_ == 0)
{
if (v_heqProofs_2359_ == 0)
{
v___y_2373_ = v___x_2354_;
goto v___jp_2372_;
}
else
{
lean_del_object(v___x_2366_);
goto v___jp_2369_;
}
}
else
{
v___y_2373_ = v_heqProofs_2359_;
goto v___jp_2372_;
}
v___jp_2369_:
{
if (v_heq_2331_ == 0)
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Lean_Meta_mkEqOfHEq(v_val_2368_, v_heq_2331_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
return v___x_2370_;
}
else
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_Meta_mkHEqOfEq(v_val_2368_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
return v___x_2371_;
}
}
v___jp_2372_:
{
if (v___y_2373_ == 0)
{
lean_del_object(v___x_2366_);
goto v___jp_2369_;
}
else
{
lean_object* v___x_2375_; 
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v_val_2368_);
v___x_2375_ = v___x_2366_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_val_2368_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
else
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
lean_del_object(v___x_2366_);
lean_dec(v_a_2364_);
v___x_2377_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3);
v___x_2378_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2377_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
return v___x_2378_;
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
v_a_2380_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2363_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2363_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
lean_dec(v_a_2358_);
lean_dec_ref(v_rhs_2330_);
v_a_2388_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2361_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2361_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
else
{
lean_dec(v_a_2345_);
lean_dec_ref(v_rhs_2330_);
lean_dec_ref(v_lhs_2329_);
return v___x_2357_;
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_dec(v_a_2348_);
lean_dec(v_a_2345_);
lean_dec_ref(v_rhs_2330_);
lean_dec_ref(v_lhs_2329_);
v_a_2396_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2350_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2350_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec(v_a_2345_);
lean_dec_ref(v_rhs_2330_);
lean_dec_ref(v_lhs_2329_);
v_a_2404_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2347_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2347_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec_ref(v_rhs_2330_);
lean_dec_ref(v_lhs_2329_);
v_a_2412_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2344_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2344_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
else
{
lean_object* v___x_2420_; 
lean_dec_ref(v_rhs_2330_);
v___x_2420_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(v_lhs_2329_, v_heq_2331_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
return v___x_2420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(lean_object* v_thm_2421_, lean_object* v_lhs_2422_, lean_object* v_rhs_2423_, lean_object* v_i_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v___x_2436_; uint8_t v___x_2437_; 
v___x_2436_ = lean_unsigned_to_nat(0u);
v___x_2437_ = lean_nat_dec_lt(v___x_2436_, v_i_2424_);
if (v___x_2437_ == 0)
{
lean_object* v_proof_2438_; lean_object* v___x_2439_; 
v_proof_2438_ = lean_ctor_get(v_thm_2421_, 1);
lean_inc_ref(v_proof_2438_);
v___x_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2439_, 0, v_proof_2438_);
return v___x_2439_;
}
else
{
lean_object* v___x_2440_; lean_object* v_i_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2440_ = lean_unsigned_to_nat(1u);
v_i_2441_ = lean_nat_sub(v_i_2424_, v___x_2440_);
v___x_2442_ = l_Lean_Expr_appFn_x21(v_lhs_2422_);
v___x_2443_ = l_Lean_Expr_appFn_x21(v_rhs_2423_);
v___x_2444_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_2421_, v___x_2442_, v___x_2443_, v_i_2441_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
lean_dec_ref(v___x_2443_);
lean_dec_ref(v___x_2442_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v_argKinds_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; uint8_t v___y_2450_; uint8_t v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
lean_inc(v_a_2445_);
lean_dec_ref_known(v___x_2444_, 1);
v_argKinds_2446_ = lean_ctor_get(v_thm_2421_, 2);
v___x_2447_ = l_Lean_Expr_appArg_x21(v_lhs_2422_);
v___x_2448_ = l_Lean_Expr_appArg_x21(v_rhs_2423_);
v___x_2461_ = 0;
v___x_2462_ = lean_box(v___x_2461_);
v___x_2463_ = lean_array_get(v___x_2462_, v_argKinds_2446_, v_i_2441_);
lean_dec(v_i_2441_);
lean_dec(v___x_2462_);
v___x_2464_ = lean_unbox(v___x_2463_);
lean_dec(v___x_2463_);
if (v___x_2464_ == 4)
{
v___y_2450_ = v___x_2437_;
goto v___jp_2449_;
}
else
{
uint8_t v___x_2465_; 
v___x_2465_ = 0;
v___y_2450_ = v___x_2465_;
goto v___jp_2449_;
}
v___jp_2449_:
{
lean_object* v___x_2451_; 
lean_inc_ref(v___x_2448_);
lean_inc_ref(v___x_2447_);
v___x_2451_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___x_2447_, v___x_2448_, v___y_2450_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2460_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2454_ = v___x_2451_;
v_isShared_2455_ = v_isSharedCheck_2460_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2451_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2460_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2456_; lean_object* v___x_2458_; 
v___x_2456_ = l_Lean_mkApp3(v_a_2445_, v___x_2447_, v___x_2448_, v_a_2452_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v___x_2456_);
v___x_2458_ = v___x_2454_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v___x_2456_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
else
{
lean_dec_ref(v___x_2448_);
lean_dec_ref(v___x_2447_);
lean_dec(v_a_2445_);
return v___x_2451_;
}
}
}
else
{
lean_dec(v_i_2441_);
return v___x_2444_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(lean_object* v_f_2469_, lean_object* v_g_2470_, lean_object* v_numArgs_2471_, lean_object* v_lhs_2472_, lean_object* v_rhs_2473_, uint8_t v_heq_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_){
_start:
{
lean_object* v___x_2486_; 
lean_inc(v_numArgs_2471_);
lean_inc_ref(v_f_2469_);
v___x_2486_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(v_f_2469_, v_numArgs_2471_, v_a_2478_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v_argKinds_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2487_);
lean_dec_ref_known(v___x_2486_, 1);
v_argKinds_2488_ = lean_ctor_get(v_a_2487_, 2);
v___x_2489_ = lean_array_get_size(v_argKinds_2488_);
v___x_2490_ = lean_nat_dec_eq(v___x_2489_, v_numArgs_2471_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
lean_dec(v_a_2487_);
lean_dec_ref(v_rhs_2473_);
lean_dec_ref(v_lhs_2472_);
lean_dec(v_numArgs_2471_);
lean_dec_ref(v_g_2470_);
lean_dec_ref(v_f_2469_);
v___x_2491_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2);
v___x_2492_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2491_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
return v___x_2492_;
}
else
{
lean_object* v___x_2493_; 
v___x_2493_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_2487_, v_lhs_2472_, v_rhs_2473_, v_numArgs_2471_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
lean_dec(v_a_2487_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; uint8_t v___x_2495_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___x_2493_, 1);
v___x_2495_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_f_2469_, v_g_2470_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__4));
v___x_2497_ = l_Lean_Core_mkFreshUserName(v___x_2496_, v_a_2483_, v_a_2484_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2499_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2497_, 1);
lean_inc(v_a_2484_);
lean_inc_ref(v_a_2483_);
lean_inc(v_a_2482_);
lean_inc_ref(v_a_2481_);
lean_inc_ref(v_f_2469_);
v___x_2499_ = lean_infer_type(v_f_2469_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___f_2503_; lean_object* v___x_2504_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2500_);
lean_dec_ref_known(v___x_2499_, 1);
v___x_2501_ = lean_box(v___x_2495_);
v___x_2502_ = lean_box(v___x_2490_);
v___f_2503_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___boxed), 17, 5);
lean_closure_set(v___f_2503_, 0, v_numArgs_2471_);
lean_closure_set(v___f_2503_, 1, v_rhs_2473_);
lean_closure_set(v___f_2503_, 2, v_lhs_2472_);
lean_closure_set(v___f_2503_, 3, v___x_2501_);
lean_closure_set(v___f_2503_, 4, v___x_2502_);
v___x_2504_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_a_2498_, v_a_2500_, v___f_2503_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2506_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2504_, 1);
v___x_2506_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_f_2469_, v_g_2470_, v___x_2495_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v___x_2508_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_a_2507_);
lean_dec_ref_known(v___x_2506_, 1);
v___x_2508_ = l_Lean_Meta_mkEqNDRec(v_a_2505_, v_a_2494_, v_a_2507_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2510_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2509_);
lean_dec_ref_known(v___x_2508_, 1);
v___x_2510_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_2509_, v_heq_2474_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
return v___x_2510_;
}
else
{
return v___x_2508_;
}
}
else
{
lean_dec(v_a_2505_);
lean_dec(v_a_2494_);
return v___x_2506_;
}
}
else
{
lean_dec(v_a_2494_);
lean_dec_ref(v_g_2470_);
lean_dec_ref(v_f_2469_);
return v___x_2504_;
}
}
else
{
lean_dec(v_a_2498_);
lean_dec(v_a_2494_);
lean_dec_ref(v_rhs_2473_);
lean_dec_ref(v_lhs_2472_);
lean_dec(v_numArgs_2471_);
lean_dec_ref(v_g_2470_);
lean_dec_ref(v_f_2469_);
return v___x_2499_;
}
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2518_; 
lean_dec(v_a_2494_);
lean_dec_ref(v_rhs_2473_);
lean_dec_ref(v_lhs_2472_);
lean_dec(v_numArgs_2471_);
lean_dec_ref(v_g_2470_);
lean_dec_ref(v_f_2469_);
v_a_2511_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2513_ = v___x_2497_;
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2497_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2516_; 
if (v_isShared_2514_ == 0)
{
v___x_2516_ = v___x_2513_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2511_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
else
{
lean_object* v___x_2519_; 
lean_dec_ref(v_rhs_2473_);
lean_dec_ref(v_lhs_2472_);
lean_dec(v_numArgs_2471_);
lean_dec_ref(v_g_2470_);
lean_dec_ref(v_f_2469_);
v___x_2519_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_2494_, v_heq_2474_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
return v___x_2519_;
}
}
else
{
lean_dec_ref(v_rhs_2473_);
lean_dec_ref(v_lhs_2472_);
lean_dec(v_numArgs_2471_);
lean_dec_ref(v_g_2470_);
lean_dec_ref(v_f_2469_);
return v___x_2493_;
}
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec_ref(v_rhs_2473_);
lean_dec_ref(v_lhs_2472_);
lean_dec(v_numArgs_2471_);
lean_dec_ref(v_g_2470_);
lean_dec_ref(v_f_2469_);
v_a_2520_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2486_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2486_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1(void){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2529_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2530_ = lean_unsigned_to_nat(27u);
v___x_2531_ = lean_unsigned_to_nat(237u);
v___x_2532_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0));
v___x_2533_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2534_ = l_mkPanicMessageWithDecl(v___x_2533_, v___x_2532_, v___x_2531_, v___x_2530_, v___x_2529_);
return v___x_2534_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2(void){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2535_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2536_ = lean_unsigned_to_nat(27u);
v___x_2537_ = lean_unsigned_to_nat(236u);
v___x_2538_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0));
v___x_2539_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2540_ = l_mkPanicMessageWithDecl(v___x_2539_, v___x_2538_, v___x_2537_, v___x_2536_, v___x_2535_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(lean_object* v_lhs_2541_, lean_object* v_rhs_2542_, uint8_t v_heq_2543_, lean_object* v_e_u2081_2544_, lean_object* v_e_u2082_2545_, lean_object* v_numArgs_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
if (lean_obj_tag(v_e_u2081_2544_) == 5)
{
if (lean_obj_tag(v_e_u2082_2545_) == 5)
{
lean_object* v_fn_2558_; lean_object* v_fn_2559_; lean_object* v___x_2560_; lean_object* v_numArgs_2561_; uint8_t v___x_2562_; 
v_fn_2558_ = lean_ctor_get(v_e_u2081_2544_, 0);
lean_inc_ref(v_fn_2558_);
lean_dec_ref_known(v_e_u2081_2544_, 2);
v_fn_2559_ = lean_ctor_get(v_e_u2082_2545_, 0);
lean_inc_ref(v_fn_2559_);
lean_dec_ref_known(v_e_u2082_2545_, 2);
v___x_2560_ = lean_unsigned_to_nat(1u);
v_numArgs_2561_ = lean_nat_add(v_numArgs_2546_, v___x_2560_);
lean_dec(v_numArgs_2546_);
v___x_2562_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_2558_, v_fn_2559_);
if (v___x_2562_ == 0)
{
lean_object* v___x_2563_; 
lean_inc_ref(v_fn_2559_);
lean_inc_ref(v_fn_2558_);
v___x_2563_ = l_Lean_Meta_Grind_hasSameType(v_fn_2558_, v_fn_2559_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; uint8_t v___x_2565_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_a_2564_);
lean_dec_ref_known(v___x_2563_, 1);
v___x_2565_ = lean_unbox(v_a_2564_);
lean_dec(v_a_2564_);
if (v___x_2565_ == 0)
{
v_e_u2081_2544_ = v_fn_2558_;
v_e_u2082_2545_ = v_fn_2559_;
v_numArgs_2546_ = v_numArgs_2561_;
goto _start;
}
else
{
lean_object* v___x_2567_; 
v___x_2567_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_2558_, v_fn_2559_, v_numArgs_2561_, v_lhs_2541_, v_rhs_2542_, v_heq_2543_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
return v___x_2567_;
}
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_dec(v_numArgs_2561_);
lean_dec_ref(v_fn_2559_);
lean_dec_ref(v_fn_2558_);
lean_dec_ref(v_rhs_2542_);
lean_dec_ref(v_lhs_2541_);
v_a_2568_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2563_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2563_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
else
{
lean_object* v___x_2576_; 
v___x_2576_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_2558_, v_fn_2559_, v_numArgs_2561_, v_lhs_2541_, v_rhs_2542_, v_heq_2543_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
return v___x_2576_;
}
}
else
{
lean_object* v___x_2577_; lean_object* v___x_2578_; 
lean_dec_ref_known(v_e_u2081_2544_, 2);
lean_dec(v_numArgs_2546_);
lean_dec_ref(v_e_u2082_2545_);
lean_dec_ref(v_rhs_2542_);
lean_dec_ref(v_lhs_2541_);
v___x_2577_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1);
v___x_2578_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2577_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
return v___x_2578_;
}
}
else
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_dec(v_numArgs_2546_);
lean_dec_ref(v_e_u2082_2545_);
lean_dec_ref(v_e_u2081_2544_);
lean_dec_ref(v_rhs_2542_);
lean_dec_ref(v_lhs_2541_);
v___x_2579_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2);
v___x_2580_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2579_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
return v___x_2580_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(lean_object* v_lhs_2581_, lean_object* v_rhs_2582_, uint8_t v_heq_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2595_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_rhs_2582_);
lean_inc_ref(v_lhs_2581_);
v___x_2596_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(v_lhs_2581_, v_rhs_2582_, v_heq_2583_, v_lhs_2581_, v_rhs_2582_, v___x_2595_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC___boxed(lean_object* v_lhs_2597_, lean_object* v_rhs_2598_, lean_object* v_heq_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
uint8_t v_heq_boxed_2611_; lean_object* v_res_2612_; 
v_heq_boxed_2611_ = lean_unbox(v_heq_2599_);
v_res_2612_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_2597_, v_rhs_2598_, v_heq_boxed_2611_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_);
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
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___boxed(lean_object* v_lhs_2613_, lean_object* v_rhs_2614_, lean_object* v_heq_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_){
_start:
{
uint8_t v_heq_boxed_2627_; lean_object* v_res_2628_; 
v_heq_boxed_2627_ = lean_unbox(v_heq_2615_);
v_res_2628_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_2613_, v_rhs_2614_, v_heq_boxed_2627_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_);
lean_dec(v_a_2625_);
lean_dec_ref(v_a_2624_);
lean_dec(v_a_2623_);
lean_dec_ref(v_a_2622_);
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec(v_a_2619_);
lean_dec_ref(v_a_2618_);
lean_dec(v_a_2617_);
lean_dec(v_a_2616_);
lean_dec_ref(v_rhs_2614_);
lean_dec_ref(v_lhs_2613_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___boxed(lean_object* v_lhs_2629_, lean_object* v_rhs_2630_, lean_object* v_heq_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
uint8_t v_heq_boxed_2643_; lean_object* v_res_2644_; 
v_heq_boxed_2643_ = lean_unbox(v_heq_2631_);
v_res_2644_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_2629_, v_rhs_2630_, v_heq_boxed_2643_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
lean_dec(v_a_2639_);
lean_dec_ref(v_a_2638_);
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_a_2635_);
lean_dec_ref(v_a_2634_);
lean_dec(v_a_2633_);
lean_dec(v_a_2632_);
lean_dec_ref(v_rhs_2630_);
lean_dec_ref(v_lhs_2629_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof___boxed(lean_object* v_lhs_2645_, lean_object* v_rhs_2646_, lean_object* v_h_2647_, lean_object* v_flipped_2648_, lean_object* v_heq_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
uint8_t v_flipped_boxed_2661_; uint8_t v_heq_boxed_2662_; lean_object* v_res_2663_; 
v_flipped_boxed_2661_ = lean_unbox(v_flipped_2648_);
v_heq_boxed_2662_ = lean_unbox(v_heq_2649_);
v_res_2663_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_lhs_2645_, v_rhs_2646_, v_h_2647_, v_flipped_boxed_2661_, v_heq_boxed_2662_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
lean_dec(v_a_2651_);
lean_dec(v_a_2650_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___boxed(lean_object* v_lhs_2664_, lean_object* v_rhs_2665_, lean_object* v_heq_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_){
_start:
{
uint8_t v_heq_boxed_2678_; lean_object* v_res_2679_; 
v_heq_boxed_2678_ = lean_unbox(v_heq_2666_);
v_res_2679_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_2664_, v_rhs_2665_, v_heq_boxed_2678_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_);
lean_dec(v_a_2676_);
lean_dec_ref(v_a_2675_);
lean_dec(v_a_2674_);
lean_dec_ref(v_a_2673_);
lean_dec(v_a_2672_);
lean_dec_ref(v_a_2671_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
lean_dec(v_a_2668_);
lean_dec(v_a_2667_);
lean_dec_ref(v_rhs_2665_);
lean_dec_ref(v_lhs_2664_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper___boxed(lean_object* v_thm_2680_, lean_object* v_lhs_2681_, lean_object* v_rhs_2682_, lean_object* v_i_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_2680_, v_lhs_2681_, v_rhs_2682_, v_i_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
lean_dec(v_a_2684_);
lean_dec(v_i_2683_);
lean_dec_ref(v_rhs_2682_);
lean_dec_ref(v_lhs_2681_);
lean_dec_ref(v_thm_2680_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___boxed(lean_object** _args){
lean_object* v_lhs_2696_ = _args[0];
lean_object* v_rhs_2697_ = _args[1];
lean_object* v_heq_2698_ = _args[2];
lean_object* v_e_u2081_2699_ = _args[3];
lean_object* v_e_u2082_2700_ = _args[4];
lean_object* v_numArgs_2701_ = _args[5];
lean_object* v_a_2702_ = _args[6];
lean_object* v_a_2703_ = _args[7];
lean_object* v_a_2704_ = _args[8];
lean_object* v_a_2705_ = _args[9];
lean_object* v_a_2706_ = _args[10];
lean_object* v_a_2707_ = _args[11];
lean_object* v_a_2708_ = _args[12];
lean_object* v_a_2709_ = _args[13];
lean_object* v_a_2710_ = _args[14];
lean_object* v_a_2711_ = _args[15];
lean_object* v_a_2712_ = _args[16];
_start:
{
uint8_t v_heq_boxed_2713_; lean_object* v_res_2714_; 
v_heq_boxed_2713_ = lean_unbox(v_heq_2698_);
v_res_2714_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(v_lhs_2696_, v_rhs_2697_, v_heq_boxed_2713_, v_e_u2081_2699_, v_e_u2082_2700_, v_numArgs_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
lean_dec(v_a_2707_);
lean_dec_ref(v_a_2706_);
lean_dec(v_a_2705_);
lean_dec_ref(v_a_2704_);
lean_dec(v_a_2703_);
lean_dec(v_a_2702_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___boxed(lean_object* v_lhs_2715_, lean_object* v_common_2716_, lean_object* v_acc_2717_, lean_object* v_heq_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_){
_start:
{
uint8_t v_heq_boxed_2730_; lean_object* v_res_2731_; 
v_heq_boxed_2730_ = lean_unbox(v_heq_2718_);
v_res_2731_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_2715_, v_common_2716_, v_acc_2717_, v_heq_boxed_2730_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
lean_dec(v_a_2728_);
lean_dec_ref(v_a_2727_);
lean_dec(v_a_2726_);
lean_dec_ref(v_a_2725_);
lean_dec(v_a_2724_);
lean_dec_ref(v_a_2723_);
lean_dec(v_a_2722_);
lean_dec_ref(v_a_2721_);
lean_dec(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_common_2716_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___boxed(lean_object** _args){
lean_object* v_f_2732_ = _args[0];
lean_object* v_g_2733_ = _args[1];
lean_object* v_numArgs_2734_ = _args[2];
lean_object* v_lhs_2735_ = _args[3];
lean_object* v_rhs_2736_ = _args[4];
lean_object* v_heq_2737_ = _args[5];
lean_object* v_a_2738_ = _args[6];
lean_object* v_a_2739_ = _args[7];
lean_object* v_a_2740_ = _args[8];
lean_object* v_a_2741_ = _args[9];
lean_object* v_a_2742_ = _args[10];
lean_object* v_a_2743_ = _args[11];
lean_object* v_a_2744_ = _args[12];
lean_object* v_a_2745_ = _args[13];
lean_object* v_a_2746_ = _args[14];
lean_object* v_a_2747_ = _args[15];
lean_object* v_a_2748_ = _args[16];
_start:
{
uint8_t v_heq_boxed_2749_; lean_object* v_res_2750_; 
v_heq_boxed_2749_ = lean_unbox(v_heq_2737_);
v_res_2750_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_2732_, v_g_2733_, v_numArgs_2734_, v_lhs_2735_, v_rhs_2736_, v_heq_boxed_2749_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
lean_dec(v_a_2747_);
lean_dec_ref(v_a_2746_);
lean_dec(v_a_2745_);
lean_dec_ref(v_a_2744_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
lean_dec(v_a_2741_);
lean_dec_ref(v_a_2740_);
lean_dec(v_a_2739_);
lean_dec(v_a_2738_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___boxed(lean_object* v_rhs_2751_, lean_object* v_common_2752_, lean_object* v_lhsEqCommon_x3f_2753_, lean_object* v_heq_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_){
_start:
{
uint8_t v_heq_boxed_2766_; lean_object* v_res_2767_; 
v_heq_boxed_2766_ = lean_unbox(v_heq_2754_);
v_res_2767_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_2751_, v_common_2752_, v_lhsEqCommon_x3f_2753_, v_heq_boxed_2766_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_);
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
lean_dec_ref(v_common_2752_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop___boxed(lean_object* v_lhs_2768_, lean_object* v_rhs_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_2768_, v_rhs_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
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
lean_dec_ref(v_rhs_2769_);
lean_dec_ref(v_lhs_2768_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___boxed(lean_object* v_lhs_2782_, lean_object* v_rhs_2783_, lean_object* v_heq_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_){
_start:
{
uint8_t v_heq_boxed_2796_; lean_object* v_res_2797_; 
v_heq_boxed_2796_ = lean_unbox(v_heq_2784_);
v_res_2797_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_2782_, v_rhs_2783_, v_heq_boxed_2796_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_);
lean_dec(v_a_2794_);
lean_dec_ref(v_a_2793_);
lean_dec(v_a_2792_);
lean_dec_ref(v_a_2791_);
lean_dec(v_a_2790_);
lean_dec_ref(v_a_2789_);
lean_dec(v_a_2788_);
lean_dec_ref(v_a_2787_);
lean_dec(v_a_2786_);
lean_dec(v_a_2785_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___boxed(lean_object* v_lhs_2798_, lean_object* v_rhs_2799_, lean_object* v_heq_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_){
_start:
{
uint8_t v_heq_boxed_2812_; lean_object* v_res_2813_; 
v_heq_boxed_2812_ = lean_unbox(v_heq_2800_);
v_res_2813_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_lhs_2798_, v_rhs_2799_, v_heq_boxed_2812_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrProof___boxed(lean_object* v_lhs_2814_, lean_object* v_rhs_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_){
_start:
{
lean_object* v_res_2827_; 
v_res_2827_ = l_Lean_Meta_Grind_mkEqCongrProof(v_lhs_2814_, v_rhs_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_);
lean_dec(v_a_2825_);
lean_dec_ref(v_a_2824_);
lean_dec(v_a_2823_);
lean_dec_ref(v_a_2822_);
lean_dec(v_a_2821_);
lean_dec_ref(v_a_2820_);
lean_dec(v_a_2819_);
lean_dec_ref(v_a_2818_);
lean_dec(v_a_2817_);
lean_dec(v_a_2816_);
return v_res_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___boxed(lean_object* v_lhs_2828_, lean_object* v_rhs_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(v_lhs_2828_, v_rhs_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_);
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
lean_dec(v_a_2830_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___boxed(lean_object* v_lhs_2842_, lean_object* v_rhs_2843_, lean_object* v_heq_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_){
_start:
{
uint8_t v_heq_boxed_2856_; lean_object* v_res_2857_; 
v_heq_boxed_2856_ = lean_unbox(v_heq_2844_);
v_res_2857_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(v_lhs_2842_, v_rhs_2843_, v_heq_boxed_2856_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_);
lean_dec(v_a_2854_);
lean_dec_ref(v_a_2853_);
lean_dec(v_a_2852_);
lean_dec_ref(v_a_2851_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
lean_dec(v_a_2846_);
lean_dec(v_a_2845_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(lean_object* v_00_u03b1_2858_, lean_object* v_ref_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_2859_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___boxed(lean_object* v_00_u03b1_2872_, lean_object* v_ref_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(v_00_u03b1_2872_, v_ref_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec(v___y_2874_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(lean_object* v_00_u03b1_2886_, lean_object* v_name_2887_, uint8_t v_bi_2888_, lean_object* v_type_2889_, lean_object* v_k_2890_, uint8_t v_kind_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v___x_2903_; 
v___x_2903_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_2887_, v_bi_2888_, v_type_2889_, v_k_2890_, v_kind_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
return v___x_2903_;
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(lean_object* v_00_u03b1_2924_, lean_object* v_name_2925_, lean_object* v_type_2926_, lean_object* v_k_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_name_2925_, v_type_2926_, v_k_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___boxed(lean_object* v_00_u03b1_2940_, lean_object* v_name_2941_, lean_object* v_type_2942_, lean_object* v_k_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(v_00_u03b1_2940_, v_name_2941_, v_type_2942_, v_k_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec(v___y_2944_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(lean_object* v_00_u03b1_2956_, lean_object* v_msg_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v_msg_2957_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___boxed(lean_object* v_00_u03b1_2970_, lean_object* v_msg_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(v_00_u03b1_2970_, v_msg_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec(v___y_2972_);
return v_res_2983_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__1(void){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__0));
v___x_2986_ = l_Lean_stringToMessageData(v___x_2985_);
return v___x_2986_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__3(void){
_start:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__2));
v___x_2989_ = l_Lean_stringToMessageData(v___x_2988_);
return v___x_2989_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__5(void){
_start:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__4));
v___x_2992_ = l_Lean_stringToMessageData(v___x_2991_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* lean_grind_mk_eq_proof(lean_object* v_a_2993_, lean_object* v_b_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_){
_start:
{
lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___x_3019_; 
lean_inc_ref(v_b_2994_);
lean_inc_ref(v_a_2993_);
v___x_3019_ = l_Lean_Meta_Grind_hasSameType(v_a_2993_, v_b_2994_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; uint8_t v___x_3021_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref_known(v___x_3019_, 1);
v___x_3021_ = lean_unbox(v_a_3020_);
lean_dec(v_a_3020_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; 
lean_dec(v_a_3000_);
lean_dec_ref(v_a_2999_);
lean_dec(v_a_2998_);
lean_dec_ref(v_a_2997_);
lean_dec(v_a_2996_);
lean_dec(v_a_2995_);
lean_inc(v_a_3004_);
lean_inc_ref(v_a_3003_);
lean_inc(v_a_3002_);
lean_inc_ref(v_a_3001_);
lean_inc_ref(v_a_2993_);
v___x_3022_ = lean_infer_type(v_a_2993_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v___x_3024_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref_known(v___x_3022_, 1);
lean_inc(v_a_3004_);
lean_inc_ref(v_a_3003_);
lean_inc(v_a_3002_);
lean_inc_ref(v_a_3001_);
lean_inc_ref(v_b_2994_);
v___x_3024_ = lean_infer_type(v_b_2994_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
v___x_3026_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__1, &l_Lean_Meta_Grind_mkEqProofImpl___closed__1_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__1);
v___x_3027_ = l_Lean_indentExpr(v_a_2993_);
v___x_3028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3026_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
v___x_3029_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__3, &l_Lean_Meta_Grind_mkEqProofImpl___closed__3_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__3);
v___x_3030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3028_);
lean_ctor_set(v___x_3030_, 1, v___x_3029_);
v___x_3031_ = l_Lean_indentExpr(v_a_3023_);
v___x_3032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3030_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__5, &l_Lean_Meta_Grind_mkEqProofImpl___closed__5_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__5);
v___x_3034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3032_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
v___x_3035_ = l_Lean_indentExpr(v_b_2994_);
v___x_3036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3034_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
v___x_3037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
lean_ctor_set(v___x_3037_, 1, v___x_3029_);
v___x_3038_ = l_Lean_indentExpr(v_a_3025_);
v___x_3039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3037_);
lean_ctor_set(v___x_3039_, 1, v___x_3038_);
v___x_3040_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v___x_3039_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_3040_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3040_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
else
{
lean_dec(v_a_3023_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec_ref(v_b_2994_);
lean_dec_ref(v_a_2993_);
return v___x_3024_;
}
}
else
{
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec_ref(v_b_2994_);
lean_dec_ref(v_a_2993_);
return v___x_3022_;
}
}
else
{
v___y_3007_ = v_a_2995_;
v___y_3008_ = v_a_2996_;
v___y_3009_ = v_a_2997_;
v___y_3010_ = v_a_2998_;
v___y_3011_ = v_a_2999_;
v___y_3012_ = v_a_3000_;
v___y_3013_ = v_a_3001_;
v___y_3014_ = v_a_3002_;
v___y_3015_ = v_a_3003_;
v___y_3016_ = v_a_3004_;
goto v___jp_3006_;
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec(v_a_3000_);
lean_dec_ref(v_a_2999_);
lean_dec(v_a_2998_);
lean_dec_ref(v_a_2997_);
lean_dec(v_a_2996_);
lean_dec(v_a_2995_);
lean_dec_ref(v_b_2994_);
lean_dec_ref(v_a_2993_);
v_a_3049_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_3019_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3019_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
v___jp_3006_:
{
uint8_t v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = 0;
v___x_3018_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_2993_, v_b_2994_, v___x_3017_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3007_);
return v___x_3018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqProofImpl___boxed(lean_object* v_a_3057_, lean_object* v_b_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = lean_grind_mk_eq_proof(v_a_3057_, v_b_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* lean_grind_mk_heq_proof(lean_object* v_a_3071_, lean_object* v_b_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_){
_start:
{
uint8_t v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = 1;
v___x_3085_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_3071_, v_b_3072_, v___x_3084_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
lean_dec(v_a_3082_);
lean_dec_ref(v_a_3081_);
lean_dec(v_a_3080_);
lean_dec_ref(v_a_3079_);
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3077_);
lean_dec(v_a_3076_);
lean_dec_ref(v_a_3075_);
lean_dec(v_a_3074_);
lean_dec(v_a_3073_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHEqProofImpl___boxed(lean_object* v_a_3086_, lean_object* v_b_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = lean_grind_mk_heq_proof(v_a_3086_, v_b_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_);
return v_res_3099_;
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
