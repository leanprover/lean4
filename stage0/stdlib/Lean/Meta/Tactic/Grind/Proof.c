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
lean_object* v___x_981_; lean_object* v___x_126590__overap_982_; lean_object* v___x_983_; 
v___x_981_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0);
v___x_126590__overap_982_ = lean_panic_fn_borrowed(v___x_981_, v_msg_969_);
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
v___x_983_ = lean_apply_11(v___x_126590__overap_982_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, lean_box(0));
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
uint8_t v___x_134518__boxed_1169_; uint8_t v___x_134519__boxed_1170_; lean_object* v_res_1171_; 
v___x_134518__boxed_1169_ = lean_unbox(v___x_1155_);
v___x_134519__boxed_1170_ = lean_unbox(v___x_1156_);
v_res_1171_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0(v_numArgs_1152_, v_rhs_1153_, v_lhs_1154_, v___x_134518__boxed_1169_, v___x_134519__boxed_1170_, v_x_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
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
lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; uint8_t v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; uint8_t v___y_1361_; lean_object* v_fileName_1397_; lean_object* v_fileMap_1398_; lean_object* v_options_1399_; lean_object* v_currRecDepth_1400_; lean_object* v_maxRecDepth_1401_; lean_object* v_ref_1402_; lean_object* v_currNamespace_1403_; lean_object* v_openDecls_1404_; lean_object* v_initHeartbeats_1405_; lean_object* v_maxHeartbeats_1406_; lean_object* v_quotContext_1407_; lean_object* v_currMacroScope_1408_; uint8_t v_diag_1409_; lean_object* v_cancelTk_x3f_1410_; uint8_t v_suppressElabErrors_1411_; lean_object* v_inheritedTraceOptions_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
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
lean_dec_ref(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec_ref(v___y_1352_);
v___x_1362_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4);
v___x_1363_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1362_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v___y_1360_, v_a_1323_);
lean_dec_ref(v___y_1360_);
return v___x_1363_;
}
else
{
lean_object* v___x_1364_; size_t v___x_1365_; size_t v___x_1366_; uint8_t v___x_1367_; 
v___x_1364_ = l_Lean_Expr_constLevels_x21(v___y_1355_);
lean_dec_ref(v___y_1355_);
v___x_1365_ = lean_ptr_addr(v___y_1357_);
v___x_1366_ = lean_ptr_addr(v___y_1358_);
v___x_1367_ = lean_usize_dec_eq(v___x_1365_, v___x_1366_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; 
lean_inc_ref(v___y_1359_);
lean_inc_ref(v___y_1352_);
v___x_1368_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1352_, v___y_1359_, v___y_1356_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v___y_1360_, v_a_1323_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1370_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1368_, 1);
lean_inc_ref(v___y_1353_);
lean_inc_ref(v___y_1354_);
v___x_1370_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1354_, v___y_1353_, v___y_1356_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v___y_1360_, v_a_1323_);
lean_dec_ref(v___y_1360_);
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
v___x_1377_ = l_Lean_mkApp8(v___x_1376_, v___y_1357_, v___y_1358_, v___y_1352_, v___y_1354_, v___y_1353_, v___y_1359_, v_a_1369_, v_a_1371_);
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
lean_dec_ref(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec_ref(v___y_1352_);
return v___x_1370_;
}
}
else
{
lean_dec(v___x_1364_);
lean_dec_ref(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec_ref(v___y_1352_);
return v___x_1368_;
}
}
else
{
uint8_t v___x_1382_; lean_object* v___x_1383_; 
lean_dec_ref(v___y_1358_);
v___x_1382_ = 0;
lean_inc_ref(v___y_1359_);
lean_inc_ref(v___y_1352_);
v___x_1383_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1352_, v___y_1359_, v___x_1382_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v___y_1360_, v_a_1323_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1385_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1383_, 1);
lean_inc_ref(v___y_1353_);
lean_inc_ref(v___y_1354_);
v___x_1385_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1354_, v___y_1353_, v___x_1382_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v___y_1360_, v_a_1323_);
lean_dec_ref(v___y_1360_);
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
v___x_1392_ = l_Lean_mkApp7(v___x_1391_, v___y_1357_, v___y_1352_, v___y_1354_, v___y_1353_, v___y_1359_, v_a_1384_, v_a_1386_);
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
lean_dec_ref(v___y_1359_);
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1353_);
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
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec_ref(v___y_1352_);
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
v___y_1352_ = v_arg_1422_;
v___y_1353_ = v_arg_1434_;
v___y_1354_ = v_arg_1419_;
v___y_1355_ = v___x_1426_;
v___y_1356_ = v___x_1439_;
v___y_1357_ = v_arg_1425_;
v___y_1358_ = v_arg_1437_;
v___y_1359_ = v_arg_1431_;
v___y_1360_ = v___x_1418_;
v___y_1361_ = v___x_1442_;
goto v___jp_1351_;
}
else
{
uint8_t v___x_1443_; 
v___x_1443_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1441_, v_arg_1419_, v_arg_1434_);
lean_dec(v___x_1441_);
v___y_1352_ = v_arg_1422_;
v___y_1353_ = v_arg_1434_;
v___y_1354_ = v_arg_1419_;
v___y_1355_ = v___x_1426_;
v___y_1356_ = v___x_1439_;
v___y_1357_ = v_arg_1425_;
v___y_1358_ = v_arg_1437_;
v___y_1359_ = v_arg_1431_;
v___y_1360_ = v___x_1418_;
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
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2(void){
_start:
{
uint8_t v___x_1451_; uint64_t v___x_1452_; 
v___x_1451_ = 1;
v___x_1452_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1451_);
return v___x_1452_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1454_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1455_ = lean_unsigned_to_nat(38u);
v___x_1456_ = lean_unsigned_to_nat(250u);
v___x_1457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3));
v___x_1458_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1459_ = l_mkPanicMessageWithDecl(v___x_1458_, v___x_1457_, v___x_1456_, v___x_1455_, v___x_1454_);
return v___x_1459_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6(void){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1461_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5));
v___x_1462_ = lean_unsigned_to_nat(6u);
v___x_1463_ = lean_unsigned_to_nat(260u);
v___x_1464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3));
v___x_1465_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1466_ = l_mkPanicMessageWithDecl(v___x_1465_, v___x_1464_, v___x_1463_, v___x_1462_, v___x_1461_);
return v___x_1466_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2(void){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1469_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__1));
v___x_1470_ = lean_unsigned_to_nat(4u);
v___x_1471_ = lean_unsigned_to_nat(219u);
v___x_1472_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__0));
v___x_1473_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1474_ = l_mkPanicMessageWithDecl(v___x_1473_, v___x_1472_, v___x_1471_, v___x_1470_, v___x_1469_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(lean_object* v_lhs_1475_, lean_object* v_rhs_1476_, uint8_t v_heq_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v_numArgs_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; 
v_numArgs_1489_ = l_Lean_Expr_getAppNumArgs(v_lhs_1475_);
v___x_1490_ = l_Lean_Expr_getAppNumArgs(v_rhs_1476_);
v___x_1491_ = lean_nat_dec_eq(v___x_1490_, v_numArgs_1489_);
lean_dec(v___x_1490_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
lean_dec(v_numArgs_1489_);
lean_dec_ref(v_rhs_1476_);
lean_dec_ref(v_lhs_1475_);
v___x_1492_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2);
v___x_1493_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1492_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
return v___x_1493_;
}
else
{
lean_object* v_f_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v_f_1494_ = l_Lean_Expr_getAppFn(v_lhs_1475_);
v___x_1495_ = lean_box(0);
lean_inc_ref(v_f_1494_);
v___x_1496_ = l_Lean_Meta_getFunInfo(v_f_1494_, v___x_1495_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1496_, 1);
v___x_1498_ = l_Lean_Meta_FunInfo_getArity(v_a_1497_);
lean_dec(v_a_1497_);
v___x_1499_ = lean_nat_dec_lt(v___x_1498_, v_numArgs_1489_);
lean_dec(v___x_1498_);
if (v___x_1499_ == 0)
{
lean_object* v_g_1500_; lean_object* v___x_1501_; 
v_g_1500_ = l_Lean_Expr_getAppFn(v_rhs_1476_);
v___x_1501_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_1494_, v_g_1500_, v_numArgs_1489_, v_lhs_1475_, v_rhs_1476_, v_heq_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
return v___x_1501_;
}
else
{
lean_object* v___x_1502_; 
lean_dec_ref(v_f_1494_);
lean_dec(v_numArgs_1489_);
lean_inc_ref(v_lhs_1475_);
v___x_1502_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(v_lhs_1475_, v_rhs_1476_);
if (lean_obj_tag(v___x_1502_) == 1)
{
lean_object* v_val_1503_; lean_object* v_fst_1504_; lean_object* v_snd_1505_; lean_object* v___y_1507_; lean_object* v___x_1520_; 
v_val_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_val_1503_);
lean_dec_ref_known(v___x_1502_, 1);
v_fst_1504_ = lean_ctor_get(v_val_1503_, 0);
lean_inc(v_fst_1504_);
v_snd_1505_ = lean_ctor_get(v_val_1503_, 1);
lean_inc_n(v_snd_1505_, 2);
lean_dec(v_val_1503_);
v___x_1520_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(v_fst_1504_, v_snd_1505_, v_a_1481_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
if (lean_obj_tag(v___x_1520_) == 0)
{
v___y_1507_ = v___x_1520_;
goto v___jp_1506_;
}
else
{
lean_object* v_a_1521_; uint8_t v___y_1523_; uint8_t v___x_1525_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
v___x_1525_ = l_Lean_Exception_isInterrupt(v_a_1521_);
if (v___x_1525_ == 0)
{
uint8_t v___x_1526_; 
v___x_1526_ = l_Lean_Exception_isRuntime(v_a_1521_);
v___y_1523_ = v___x_1526_;
goto v___jp_1522_;
}
else
{
lean_dec(v_a_1521_);
v___y_1523_ = v___x_1525_;
goto v___jp_1522_;
}
v___jp_1522_:
{
if (v___y_1523_ == 0)
{
lean_object* v___x_1524_; 
lean_dec_ref_known(v___x_1520_, 1);
lean_inc_ref(v_rhs_1476_);
lean_inc_ref(v_lhs_1475_);
v___x_1524_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1475_, v_rhs_1476_, lean_box(0), v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
v___y_1507_ = v___x_1524_;
goto v___jp_1506_;
}
else
{
v___y_1507_ = v___x_1520_;
goto v___jp_1506_;
}
}
}
v___jp_1506_:
{
if (lean_obj_tag(v___y_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1509_; 
v_a_1508_ = lean_ctor_get(v___y_1507_, 0);
lean_inc(v_a_1508_);
lean_dec_ref_known(v___y_1507_, 1);
v___x_1509_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_1508_, v_lhs_1475_, v_rhs_1476_, v_snd_1505_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
lean_dec(v_snd_1505_);
lean_dec_ref(v_rhs_1476_);
lean_dec_ref(v_lhs_1475_);
lean_dec(v_a_1508_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1511_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v___x_1509_, 1);
v___x_1511_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_1510_, v_heq_1477_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
return v___x_1511_;
}
else
{
return v___x_1509_;
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
lean_dec(v_snd_1505_);
lean_dec_ref(v_rhs_1476_);
lean_dec_ref(v_lhs_1475_);
v_a_1512_ = lean_ctor_get(v___y_1507_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___y_1507_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___y_1507_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___y_1507_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
}
else
{
lean_object* v___x_1527_; 
lean_dec(v___x_1502_);
v___x_1527_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1475_, v_rhs_1476_, lean_box(0), v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
return v___x_1527_;
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec_ref(v_f_1494_);
lean_dec(v_numArgs_1489_);
lean_dec_ref(v_rhs_1476_);
lean_dec_ref(v_lhs_1475_);
v_a_1528_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1496_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1496_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(lean_object* v_lhs_1536_, lean_object* v_rhs_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
uint8_t v___x_1549_; 
v___x_1549_ = l_Lean_Expr_isApp(v_lhs_1536_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = lean_box(0);
v___x_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
return v___x_1551_;
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1552_ = l_Lean_Expr_appFn_x21(v_lhs_1536_);
v___x_1553_ = l_Lean_Expr_appFn_x21(v_rhs_1537_);
v___x_1554_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v___x_1552_, v___x_1553_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
lean_dec_ref(v___x_1553_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1654_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1557_ = v___x_1554_;
v_isShared_1558_ = v_isSharedCheck_1654_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1554_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1654_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v_a_u2081_1559_; lean_object* v_a_u2082_1560_; 
v_a_u2081_1559_ = l_Lean_Expr_appArg_x21(v_lhs_1536_);
v_a_u2082_1560_ = l_Lean_Expr_appArg_x21(v_rhs_1537_);
if (lean_obj_tag(v_a_1555_) == 1)
{
lean_object* v_val_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1618_; 
lean_del_object(v___x_1557_);
lean_dec_ref(v___x_1552_);
v_val_1561_ = lean_ctor_get(v_a_1555_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v_a_1555_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1563_ = v_a_1555_;
v_isShared_1564_ = v_isSharedCheck_1618_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_val_1561_);
lean_dec(v_a_1555_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1618_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
size_t v___x_1565_; size_t v___x_1566_; uint8_t v___x_1567_; 
v___x_1565_ = lean_ptr_addr(v_a_u2081_1559_);
v___x_1566_ = lean_ptr_addr(v_a_u2082_1560_);
v___x_1567_ = lean_usize_dec_eq(v___x_1565_, v___x_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; 
v___x_1568_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_1559_, v_a_u2082_1560_, v___x_1567_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1570_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___x_1568_, 1);
v___x_1570_ = l_Lean_Meta_mkCongr(v_val_1561_, v_a_1569_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1581_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1581_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1581_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v_a_1571_);
v___x_1576_ = v___x_1563_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1578_; 
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1576_);
v___x_1578_ = v___x_1573_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_del_object(v___x_1563_);
v_a_1582_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1570_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1570_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_del_object(v___x_1563_);
lean_dec(v_val_1561_);
v_a_1590_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1568_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1568_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
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
lean_object* v___x_1598_; 
lean_dec_ref(v_a_u2082_1560_);
v___x_1598_ = l_Lean_Meta_mkCongrFun(v_val_1561_, v_a_u2081_1559_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1609_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1601_ = v___x_1598_;
v_isShared_1602_ = v_isSharedCheck_1609_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1598_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1609_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v_a_1599_);
v___x_1604_ = v___x_1563_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1606_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v___x_1604_);
v___x_1606_ = v___x_1601_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_del_object(v___x_1563_);
v_a_1610_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1598_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1598_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
}
else
{
size_t v___x_1619_; size_t v___x_1620_; uint8_t v___x_1621_; 
lean_dec(v_a_1555_);
v___x_1619_ = lean_ptr_addr(v_a_u2081_1559_);
v___x_1620_ = lean_ptr_addr(v_a_u2082_1560_);
v___x_1621_ = lean_usize_dec_eq(v___x_1619_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; 
lean_del_object(v___x_1557_);
v___x_1622_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_1559_, v_a_u2082_1560_, v___x_1621_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1624_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v___x_1622_, 1);
v___x_1624_ = l_Lean_Meta_mkCongrArg(v___x_1552_, v_a_1623_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1633_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1627_ = v___x_1624_;
v_isShared_1628_ = v_isSharedCheck_1633_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1633_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1629_, 0, v_a_1625_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1629_);
v___x_1631_ = v___x_1627_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
v_a_1634_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1624_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1624_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_dec_ref(v___x_1552_);
v_a_1642_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1622_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1622_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
lean_dec_ref(v_a_u2082_1560_);
lean_dec_ref(v_a_u2081_1559_);
lean_dec_ref(v___x_1552_);
v___x_1650_ = lean_box(0);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 0, v___x_1650_);
v___x_1652_ = v___x_1557_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1552_);
return v___x_1554_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1658_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__2));
v___x_1659_ = lean_unsigned_to_nat(14u);
v___x_1660_ = lean_unsigned_to_nat(22u);
v___x_1661_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__1));
v___x_1662_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__0));
v___x_1663_ = l_mkPanicMessageWithDecl(v___x_1662_, v___x_1661_, v___x_1660_, v___x_1659_, v___x_1658_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(lean_object* v_lhs_1664_, lean_object* v_rhs_1665_, uint8_t v_heq_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_1664_, v_rhs_1665_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1692_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1692_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1692_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___y_1684_; 
if (lean_obj_tag(v_a_1679_) == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3);
v___x_1690_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_spec__13(v___x_1689_);
v___y_1684_ = v___x_1690_;
goto v___jp_1683_;
}
else
{
lean_object* v_val_1691_; 
v_val_1691_ = lean_ctor_get(v_a_1679_, 0);
lean_inc(v_val_1691_);
lean_dec_ref_known(v_a_1679_, 1);
v___y_1684_ = v_val_1691_;
goto v___jp_1683_;
}
v___jp_1683_:
{
if (v_heq_1666_ == 0)
{
lean_object* v___x_1686_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v___y_1684_);
v___x_1686_ = v___x_1681_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___y_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
else
{
lean_object* v___x_1688_; 
lean_del_object(v___x_1681_);
v___x_1688_ = l_Lean_Meta_mkHEqOfEq(v___y_1684_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_);
return v___x_1688_;
}
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
v_a_1693_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1678_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1678_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__1(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1702_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1703_ = lean_unsigned_to_nat(36u);
v___x_1704_ = lean_unsigned_to_nat(143u);
v___x_1705_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1706_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1707_ = l_mkPanicMessageWithDecl(v___x_1706_, v___x_1705_, v___x_1704_, v___x_1703_, v___x_1702_);
return v___x_1707_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__2(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1708_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_1709_ = lean_unsigned_to_nat(34u);
v___x_1710_ = lean_unsigned_to_nat(144u);
v___x_1711_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1712_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1713_ = l_mkPanicMessageWithDecl(v___x_1712_, v___x_1711_, v___x_1710_, v___x_1709_, v___x_1708_);
return v___x_1713_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__4(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1715_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__3));
v___x_1716_ = lean_unsigned_to_nat(4u);
v___x_1717_ = lean_unsigned_to_nat(145u);
v___x_1718_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1719_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_1720_ = l_mkPanicMessageWithDecl(v___x_1719_, v___x_1718_, v___x_1717_, v___x_1716_, v___x_1715_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrProof(lean_object* v_lhs_1731_, lean_object* v_rhs_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; uint8_t v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; uint8_t v___y_1780_; lean_object* v_fileName_1816_; lean_object* v_fileMap_1817_; lean_object* v_options_1818_; lean_object* v_currRecDepth_1819_; lean_object* v_maxRecDepth_1820_; lean_object* v_ref_1821_; lean_object* v_currNamespace_1822_; lean_object* v_openDecls_1823_; lean_object* v_initHeartbeats_1824_; lean_object* v_maxHeartbeats_1825_; lean_object* v_quotContext_1826_; lean_object* v_currMacroScope_1827_; uint8_t v_diag_1828_; lean_object* v_cancelTk_x3f_1829_; uint8_t v_suppressElabErrors_1830_; lean_object* v_inheritedTraceOptions_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; lean_object* v___x_1863_; uint8_t v___x_1864_; 
v_fileName_1816_ = lean_ctor_get(v_a_1741_, 0);
v_fileMap_1817_ = lean_ctor_get(v_a_1741_, 1);
v_options_1818_ = lean_ctor_get(v_a_1741_, 2);
v_currRecDepth_1819_ = lean_ctor_get(v_a_1741_, 3);
v_maxRecDepth_1820_ = lean_ctor_get(v_a_1741_, 4);
v_ref_1821_ = lean_ctor_get(v_a_1741_, 5);
v_currNamespace_1822_ = lean_ctor_get(v_a_1741_, 6);
v_openDecls_1823_ = lean_ctor_get(v_a_1741_, 7);
v_initHeartbeats_1824_ = lean_ctor_get(v_a_1741_, 8);
v_maxHeartbeats_1825_ = lean_ctor_get(v_a_1741_, 9);
v_quotContext_1826_ = lean_ctor_get(v_a_1741_, 10);
v_currMacroScope_1827_ = lean_ctor_get(v_a_1741_, 11);
v_diag_1828_ = lean_ctor_get_uint8(v_a_1741_, sizeof(void*)*14);
v_cancelTk_x3f_1829_ = lean_ctor_get(v_a_1741_, 12);
v_suppressElabErrors_1830_ = lean_ctor_get_uint8(v_a_1741_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1831_ = lean_ctor_get(v_a_1741_, 13);
v___x_1832_ = l_Lean_Expr_cleanupAnnotations(v_lhs_1731_);
v___x_1833_ = l_Lean_Expr_isApp(v___x_1832_);
v___x_1863_ = lean_unsigned_to_nat(0u);
v___x_1864_ = lean_nat_dec_eq(v_maxRecDepth_1820_, v___x_1863_);
if (v___x_1864_ == 0)
{
uint8_t v___x_1865_; 
v___x_1865_ = lean_nat_dec_eq(v_currRecDepth_1819_, v_maxRecDepth_1820_);
if (v___x_1865_ == 0)
{
goto v___jp_1834_;
}
else
{
lean_object* v___x_1866_; 
lean_dec_ref(v___x_1832_);
lean_dec_ref(v_rhs_1732_);
lean_inc(v_ref_1821_);
v___x_1866_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1821_);
return v___x_1866_;
}
}
else
{
goto v___jp_1834_;
}
v___jp_1744_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__1, &l_Lean_Meta_Grind_mkEqCongrProof___closed__1_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__1);
v___x_1756_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1755_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec_ref(v___y_1753_);
return v___x_1756_;
}
v___jp_1757_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__2, &l_Lean_Meta_Grind_mkEqCongrProof___closed__2_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__2);
v___x_1769_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1768_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec_ref(v___y_1766_);
return v___x_1769_;
}
v___jp_1770_:
{
if (v___y_1780_ == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_dec_ref(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec_ref(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1771_);
v___x_1781_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__4, &l_Lean_Meta_Grind_mkEqCongrProof___closed__4_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__4);
v___x_1782_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1781_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v___y_1779_, v_a_1742_);
lean_dec_ref(v___y_1779_);
return v___x_1782_;
}
else
{
lean_object* v___x_1783_; size_t v___x_1784_; size_t v___x_1785_; uint8_t v___x_1786_; 
v___x_1783_ = l_Lean_Expr_constLevels_x21(v___y_1777_);
lean_dec_ref(v___y_1777_);
v___x_1784_ = lean_ptr_addr(v___y_1773_);
v___x_1785_ = lean_ptr_addr(v___y_1775_);
v___x_1786_ = lean_usize_dec_eq(v___x_1784_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; 
lean_inc_ref(v___y_1772_);
lean_inc_ref(v___y_1771_);
v___x_1787_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1771_, v___y_1772_, v___y_1776_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v___y_1779_, v_a_1742_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1789_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v___x_1787_, 1);
lean_inc_ref(v___y_1778_);
lean_inc_ref(v___y_1774_);
v___x_1789_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1774_, v___y_1778_, v___y_1776_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v___y_1779_, v_a_1742_);
lean_dec_ref(v___y_1779_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1800_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1800_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1800_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
v___x_1794_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__6));
v___x_1795_ = l_Lean_mkConst(v___x_1794_, v___x_1783_);
v___x_1796_ = l_Lean_mkApp8(v___x_1795_, v___y_1773_, v___y_1775_, v___y_1771_, v___y_1774_, v___y_1772_, v___y_1778_, v_a_1788_, v_a_1790_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v___x_1796_);
v___x_1798_ = v___x_1792_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
else
{
lean_dec(v_a_1788_);
lean_dec(v___x_1783_);
lean_dec_ref(v___y_1778_);
lean_dec_ref(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1771_);
return v___x_1789_;
}
}
else
{
lean_dec(v___x_1783_);
lean_dec_ref(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec_ref(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1771_);
return v___x_1787_;
}
}
else
{
uint8_t v___x_1801_; lean_object* v___x_1802_; 
lean_dec_ref(v___y_1775_);
v___x_1801_ = 0;
lean_inc_ref(v___y_1772_);
lean_inc_ref(v___y_1771_);
v___x_1802_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1771_, v___y_1772_, v___x_1801_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v___y_1779_, v_a_1742_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1804_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref_known(v___x_1802_, 1);
lean_inc_ref(v___y_1778_);
lean_inc_ref(v___y_1774_);
v___x_1804_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1774_, v___y_1778_, v___x_1801_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v___y_1779_, v_a_1742_);
lean_dec_ref(v___y_1779_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1815_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1815_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1815_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1809_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__8));
v___x_1810_ = l_Lean_mkConst(v___x_1809_, v___x_1783_);
v___x_1811_ = l_Lean_mkApp7(v___x_1810_, v___y_1773_, v___y_1771_, v___y_1774_, v___y_1772_, v___y_1778_, v_a_1803_, v_a_1805_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1811_);
v___x_1813_ = v___x_1807_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
else
{
lean_dec(v_a_1803_);
lean_dec(v___x_1783_);
lean_dec_ref(v___y_1778_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1771_);
return v___x_1804_;
}
}
else
{
lean_dec(v___x_1783_);
lean_dec_ref(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1771_);
return v___x_1802_;
}
}
}
}
v___jp_1834_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = lean_unsigned_to_nat(1u);
v___x_1836_ = lean_nat_add(v_currRecDepth_1819_, v___x_1835_);
lean_inc_ref(v_inheritedTraceOptions_1831_);
lean_inc(v_cancelTk_x3f_1829_);
lean_inc(v_currMacroScope_1827_);
lean_inc(v_quotContext_1826_);
lean_inc(v_maxHeartbeats_1825_);
lean_inc(v_initHeartbeats_1824_);
lean_inc(v_openDecls_1823_);
lean_inc(v_currNamespace_1822_);
lean_inc(v_ref_1821_);
lean_inc(v_maxRecDepth_1820_);
lean_inc_ref(v_options_1818_);
lean_inc_ref(v_fileMap_1817_);
lean_inc_ref(v_fileName_1816_);
v___x_1837_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1837_, 0, v_fileName_1816_);
lean_ctor_set(v___x_1837_, 1, v_fileMap_1817_);
lean_ctor_set(v___x_1837_, 2, v_options_1818_);
lean_ctor_set(v___x_1837_, 3, v___x_1836_);
lean_ctor_set(v___x_1837_, 4, v_maxRecDepth_1820_);
lean_ctor_set(v___x_1837_, 5, v_ref_1821_);
lean_ctor_set(v___x_1837_, 6, v_currNamespace_1822_);
lean_ctor_set(v___x_1837_, 7, v_openDecls_1823_);
lean_ctor_set(v___x_1837_, 8, v_initHeartbeats_1824_);
lean_ctor_set(v___x_1837_, 9, v_maxHeartbeats_1825_);
lean_ctor_set(v___x_1837_, 10, v_quotContext_1826_);
lean_ctor_set(v___x_1837_, 11, v_currMacroScope_1827_);
lean_ctor_set(v___x_1837_, 12, v_cancelTk_x3f_1829_);
lean_ctor_set(v___x_1837_, 13, v_inheritedTraceOptions_1831_);
lean_ctor_set_uint8(v___x_1837_, sizeof(void*)*14, v_diag_1828_);
lean_ctor_set_uint8(v___x_1837_, sizeof(void*)*14 + 1, v_suppressElabErrors_1830_);
if (v___x_1833_ == 0)
{
lean_dec_ref(v___x_1832_);
lean_dec_ref(v_rhs_1732_);
v___y_1745_ = v_a_1733_;
v___y_1746_ = v_a_1734_;
v___y_1747_ = v_a_1735_;
v___y_1748_ = v_a_1736_;
v___y_1749_ = v_a_1737_;
v___y_1750_ = v_a_1738_;
v___y_1751_ = v_a_1739_;
v___y_1752_ = v_a_1740_;
v___y_1753_ = v___x_1837_;
v___y_1754_ = v_a_1742_;
goto v___jp_1744_;
}
else
{
lean_object* v_arg_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; 
v_arg_1838_ = lean_ctor_get(v___x_1832_, 1);
lean_inc_ref(v_arg_1838_);
v___x_1839_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1832_);
v___x_1840_ = l_Lean_Expr_isApp(v___x_1839_);
if (v___x_1840_ == 0)
{
lean_dec_ref(v___x_1839_);
lean_dec_ref(v_arg_1838_);
lean_dec_ref(v_rhs_1732_);
v___y_1745_ = v_a_1733_;
v___y_1746_ = v_a_1734_;
v___y_1747_ = v_a_1735_;
v___y_1748_ = v_a_1736_;
v___y_1749_ = v_a_1737_;
v___y_1750_ = v_a_1738_;
v___y_1751_ = v_a_1739_;
v___y_1752_ = v_a_1740_;
v___y_1753_ = v___x_1837_;
v___y_1754_ = v_a_1742_;
goto v___jp_1744_;
}
else
{
lean_object* v_arg_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v_arg_1841_ = lean_ctor_get(v___x_1839_, 1);
lean_inc_ref(v_arg_1841_);
v___x_1842_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1839_);
v___x_1843_ = l_Lean_Expr_isApp(v___x_1842_);
if (v___x_1843_ == 0)
{
lean_dec_ref(v___x_1842_);
lean_dec_ref(v_arg_1841_);
lean_dec_ref(v_arg_1838_);
lean_dec_ref(v_rhs_1732_);
v___y_1745_ = v_a_1733_;
v___y_1746_ = v_a_1734_;
v___y_1747_ = v_a_1735_;
v___y_1748_ = v_a_1736_;
v___y_1749_ = v_a_1737_;
v___y_1750_ = v_a_1738_;
v___y_1751_ = v_a_1739_;
v___y_1752_ = v_a_1740_;
v___y_1753_ = v___x_1837_;
v___y_1754_ = v_a_1742_;
goto v___jp_1744_;
}
else
{
lean_object* v_arg_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v_arg_1844_ = lean_ctor_get(v___x_1842_, 1);
lean_inc_ref(v_arg_1844_);
v___x_1845_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1842_);
v___x_1846_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_1847_ = l_Lean_Expr_isConstOf(v___x_1845_, v___x_1846_);
if (v___x_1847_ == 0)
{
lean_dec_ref(v___x_1845_);
lean_dec_ref(v_arg_1844_);
lean_dec_ref(v_arg_1841_);
lean_dec_ref(v_arg_1838_);
lean_dec_ref(v_rhs_1732_);
v___y_1745_ = v_a_1733_;
v___y_1746_ = v_a_1734_;
v___y_1747_ = v_a_1735_;
v___y_1748_ = v_a_1736_;
v___y_1749_ = v_a_1737_;
v___y_1750_ = v_a_1738_;
v___y_1751_ = v_a_1739_;
v___y_1752_ = v_a_1740_;
v___y_1753_ = v___x_1837_;
v___y_1754_ = v_a_1742_;
goto v___jp_1744_;
}
else
{
lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1848_ = l_Lean_Expr_cleanupAnnotations(v_rhs_1732_);
v___x_1849_ = l_Lean_Expr_isApp(v___x_1848_);
if (v___x_1849_ == 0)
{
lean_dec_ref(v___x_1848_);
lean_dec_ref(v___x_1845_);
lean_dec_ref(v_arg_1844_);
lean_dec_ref(v_arg_1841_);
lean_dec_ref(v_arg_1838_);
v___y_1758_ = v_a_1733_;
v___y_1759_ = v_a_1734_;
v___y_1760_ = v_a_1735_;
v___y_1761_ = v_a_1736_;
v___y_1762_ = v_a_1737_;
v___y_1763_ = v_a_1738_;
v___y_1764_ = v_a_1739_;
v___y_1765_ = v_a_1740_;
v___y_1766_ = v___x_1837_;
v___y_1767_ = v_a_1742_;
goto v___jp_1757_;
}
else
{
lean_object* v_arg_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; 
v_arg_1850_ = lean_ctor_get(v___x_1848_, 1);
lean_inc_ref(v_arg_1850_);
v___x_1851_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1848_);
v___x_1852_ = l_Lean_Expr_isApp(v___x_1851_);
if (v___x_1852_ == 0)
{
lean_dec_ref(v___x_1851_);
lean_dec_ref(v_arg_1850_);
lean_dec_ref(v___x_1845_);
lean_dec_ref(v_arg_1844_);
lean_dec_ref(v_arg_1841_);
lean_dec_ref(v_arg_1838_);
v___y_1758_ = v_a_1733_;
v___y_1759_ = v_a_1734_;
v___y_1760_ = v_a_1735_;
v___y_1761_ = v_a_1736_;
v___y_1762_ = v_a_1737_;
v___y_1763_ = v_a_1738_;
v___y_1764_ = v_a_1739_;
v___y_1765_ = v_a_1740_;
v___y_1766_ = v___x_1837_;
v___y_1767_ = v_a_1742_;
goto v___jp_1757_;
}
else
{
lean_object* v_arg_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; 
v_arg_1853_ = lean_ctor_get(v___x_1851_, 1);
lean_inc_ref(v_arg_1853_);
v___x_1854_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1851_);
v___x_1855_ = l_Lean_Expr_isApp(v___x_1854_);
if (v___x_1855_ == 0)
{
lean_dec_ref(v___x_1854_);
lean_dec_ref(v_arg_1853_);
lean_dec_ref(v_arg_1850_);
lean_dec_ref(v___x_1845_);
lean_dec_ref(v_arg_1844_);
lean_dec_ref(v_arg_1841_);
lean_dec_ref(v_arg_1838_);
v___y_1758_ = v_a_1733_;
v___y_1759_ = v_a_1734_;
v___y_1760_ = v_a_1735_;
v___y_1761_ = v_a_1736_;
v___y_1762_ = v_a_1737_;
v___y_1763_ = v_a_1738_;
v___y_1764_ = v_a_1739_;
v___y_1765_ = v_a_1740_;
v___y_1766_ = v___x_1837_;
v___y_1767_ = v_a_1742_;
goto v___jp_1757_;
}
else
{
lean_object* v_arg_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; 
v_arg_1856_ = lean_ctor_get(v___x_1854_, 1);
lean_inc_ref(v_arg_1856_);
v___x_1857_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1854_);
v___x_1858_ = l_Lean_Expr_isConstOf(v___x_1857_, v___x_1846_);
lean_dec_ref(v___x_1857_);
if (v___x_1858_ == 0)
{
lean_dec_ref(v_arg_1856_);
lean_dec_ref(v_arg_1853_);
lean_dec_ref(v_arg_1850_);
lean_dec_ref(v___x_1845_);
lean_dec_ref(v_arg_1844_);
lean_dec_ref(v_arg_1841_);
lean_dec_ref(v_arg_1838_);
v___y_1758_ = v_a_1733_;
v___y_1759_ = v_a_1734_;
v___y_1760_ = v_a_1735_;
v___y_1761_ = v_a_1736_;
v___y_1762_ = v_a_1737_;
v___y_1763_ = v_a_1738_;
v___y_1764_ = v_a_1739_;
v___y_1765_ = v_a_1740_;
v___y_1766_ = v___x_1837_;
v___y_1767_ = v_a_1742_;
goto v___jp_1757_;
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1860_; uint8_t v___x_1861_; 
v___x_1859_ = lean_st_ref_get(v_a_1733_);
v___x_1860_ = lean_st_ref_get(v_a_1733_);
v___x_1861_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1859_, v_arg_1841_, v_arg_1853_);
lean_dec(v___x_1859_);
if (v___x_1861_ == 0)
{
lean_dec(v___x_1860_);
v___y_1771_ = v_arg_1841_;
v___y_1772_ = v_arg_1853_;
v___y_1773_ = v_arg_1844_;
v___y_1774_ = v_arg_1838_;
v___y_1775_ = v_arg_1856_;
v___y_1776_ = v___x_1858_;
v___y_1777_ = v___x_1845_;
v___y_1778_ = v_arg_1850_;
v___y_1779_ = v___x_1837_;
v___y_1780_ = v___x_1861_;
goto v___jp_1770_;
}
else
{
uint8_t v___x_1862_; 
v___x_1862_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1860_, v_arg_1838_, v_arg_1850_);
lean_dec(v___x_1860_);
v___y_1771_ = v_arg_1841_;
v___y_1772_ = v_arg_1853_;
v___y_1773_ = v_arg_1844_;
v___y_1774_ = v_arg_1838_;
v___y_1775_ = v_arg_1856_;
v___y_1776_ = v___x_1858_;
v___y_1777_ = v___x_1845_;
v___y_1778_ = v_arg_1850_;
v___y_1779_ = v___x_1837_;
v___y_1780_ = v___x_1862_;
goto v___jp_1770_;
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
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1877_ = lean_box(0);
v___x_1878_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3));
v___x_1879_ = l_Lean_mkConst(v___x_1878_, v___x_1877_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(lean_object* v_lhs_1880_, lean_object* v_rhs_1881_, uint8_t v_heq_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
lean_object* v___x_1894_; lean_object* v_p_1895_; lean_object* v___x_1896_; lean_object* v_q_1897_; uint8_t v___x_1898_; lean_object* v___x_1899_; 
v___x_1894_ = l_Lean_Expr_appFn_x21(v_lhs_1880_);
v_p_1895_ = l_Lean_Expr_appArg_x21(v___x_1894_);
lean_dec_ref(v___x_1894_);
v___x_1896_ = l_Lean_Expr_appFn_x21(v_rhs_1881_);
v_q_1897_ = l_Lean_Expr_appArg_x21(v___x_1896_);
lean_dec_ref(v___x_1896_);
v___x_1898_ = 0;
lean_inc_ref(v_q_1897_);
lean_inc_ref(v_p_1895_);
v___x_1899_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_p_1895_, v_q_1897_, v___x_1898_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v_hp_1901_; lean_object* v_hq_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref_known(v___x_1899_, 1);
v_hp_1901_ = l_Lean_Expr_appArg_x21(v_lhs_1880_);
v_hq_1902_ = l_Lean_Expr_appArg_x21(v_rhs_1881_);
v___x_1903_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4);
v___x_1904_ = l_Lean_mkApp5(v___x_1903_, v_p_1895_, v_q_1897_, v_a_1900_, v_hp_1901_, v_hq_1902_);
v___x_1905_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v___x_1904_, v_heq_1882_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
return v___x_1905_;
}
else
{
lean_dec_ref(v_q_1897_);
lean_dec_ref(v_p_1895_);
return v___x_1899_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1916_ = lean_box(0);
v___x_1917_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1));
v___x_1918_ = l_Lean_mkConst(v___x_1917_, v___x_1916_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(lean_object* v_lhs_1919_, lean_object* v_rhs_1920_, uint8_t v_heq_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_){
_start:
{
lean_object* v___x_1933_; lean_object* v_p_1934_; lean_object* v___x_1935_; lean_object* v_q_1936_; uint8_t v___x_1937_; lean_object* v___x_1938_; 
v___x_1933_ = l_Lean_Expr_appFn_x21(v_lhs_1919_);
v_p_1934_ = l_Lean_Expr_appArg_x21(v___x_1933_);
lean_dec_ref(v___x_1933_);
v___x_1935_ = l_Lean_Expr_appFn_x21(v_rhs_1920_);
v_q_1936_ = l_Lean_Expr_appArg_x21(v___x_1935_);
lean_dec_ref(v___x_1935_);
v___x_1937_ = 0;
lean_inc_ref(v_q_1936_);
lean_inc_ref(v_p_1934_);
v___x_1938_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_p_1934_, v_q_1936_, v___x_1937_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v_hp_1940_; lean_object* v_hq_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1938_, 1);
v_hp_1940_ = l_Lean_Expr_appArg_x21(v_lhs_1919_);
v_hq_1941_ = l_Lean_Expr_appArg_x21(v_rhs_1920_);
v___x_1942_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2);
v___x_1943_ = l_Lean_mkApp5(v___x_1942_, v_p_1934_, v_q_1936_, v_a_1939_, v_hp_1940_, v_hq_1941_);
v___x_1944_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v___x_1943_, v_heq_1921_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_);
return v___x_1944_;
}
else
{
lean_dec_ref(v_q_1936_);
lean_dec_ref(v_p_1934_);
return v___x_1938_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(lean_object* v_lhs_1945_, lean_object* v_rhs_1946_, uint8_t v_heq_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
if (lean_obj_tag(v_lhs_1945_) == 7)
{
if (lean_obj_tag(v_rhs_1946_) == 7)
{
lean_object* v_binderType_1959_; lean_object* v_body_1960_; lean_object* v_binderType_1961_; lean_object* v_body_1962_; lean_object* v___y_1964_; lean_object* v_a_1965_; lean_object* v___x_1984_; uint8_t v_foApprox_1985_; uint8_t v_ctxApprox_1986_; uint8_t v_quasiPatternApprox_1987_; uint8_t v_constApprox_1988_; uint8_t v_isDefEqStuckEx_1989_; uint8_t v_unificationHints_1990_; uint8_t v_proofIrrelevance_1991_; uint8_t v_assignSyntheticOpaque_1992_; uint8_t v_offsetCnstrs_1993_; uint8_t v_etaStruct_1994_; uint8_t v_univApprox_1995_; uint8_t v_iota_1996_; uint8_t v_beta_1997_; uint8_t v_proj_1998_; uint8_t v_zeta_1999_; uint8_t v_zetaDelta_2000_; uint8_t v_zetaUnused_2001_; uint8_t v_zetaHave_2002_; uint8_t v_trackZetaDelta_2003_; lean_object* v_zetaDeltaSet_2004_; lean_object* v_lctx_2005_; lean_object* v_localInstances_2006_; lean_object* v_defEqCtx_x3f_2007_; lean_object* v_synthPendingDepth_2008_; lean_object* v_canUnfold_x3f_2009_; uint8_t v_univApprox_2010_; uint8_t v_inTypeClassResolution_2011_; uint8_t v_cacheInferType_2012_; lean_object* v_a_2014_; uint8_t v___x_2060_; lean_object* v_config_2061_; uint64_t v___x_2062_; uint64_t v___x_2063_; uint64_t v___x_2064_; uint64_t v___x_2065_; uint64_t v___x_2066_; uint64_t v_key_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v_binderType_1959_ = lean_ctor_get(v_lhs_1945_, 1);
lean_inc_ref_n(v_binderType_1959_, 2);
v_body_1960_ = lean_ctor_get(v_lhs_1945_, 2);
lean_inc_ref(v_body_1960_);
lean_dec_ref_known(v_lhs_1945_, 3);
v_binderType_1961_ = lean_ctor_get(v_rhs_1946_, 1);
lean_inc_ref(v_binderType_1961_);
v_body_1962_ = lean_ctor_get(v_rhs_1946_, 2);
lean_inc_ref(v_body_1962_);
lean_dec_ref_known(v_rhs_1946_, 3);
v___x_1984_ = l_Lean_Meta_Context_config(v_a_1954_);
v_foApprox_1985_ = lean_ctor_get_uint8(v___x_1984_, 0);
v_ctxApprox_1986_ = lean_ctor_get_uint8(v___x_1984_, 1);
v_quasiPatternApprox_1987_ = lean_ctor_get_uint8(v___x_1984_, 2);
v_constApprox_1988_ = lean_ctor_get_uint8(v___x_1984_, 3);
v_isDefEqStuckEx_1989_ = lean_ctor_get_uint8(v___x_1984_, 4);
v_unificationHints_1990_ = lean_ctor_get_uint8(v___x_1984_, 5);
v_proofIrrelevance_1991_ = lean_ctor_get_uint8(v___x_1984_, 6);
v_assignSyntheticOpaque_1992_ = lean_ctor_get_uint8(v___x_1984_, 7);
v_offsetCnstrs_1993_ = lean_ctor_get_uint8(v___x_1984_, 8);
v_etaStruct_1994_ = lean_ctor_get_uint8(v___x_1984_, 10);
v_univApprox_1995_ = lean_ctor_get_uint8(v___x_1984_, 11);
v_iota_1996_ = lean_ctor_get_uint8(v___x_1984_, 12);
v_beta_1997_ = lean_ctor_get_uint8(v___x_1984_, 13);
v_proj_1998_ = lean_ctor_get_uint8(v___x_1984_, 14);
v_zeta_1999_ = lean_ctor_get_uint8(v___x_1984_, 15);
v_zetaDelta_2000_ = lean_ctor_get_uint8(v___x_1984_, 16);
v_zetaUnused_2001_ = lean_ctor_get_uint8(v___x_1984_, 17);
v_zetaHave_2002_ = lean_ctor_get_uint8(v___x_1984_, 18);
v_trackZetaDelta_2003_ = lean_ctor_get_uint8(v_a_1954_, sizeof(void*)*7);
v_zetaDeltaSet_2004_ = lean_ctor_get(v_a_1954_, 1);
v_lctx_2005_ = lean_ctor_get(v_a_1954_, 2);
v_localInstances_2006_ = lean_ctor_get(v_a_1954_, 3);
v_defEqCtx_x3f_2007_ = lean_ctor_get(v_a_1954_, 4);
v_synthPendingDepth_2008_ = lean_ctor_get(v_a_1954_, 5);
v_canUnfold_x3f_2009_ = lean_ctor_get(v_a_1954_, 6);
v_univApprox_2010_ = lean_ctor_get_uint8(v_a_1954_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2011_ = lean_ctor_get_uint8(v_a_1954_, sizeof(void*)*7 + 2);
v_cacheInferType_2012_ = lean_ctor_get_uint8(v_a_1954_, sizeof(void*)*7 + 3);
v___x_2060_ = 1;
v_config_2061_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_config_2061_, 0, v_foApprox_1985_);
lean_ctor_set_uint8(v_config_2061_, 1, v_ctxApprox_1986_);
lean_ctor_set_uint8(v_config_2061_, 2, v_quasiPatternApprox_1987_);
lean_ctor_set_uint8(v_config_2061_, 3, v_constApprox_1988_);
lean_ctor_set_uint8(v_config_2061_, 4, v_isDefEqStuckEx_1989_);
lean_ctor_set_uint8(v_config_2061_, 5, v_unificationHints_1990_);
lean_ctor_set_uint8(v_config_2061_, 6, v_proofIrrelevance_1991_);
lean_ctor_set_uint8(v_config_2061_, 7, v_assignSyntheticOpaque_1992_);
lean_ctor_set_uint8(v_config_2061_, 8, v_offsetCnstrs_1993_);
lean_ctor_set_uint8(v_config_2061_, 9, v___x_2060_);
lean_ctor_set_uint8(v_config_2061_, 10, v_etaStruct_1994_);
lean_ctor_set_uint8(v_config_2061_, 11, v_univApprox_1995_);
lean_ctor_set_uint8(v_config_2061_, 12, v_iota_1996_);
lean_ctor_set_uint8(v_config_2061_, 13, v_beta_1997_);
lean_ctor_set_uint8(v_config_2061_, 14, v_proj_1998_);
lean_ctor_set_uint8(v_config_2061_, 15, v_zeta_1999_);
lean_ctor_set_uint8(v_config_2061_, 16, v_zetaDelta_2000_);
lean_ctor_set_uint8(v_config_2061_, 17, v_zetaUnused_2001_);
lean_ctor_set_uint8(v_config_2061_, 18, v_zetaHave_2002_);
v___x_2062_ = l_Lean_Meta_Context_configKey(v_a_1954_);
v___x_2063_ = 3ULL;
v___x_2064_ = lean_uint64_shift_right(v___x_2062_, v___x_2063_);
v___x_2065_ = lean_uint64_shift_left(v___x_2064_, v___x_2063_);
v___x_2066_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2);
v_key_2067_ = lean_uint64_lor(v___x_2065_, v___x_2066_);
v___x_2068_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2068_, 0, v_config_2061_);
lean_ctor_set_uint64(v___x_2068_, sizeof(void*)*1, v_key_2067_);
lean_inc(v_canUnfold_x3f_2009_);
lean_inc(v_synthPendingDepth_2008_);
lean_inc(v_defEqCtx_x3f_2007_);
lean_inc_ref(v_localInstances_2006_);
lean_inc_ref(v_lctx_2005_);
lean_inc(v_zetaDeltaSet_2004_);
v___x_2069_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
lean_ctor_set(v___x_2069_, 1, v_zetaDeltaSet_2004_);
lean_ctor_set(v___x_2069_, 2, v_lctx_2005_);
lean_ctor_set(v___x_2069_, 3, v_localInstances_2006_);
lean_ctor_set(v___x_2069_, 4, v_defEqCtx_x3f_2007_);
lean_ctor_set(v___x_2069_, 5, v_synthPendingDepth_2008_);
lean_ctor_set(v___x_2069_, 6, v_canUnfold_x3f_2009_);
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*7, v_trackZetaDelta_2003_);
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*7 + 1, v_univApprox_2010_);
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2011_);
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*7 + 3, v_cacheInferType_2012_);
v___x_2070_ = l_Lean_Meta_getLevel(v_binderType_1959_, v___x_2069_, v_a_1955_, v_a_1956_, v_a_1957_);
lean_dec_ref_known(v___x_2069_, 7);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref_known(v___x_2070_, 1);
v_a_2014_ = v_a_2071_;
goto v___jp_2013_;
}
else
{
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2072_; 
v_a_2072_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2072_);
lean_dec_ref_known(v___x_2070_, 1);
v_a_2014_ = v_a_2072_;
goto v___jp_2013_;
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec_ref(v___x_1984_);
lean_dec_ref(v_body_1962_);
lean_dec_ref(v_binderType_1961_);
lean_dec_ref(v_body_1960_);
lean_dec_ref(v_binderType_1959_);
v_a_2073_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2070_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2070_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
v___jp_1963_:
{
uint8_t v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = 0;
lean_inc_ref(v_binderType_1961_);
lean_inc_ref(v_binderType_1959_);
v___x_1967_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_binderType_1959_, v_binderType_1961_, v___x_1966_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1969_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
lean_inc_ref(v_body_1962_);
lean_inc_ref(v_body_1960_);
v___x_1969_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_body_1960_, v_body_1962_, v___x_1966_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1983_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_1983_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1983_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1981_; 
v___x_1974_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__1));
v___x_1975_ = lean_box(0);
v___x_1976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1976_, 0, v_a_1965_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___y_1964_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = l_Lean_mkConst(v___x_1974_, v___x_1977_);
v___x_1979_ = l_Lean_mkApp6(v___x_1978_, v_binderType_1959_, v_binderType_1961_, v_body_1960_, v_body_1962_, v_a_1968_, v_a_1970_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1979_);
v___x_1981_ = v___x_1972_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
else
{
lean_dec(v_a_1968_);
lean_dec(v_a_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v_body_1962_);
lean_dec_ref(v_binderType_1961_);
lean_dec_ref(v_body_1960_);
lean_dec_ref(v_binderType_1959_);
return v___x_1969_;
}
}
else
{
lean_dec(v_a_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v_body_1962_);
lean_dec_ref(v_binderType_1961_);
lean_dec_ref(v_body_1960_);
lean_dec_ref(v_binderType_1959_);
return v___x_1967_;
}
}
v___jp_2013_:
{
uint8_t v_foApprox_2015_; uint8_t v_ctxApprox_2016_; uint8_t v_quasiPatternApprox_2017_; uint8_t v_constApprox_2018_; uint8_t v_isDefEqStuckEx_2019_; uint8_t v_unificationHints_2020_; uint8_t v_proofIrrelevance_2021_; uint8_t v_assignSyntheticOpaque_2022_; uint8_t v_offsetCnstrs_2023_; uint8_t v_etaStruct_2024_; uint8_t v_univApprox_2025_; uint8_t v_iota_2026_; uint8_t v_beta_2027_; uint8_t v_proj_2028_; uint8_t v_zeta_2029_; uint8_t v_zetaDelta_2030_; uint8_t v_zetaUnused_2031_; uint8_t v_zetaHave_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2059_; 
v_foApprox_2015_ = lean_ctor_get_uint8(v___x_1984_, 0);
v_ctxApprox_2016_ = lean_ctor_get_uint8(v___x_1984_, 1);
v_quasiPatternApprox_2017_ = lean_ctor_get_uint8(v___x_1984_, 2);
v_constApprox_2018_ = lean_ctor_get_uint8(v___x_1984_, 3);
v_isDefEqStuckEx_2019_ = lean_ctor_get_uint8(v___x_1984_, 4);
v_unificationHints_2020_ = lean_ctor_get_uint8(v___x_1984_, 5);
v_proofIrrelevance_2021_ = lean_ctor_get_uint8(v___x_1984_, 6);
v_assignSyntheticOpaque_2022_ = lean_ctor_get_uint8(v___x_1984_, 7);
v_offsetCnstrs_2023_ = lean_ctor_get_uint8(v___x_1984_, 8);
v_etaStruct_2024_ = lean_ctor_get_uint8(v___x_1984_, 10);
v_univApprox_2025_ = lean_ctor_get_uint8(v___x_1984_, 11);
v_iota_2026_ = lean_ctor_get_uint8(v___x_1984_, 12);
v_beta_2027_ = lean_ctor_get_uint8(v___x_1984_, 13);
v_proj_2028_ = lean_ctor_get_uint8(v___x_1984_, 14);
v_zeta_2029_ = lean_ctor_get_uint8(v___x_1984_, 15);
v_zetaDelta_2030_ = lean_ctor_get_uint8(v___x_1984_, 16);
v_zetaUnused_2031_ = lean_ctor_get_uint8(v___x_1984_, 17);
v_zetaHave_2032_ = lean_ctor_get_uint8(v___x_1984_, 18);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2034_ = v___x_1984_;
v_isShared_2035_ = v_isSharedCheck_2059_;
goto v_resetjp_2033_;
}
else
{
lean_dec(v___x_1984_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2059_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
uint8_t v___x_2036_; lean_object* v_config_2038_; 
v___x_2036_ = 1;
if (v_isShared_2035_ == 0)
{
v_config_2038_ = v___x_2034_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2058_, 0, v_foApprox_2015_);
lean_ctor_set_uint8(v_reuseFailAlloc_2058_, 1, v_ctxApprox_2016_);
lean_ctor_set_uint8(v_reuseFailAlloc_2058_, 2, v_quasiPatternApprox_2017_);
lean_ctor_set_uint8(v_reuseFailAlloc_2058_, 3, v_constApprox_2018_);
lean_ctor_set_uint8(v_reuseFailAlloc_2058_, 4, v_isDefEqStuckEx_2019_);
lean_ctor_set_uint8(v_reuseFailAlloc_2058_, 5, v_unificationHints_2020_);
lean_ctor_set_uint8(v_reuseFailAlloc_2058_, 6, v_proofIrrelevance_2021_);
lean_ctor_set_uint8(v_reuseFailAlloc_2058_, 7, v_assignSyntheticOpaque_2022_);
lean_ctor_set_uint8(v_reuseFailAlloc_2058_, 8, v_offsetCnstrs_2023_);
lean_ctor_set_uint8(v_reuseFailAlloc_2058_, 10, v_etaStruct_2024_);
lean_ctor_set_uint8(v_reuseFailAlloc_2058_, 11, v_univApprox_2025_);
lean_ctor_set_uint8(v_reuseFailAlloc_2058_, 12, v_iota_2026_);
lean_ctor_set_uint8(v_reuseFailAlloc_2058_, 13, v_beta_2027_);
lean_ctor_set_uint8(v_reuseFailAlloc_2058_, 14, v_proj_2028_);
lean_ctor_set_uint8(v_reuseFailAlloc_2058_, 15, v_zeta_2029_);
lean_ctor_set_uint8(v_reuseFailAlloc_2058_, 16, v_zetaDelta_2030_);
lean_ctor_set_uint8(v_reuseFailAlloc_2058_, 17, v_zetaUnused_2031_);
lean_ctor_set_uint8(v_reuseFailAlloc_2058_, 18, v_zetaHave_2032_);
v_config_2038_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
uint64_t v___x_2039_; uint64_t v___x_2040_; uint64_t v___x_2041_; uint64_t v___x_2042_; uint64_t v___x_2043_; uint64_t v_key_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
lean_ctor_set_uint8(v_config_2038_, 9, v___x_2036_);
v___x_2039_ = l_Lean_Meta_Context_configKey(v_a_1954_);
v___x_2040_ = 3ULL;
v___x_2041_ = lean_uint64_shift_right(v___x_2039_, v___x_2040_);
v___x_2042_ = lean_uint64_shift_left(v___x_2041_, v___x_2040_);
v___x_2043_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2);
v_key_2044_ = lean_uint64_lor(v___x_2042_, v___x_2043_);
v___x_2045_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2045_, 0, v_config_2038_);
lean_ctor_set_uint64(v___x_2045_, sizeof(void*)*1, v_key_2044_);
lean_inc(v_canUnfold_x3f_2009_);
lean_inc(v_synthPendingDepth_2008_);
lean_inc(v_defEqCtx_x3f_2007_);
lean_inc_ref(v_localInstances_2006_);
lean_inc_ref(v_lctx_2005_);
lean_inc(v_zetaDeltaSet_2004_);
v___x_2046_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
lean_ctor_set(v___x_2046_, 1, v_zetaDeltaSet_2004_);
lean_ctor_set(v___x_2046_, 2, v_lctx_2005_);
lean_ctor_set(v___x_2046_, 3, v_localInstances_2006_);
lean_ctor_set(v___x_2046_, 4, v_defEqCtx_x3f_2007_);
lean_ctor_set(v___x_2046_, 5, v_synthPendingDepth_2008_);
lean_ctor_set(v___x_2046_, 6, v_canUnfold_x3f_2009_);
lean_ctor_set_uint8(v___x_2046_, sizeof(void*)*7, v_trackZetaDelta_2003_);
lean_ctor_set_uint8(v___x_2046_, sizeof(void*)*7 + 1, v_univApprox_2010_);
lean_ctor_set_uint8(v___x_2046_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2011_);
lean_ctor_set_uint8(v___x_2046_, sizeof(void*)*7 + 3, v_cacheInferType_2012_);
lean_inc_ref(v_body_1960_);
v___x_2047_ = l_Lean_Meta_getLevel(v_body_1960_, v___x_2046_, v_a_1955_, v_a_1956_, v_a_1957_);
lean_dec_ref_known(v___x_2046_, 7);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2047_, 1);
v___y_1964_ = v_a_2014_;
v_a_1965_ = v_a_2048_;
goto v___jp_1963_;
}
else
{
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2049_; 
v_a_2049_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2049_);
lean_dec_ref_known(v___x_2047_, 1);
v___y_1964_ = v_a_2014_;
v_a_1965_ = v_a_2049_;
goto v___jp_1963_;
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec(v_a_2014_);
lean_dec_ref(v_body_1962_);
lean_dec_ref(v_binderType_1961_);
lean_dec_ref(v_body_1960_);
lean_dec_ref(v_binderType_1959_);
v_a_2050_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2047_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2047_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
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
lean_object* v___x_2081_; lean_object* v___x_2082_; 
lean_dec_ref_known(v_lhs_1945_, 3);
lean_dec_ref(v_rhs_1946_);
v___x_2081_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4);
v___x_2082_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2081_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
return v___x_2082_;
}
}
else
{
lean_object* v___x_2083_; 
lean_inc_ref(v_lhs_1945_);
v___x_2083_ = l_Lean_Meta_Grind_useFunCC___redArg(v_lhs_1945_, v_a_1948_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; uint8_t v___x_2085_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2084_);
lean_dec_ref_known(v___x_2083_, 1);
v___x_2085_ = lean_unbox(v_a_2084_);
lean_dec(v_a_2084_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2086_ = l_Lean_Expr_getAppNumArgs(v_lhs_1945_);
v___x_2087_ = l_Lean_Expr_getAppNumArgs(v_rhs_1946_);
v___x_2088_ = lean_nat_dec_eq(v___x_2087_, v___x_2086_);
lean_dec(v___x_2087_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
lean_dec(v___x_2086_);
lean_dec_ref(v_rhs_1946_);
lean_dec_ref(v_lhs_1945_);
v___x_2089_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6);
v___x_2090_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2089_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
return v___x_2090_;
}
else
{
lean_object* v___x_2091_; lean_object* v___x_2092_; uint8_t v___y_2108_; uint8_t v___y_2120_; lean_object* v___x_2124_; uint8_t v___x_2125_; uint8_t v___y_2130_; 
v___x_2091_ = l_Lean_Expr_getAppFn(v_lhs_1945_);
v___x_2092_ = l_Lean_Expr_getAppFn(v_rhs_1946_);
v___x_2124_ = lean_unsigned_to_nat(2u);
v___x_2125_ = lean_nat_dec_eq(v___x_2086_, v___x_2124_);
if (v___x_2125_ == 0)
{
v___y_2130_ = v___x_2125_;
goto v___jp_2129_;
}
else
{
lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10));
v___x_2135_ = l_Lean_Expr_isConstOf(v___x_2091_, v___x_2134_);
v___y_2130_ = v___x_2135_;
goto v___jp_2129_;
}
v___jp_2093_:
{
lean_object* v___x_2094_; 
lean_inc_ref(v_rhs_1946_);
lean_inc_ref(v_lhs_1945_);
v___x_2094_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(v_lhs_1945_, v_rhs_1946_, v___x_2091_, v___x_2092_, v___x_2086_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
lean_dec_ref(v___x_2092_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; uint8_t v___x_2096_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2096_ = lean_unbox(v_a_2095_);
lean_dec(v_a_2095_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; 
v___x_2097_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_1945_, v_rhs_1946_, v_heq_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
return v___x_2097_;
}
else
{
lean_object* v___x_2098_; 
v___x_2098_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_1945_, v_rhs_1946_, v_heq_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
lean_dec_ref(v_rhs_1946_);
lean_dec_ref(v_lhs_1945_);
return v___x_2098_;
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec_ref(v_rhs_1946_);
lean_dec_ref(v_lhs_1945_);
v_a_2099_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2094_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2094_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
v___jp_2107_:
{
if (v___y_2108_ == 0)
{
goto v___jp_2093_;
}
else
{
lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2109_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_2110_ = l_Lean_Expr_isConstOf(v___x_2092_, v___x_2109_);
if (v___x_2110_ == 0)
{
goto v___jp_2093_;
}
else
{
lean_object* v___x_2111_; 
lean_dec_ref(v___x_2092_);
lean_dec_ref(v___x_2091_);
lean_dec(v___x_2086_);
v___x_2111_ = l_Lean_Meta_Grind_mkEqCongrProof(v_lhs_1945_, v_rhs_1946_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
if (lean_obj_tag(v___x_2111_) == 0)
{
if (v_heq_1947_ == 0)
{
return v___x_2111_;
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2113_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref_known(v___x_2111_, 1);
v___x_2113_ = l_Lean_Meta_mkHEqOfEq(v_a_2112_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
return v___x_2113_;
}
}
else
{
return v___x_2111_;
}
}
}
}
v___jp_2114_:
{
lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2115_ = lean_unsigned_to_nat(3u);
v___x_2116_ = lean_nat_dec_eq(v___x_2086_, v___x_2115_);
if (v___x_2116_ == 0)
{
v___y_2108_ = v___x_2116_;
goto v___jp_2107_;
}
else
{
lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_2118_ = l_Lean_Expr_isConstOf(v___x_2091_, v___x_2117_);
v___y_2108_ = v___x_2118_;
goto v___jp_2107_;
}
}
v___jp_2119_:
{
if (v___y_2120_ == 0)
{
goto v___jp_2114_;
}
else
{
lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2121_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8));
v___x_2122_ = l_Lean_Expr_isConstOf(v___x_2092_, v___x_2121_);
if (v___x_2122_ == 0)
{
goto v___jp_2114_;
}
else
{
lean_object* v___x_2123_; 
lean_dec_ref(v___x_2092_);
lean_dec_ref(v___x_2091_);
lean_dec(v___x_2086_);
v___x_2123_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_1945_, v_rhs_1946_, v_heq_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
lean_dec_ref(v_rhs_1946_);
lean_dec_ref(v_lhs_1945_);
return v___x_2123_;
}
}
}
v___jp_2126_:
{
if (v___x_2125_ == 0)
{
v___y_2120_ = v___x_2125_;
goto v___jp_2119_;
}
else
{
lean_object* v___x_2127_; uint8_t v___x_2128_; 
v___x_2127_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8));
v___x_2128_ = l_Lean_Expr_isConstOf(v___x_2091_, v___x_2127_);
v___y_2120_ = v___x_2128_;
goto v___jp_2119_;
}
}
v___jp_2129_:
{
if (v___y_2130_ == 0)
{
goto v___jp_2126_;
}
else
{
lean_object* v___x_2131_; uint8_t v___x_2132_; 
v___x_2131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10));
v___x_2132_ = l_Lean_Expr_isConstOf(v___x_2092_, v___x_2131_);
if (v___x_2132_ == 0)
{
goto v___jp_2126_;
}
else
{
lean_object* v___x_2133_; 
lean_dec_ref(v___x_2092_);
lean_dec_ref(v___x_2091_);
lean_dec(v___x_2086_);
v___x_2133_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_1945_, v_rhs_1946_, v_heq_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
lean_dec_ref(v_rhs_1946_);
lean_dec_ref(v_lhs_1945_);
return v___x_2133_;
}
}
}
}
}
else
{
lean_object* v___x_2136_; 
v___x_2136_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_1945_, v_rhs_1946_, v_heq_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
return v___x_2136_;
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec_ref(v_rhs_1946_);
lean_dec_ref(v_lhs_1945_);
v_a_2137_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2083_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2083_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(lean_object* v_lhs_2145_, lean_object* v_rhs_2146_, lean_object* v_h_2147_, uint8_t v_flipped_2148_, uint8_t v_heq_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2161_ = l_Lean_Meta_Grind_congrPlaceholderProof;
v___x_2162_ = lean_expr_eqv(v_h_2147_, v___x_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; uint8_t v___x_2164_; 
v___x_2163_ = l_Lean_Meta_Grind_eqCongrSymmPlaceholderProof;
v___x_2164_ = lean_expr_eqv(v_h_2147_, v___x_2163_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; 
lean_dec_ref(v_rhs_2146_);
lean_dec_ref(v_lhs_2145_);
v___x_2165_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(v_h_2147_, v_flipped_2148_, v_heq_2149_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
return v___x_2165_;
}
else
{
lean_object* v___x_2166_; 
lean_dec_ref(v_h_2147_);
v___x_2166_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(v_lhs_2145_, v_rhs_2146_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2166_) == 0)
{
if (v_heq_2149_ == 0)
{
return v___x_2166_;
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2168_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2166_, 1);
v___x_2168_ = l_Lean_Meta_mkHEqOfEq(v_a_2167_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
return v___x_2168_;
}
}
else
{
return v___x_2166_;
}
}
}
else
{
lean_object* v___x_2169_; 
lean_dec_ref(v_h_2147_);
v___x_2169_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(v_lhs_2145_, v_rhs_2146_, v_heq_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
return v___x_2169_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2171_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2172_ = lean_unsigned_to_nat(29u);
v___x_2173_ = lean_unsigned_to_nat(288u);
v___x_2174_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0));
v___x_2175_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2176_ = l_mkPanicMessageWithDecl(v___x_2175_, v___x_2174_, v___x_2173_, v___x_2172_, v___x_2171_);
return v___x_2176_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2177_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2178_ = lean_unsigned_to_nat(35u);
v___x_2179_ = lean_unsigned_to_nat(287u);
v___x_2180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0));
v___x_2181_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2182_ = l_mkPanicMessageWithDecl(v___x_2181_, v___x_2180_, v___x_2179_, v___x_2178_, v___x_2177_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(lean_object* v_lhs_2183_, lean_object* v_common_2184_, lean_object* v_acc_2185_, uint8_t v_heq_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_){
_start:
{
size_t v___x_2198_; size_t v___x_2199_; uint8_t v___x_2200_; 
v___x_2198_ = lean_ptr_addr(v_lhs_2183_);
v___x_2199_ = lean_ptr_addr(v_common_2184_);
v___x_2200_ = lean_usize_dec_eq(v___x_2198_, v___x_2199_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = lean_st_ref_get(v_a_2187_);
lean_inc_ref(v_lhs_2183_);
v___x_2202_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2201_, v_lhs_2183_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
lean_dec(v___x_2201_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v_target_x3f_2204_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2202_, 1);
v_target_x3f_2204_ = lean_ctor_get(v_a_2203_, 4);
lean_inc(v_target_x3f_2204_);
if (lean_obj_tag(v_target_x3f_2204_) == 1)
{
lean_object* v_proof_x3f_2205_; 
v_proof_x3f_2205_ = lean_ctor_get(v_a_2203_, 5);
lean_inc(v_proof_x3f_2205_);
if (lean_obj_tag(v_proof_x3f_2205_) == 1)
{
uint8_t v_flipped_2206_; lean_object* v_val_2207_; lean_object* v_val_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2236_; 
v_flipped_2206_ = lean_ctor_get_uint8(v_a_2203_, sizeof(void*)*12);
lean_dec(v_a_2203_);
v_val_2207_ = lean_ctor_get(v_target_x3f_2204_, 0);
lean_inc(v_val_2207_);
lean_dec_ref_known(v_target_x3f_2204_, 1);
v_val_2208_ = lean_ctor_get(v_proof_x3f_2205_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v_proof_x3f_2205_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2210_ = v_proof_x3f_2205_;
v_isShared_2211_ = v_isSharedCheck_2236_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_val_2208_);
lean_dec(v_proof_x3f_2205_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2236_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2212_; 
lean_inc(v_val_2207_);
v___x_2212_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_lhs_2183_, v_val_2207_, v_val_2208_, v_flipped_2206_, v_heq_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2214_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2213_);
lean_dec_ref_known(v___x_2212_, 1);
v___x_2214_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_acc_2185_, v_a_2213_, v_heq_2186_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; lean_object* v___x_2217_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref_known(v___x_2214_, 1);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v_a_2215_);
v___x_2217_ = v___x_2210_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2215_);
v___x_2217_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
v_lhs_2183_ = v_val_2207_;
v_acc_2185_ = v___x_2217_;
goto _start;
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_del_object(v___x_2210_);
lean_dec(v_val_2207_);
v_a_2220_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2214_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2214_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_del_object(v___x_2210_);
lean_dec(v_val_2207_);
lean_dec(v_acc_2185_);
v_a_2228_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2212_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2212_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
}
else
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
lean_dec_ref_known(v_target_x3f_2204_, 1);
lean_dec(v_proof_x3f_2205_);
lean_dec(v_a_2203_);
lean_dec(v_acc_2185_);
lean_dec_ref(v_lhs_2183_);
v___x_2237_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1);
v___x_2238_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2237_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
return v___x_2238_;
}
}
else
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_dec(v_target_x3f_2204_);
lean_dec(v_a_2203_);
lean_dec(v_acc_2185_);
lean_dec_ref(v_lhs_2183_);
v___x_2239_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2);
v___x_2240_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2239_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
return v___x_2240_;
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec(v_acc_2185_);
lean_dec_ref(v_lhs_2183_);
v_a_2241_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2202_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2202_);
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
else
{
lean_object* v___x_2249_; 
lean_dec_ref(v_lhs_2183_);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v_acc_2185_);
return v___x_2249_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1(void){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2251_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2252_ = lean_unsigned_to_nat(29u);
v___x_2253_ = lean_unsigned_to_nat(300u);
v___x_2254_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0));
v___x_2255_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2256_ = l_mkPanicMessageWithDecl(v___x_2255_, v___x_2254_, v___x_2253_, v___x_2252_, v___x_2251_);
return v___x_2256_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2257_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2258_ = lean_unsigned_to_nat(35u);
v___x_2259_ = lean_unsigned_to_nat(299u);
v___x_2260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0));
v___x_2261_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2262_ = l_mkPanicMessageWithDecl(v___x_2261_, v___x_2260_, v___x_2259_, v___x_2258_, v___x_2257_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(lean_object* v_rhs_2263_, lean_object* v_common_2264_, lean_object* v_lhsEqCommon_x3f_2265_, uint8_t v_heq_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_){
_start:
{
size_t v___x_2278_; size_t v___x_2279_; uint8_t v___x_2280_; 
v___x_2278_ = lean_ptr_addr(v_rhs_2263_);
v___x_2279_ = lean_ptr_addr(v_common_2264_);
v___x_2280_ = lean_usize_dec_eq(v___x_2278_, v___x_2279_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = lean_st_ref_get(v_a_2267_);
lean_inc_ref(v_rhs_2263_);
v___x_2282_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2281_, v_rhs_2263_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
lean_dec(v___x_2281_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v_target_x3f_2284_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2282_, 1);
v_target_x3f_2284_ = lean_ctor_get(v_a_2283_, 4);
lean_inc(v_target_x3f_2284_);
if (lean_obj_tag(v_target_x3f_2284_) == 1)
{
lean_object* v_proof_x3f_2285_; 
v_proof_x3f_2285_ = lean_ctor_get(v_a_2283_, 5);
lean_inc(v_proof_x3f_2285_);
if (lean_obj_tag(v_proof_x3f_2285_) == 1)
{
uint8_t v_flipped_2286_; lean_object* v_val_2287_; lean_object* v_val_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2327_; 
v_flipped_2286_ = lean_ctor_get_uint8(v_a_2283_, sizeof(void*)*12);
lean_dec(v_a_2283_);
v_val_2287_ = lean_ctor_get(v_target_x3f_2284_, 0);
lean_inc(v_val_2287_);
lean_dec_ref_known(v_target_x3f_2284_, 1);
v_val_2288_ = lean_ctor_get(v_proof_x3f_2285_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v_proof_x3f_2285_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2290_ = v_proof_x3f_2285_;
v_isShared_2291_ = v_isSharedCheck_2327_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_val_2288_);
lean_dec(v_proof_x3f_2285_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2327_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
uint8_t v___y_2293_; 
if (v_flipped_2286_ == 0)
{
uint8_t v___x_2326_; 
v___x_2326_ = 1;
v___y_2293_ = v___x_2326_;
goto v___jp_2292_;
}
else
{
v___y_2293_ = v___x_2280_;
goto v___jp_2292_;
}
v___jp_2292_:
{
lean_object* v___x_2294_; 
lean_inc(v_val_2287_);
v___x_2294_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_val_2287_, v_rhs_2263_, v_val_2288_, v___y_2293_, v_heq_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2296_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v___x_2296_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_val_2287_, v_common_2264_, v_lhsEqCommon_x3f_2265_, v_heq_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2298_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref_known(v___x_2296_, 1);
v___x_2298_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_a_2297_, v_a_2295_, v_heq_2266_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2309_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2301_ = v___x_2298_;
v_isShared_2302_ = v_isSharedCheck_2309_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2309_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v_a_2299_);
v___x_2304_ = v___x_2290_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2306_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2304_);
v___x_2306_ = v___x_2301_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_del_object(v___x_2290_);
v_a_2310_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2298_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2298_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
else
{
lean_dec(v_a_2295_);
lean_del_object(v___x_2290_);
return v___x_2296_;
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_del_object(v___x_2290_);
lean_dec(v_val_2287_);
lean_dec(v_lhsEqCommon_x3f_2265_);
v_a_2318_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2294_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2294_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
}
else
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_dec(v_proof_x3f_2285_);
lean_dec_ref_known(v_target_x3f_2284_, 1);
lean_dec(v_a_2283_);
lean_dec(v_lhsEqCommon_x3f_2265_);
lean_dec_ref(v_rhs_2263_);
v___x_2328_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1);
v___x_2329_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2328_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
return v___x_2329_;
}
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
lean_dec(v_target_x3f_2284_);
lean_dec(v_a_2283_);
lean_dec(v_lhsEqCommon_x3f_2265_);
lean_dec_ref(v_rhs_2263_);
v___x_2330_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2);
v___x_2331_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2330_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
return v___x_2331_;
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec(v_lhsEqCommon_x3f_2265_);
lean_dec_ref(v_rhs_2263_);
v_a_2332_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2282_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2282_);
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
lean_object* v___x_2340_; 
lean_dec_ref(v_rhs_2263_);
v___x_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2340_, 0, v_lhsEqCommon_x3f_2265_);
return v___x_2340_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3(void){
_start:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2341_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2342_ = lean_unsigned_to_nat(72u);
v___x_2343_ = lean_unsigned_to_nat(321u);
v___x_2344_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0));
v___x_2345_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2346_ = l_mkPanicMessageWithDecl(v___x_2345_, v___x_2344_, v___x_2343_, v___x_2342_, v___x_2341_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(lean_object* v_lhs_2347_, lean_object* v_rhs_2348_, uint8_t v_heq_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_){
_start:
{
size_t v___x_2361_; size_t v___x_2362_; uint8_t v___x_2363_; 
v___x_2361_ = lean_ptr_addr(v_lhs_2347_);
v___x_2362_ = lean_ptr_addr(v_rhs_2348_);
v___x_2363_ = lean_usize_dec_eq(v___x_2361_, v___x_2362_);
if (v___x_2363_ == 0)
{
lean_object* v___x_2364_; 
lean_inc_ref(v_lhs_2347_);
v___x_2364_ = l_Lean_Meta_Grind_getRootENode___redArg(v_lhs_2347_, v_a_2350_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2365_);
lean_dec_ref_known(v___x_2364_, 1);
v___x_2366_ = lean_st_ref_get(v_a_2350_);
lean_inc_ref(v_lhs_2347_);
v___x_2367_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2366_, v_lhs_2347_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
lean_dec(v___x_2366_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
lean_inc(v_a_2368_);
lean_dec_ref_known(v___x_2367_, 1);
v___x_2369_ = lean_st_ref_get(v_a_2350_);
lean_inc_ref(v_rhs_2348_);
v___x_2370_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2369_, v_rhs_2348_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
lean_dec(v___x_2369_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v_root_2372_; lean_object* v_root_2373_; size_t v___x_2374_; size_t v___x_2375_; uint8_t v___x_2376_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_a_2371_);
lean_dec_ref_known(v___x_2370_, 1);
v_root_2372_ = lean_ctor_get(v_a_2368_, 2);
lean_inc_ref(v_root_2372_);
lean_dec(v_a_2368_);
v_root_2373_ = lean_ctor_get(v_a_2371_, 2);
lean_inc_ref(v_root_2373_);
lean_dec(v_a_2371_);
v___x_2374_ = lean_ptr_addr(v_root_2372_);
lean_dec_ref(v_root_2372_);
v___x_2375_ = lean_ptr_addr(v_root_2373_);
lean_dec_ref(v_root_2373_);
v___x_2376_ = lean_usize_dec_eq(v___x_2374_, v___x_2375_);
if (v___x_2376_ == 0)
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
lean_dec(v_a_2365_);
lean_dec_ref(v_rhs_2348_);
lean_dec_ref(v_lhs_2347_);
v___x_2377_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2);
v___x_2378_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2377_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
return v___x_2378_;
}
else
{
lean_object* v___x_2379_; 
lean_inc_ref(v_rhs_2348_);
lean_inc_ref(v_lhs_2347_);
v___x_2379_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(v_lhs_2347_, v_rhs_2348_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; uint8_t v_heqProofs_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2380_);
lean_dec_ref_known(v___x_2379_, 1);
v_heqProofs_2381_ = lean_ctor_get_uint8(v_a_2365_, sizeof(void*)*12 + 4);
lean_dec(v_a_2365_);
v___x_2382_ = lean_box(0);
v___x_2383_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_2347_, v_a_2380_, v___x_2382_, v_heqProofs_2381_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; lean_object* v___x_2385_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref_known(v___x_2383_, 1);
v___x_2385_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_2348_, v_a_2380_, v_a_2384_, v_heqProofs_2381_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
lean_dec(v_a_2380_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2401_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2388_ = v___x_2385_;
v_isShared_2389_ = v_isSharedCheck_2401_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2385_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2401_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
if (lean_obj_tag(v_a_2386_) == 1)
{
lean_object* v_val_2390_; uint8_t v___y_2395_; 
v_val_2390_ = lean_ctor_get(v_a_2386_, 0);
lean_inc(v_val_2390_);
lean_dec_ref_known(v_a_2386_, 1);
if (v_heq_2349_ == 0)
{
if (v_heqProofs_2381_ == 0)
{
v___y_2395_ = v___x_2376_;
goto v___jp_2394_;
}
else
{
lean_del_object(v___x_2388_);
goto v___jp_2391_;
}
}
else
{
v___y_2395_ = v_heqProofs_2381_;
goto v___jp_2394_;
}
v___jp_2391_:
{
if (v_heq_2349_ == 0)
{
lean_object* v___x_2392_; 
v___x_2392_ = l_Lean_Meta_mkEqOfHEq(v_val_2390_, v_heq_2349_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
return v___x_2392_;
}
else
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Lean_Meta_mkHEqOfEq(v_val_2390_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
return v___x_2393_;
}
}
v___jp_2394_:
{
if (v___y_2395_ == 0)
{
lean_del_object(v___x_2388_);
goto v___jp_2391_;
}
else
{
lean_object* v___x_2397_; 
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v_val_2390_);
v___x_2397_ = v___x_2388_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_val_2390_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
else
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
lean_del_object(v___x_2388_);
lean_dec(v_a_2386_);
v___x_2399_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3);
v___x_2400_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2399_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
return v___x_2400_;
}
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
v_a_2402_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2385_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2385_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec(v_a_2380_);
lean_dec_ref(v_rhs_2348_);
v_a_2410_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2383_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2383_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
else
{
lean_dec(v_a_2365_);
lean_dec_ref(v_rhs_2348_);
lean_dec_ref(v_lhs_2347_);
return v___x_2379_;
}
}
}
else
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
lean_dec(v_a_2368_);
lean_dec(v_a_2365_);
lean_dec_ref(v_rhs_2348_);
lean_dec_ref(v_lhs_2347_);
v_a_2418_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2370_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2370_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec(v_a_2365_);
lean_dec_ref(v_rhs_2348_);
lean_dec_ref(v_lhs_2347_);
v_a_2426_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2367_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2367_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_dec_ref(v_rhs_2348_);
lean_dec_ref(v_lhs_2347_);
v_a_2434_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2364_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2364_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
else
{
lean_object* v___x_2442_; 
lean_dec_ref(v_rhs_2348_);
v___x_2442_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(v_lhs_2347_, v_heq_2349_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
return v___x_2442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(lean_object* v_thm_2443_, lean_object* v_lhs_2444_, lean_object* v_rhs_2445_, lean_object* v_i_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v___x_2458_; uint8_t v___x_2459_; 
v___x_2458_ = lean_unsigned_to_nat(0u);
v___x_2459_ = lean_nat_dec_lt(v___x_2458_, v_i_2446_);
if (v___x_2459_ == 0)
{
lean_object* v_proof_2460_; lean_object* v___x_2461_; 
v_proof_2460_ = lean_ctor_get(v_thm_2443_, 1);
lean_inc_ref(v_proof_2460_);
v___x_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2461_, 0, v_proof_2460_);
return v___x_2461_;
}
else
{
lean_object* v___x_2462_; lean_object* v_i_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2462_ = lean_unsigned_to_nat(1u);
v_i_2463_ = lean_nat_sub(v_i_2446_, v___x_2462_);
v___x_2464_ = l_Lean_Expr_appFn_x21(v_lhs_2444_);
v___x_2465_ = l_Lean_Expr_appFn_x21(v_rhs_2445_);
v___x_2466_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_2443_, v___x_2464_, v___x_2465_, v_i_2463_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
lean_dec_ref(v___x_2465_);
lean_dec_ref(v___x_2464_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v_argKinds_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; uint8_t v___y_2472_; uint8_t v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
lean_dec_ref_known(v___x_2466_, 1);
v_argKinds_2468_ = lean_ctor_get(v_thm_2443_, 2);
v___x_2469_ = l_Lean_Expr_appArg_x21(v_lhs_2444_);
v___x_2470_ = l_Lean_Expr_appArg_x21(v_rhs_2445_);
v___x_2483_ = 0;
v___x_2484_ = lean_box(v___x_2483_);
v___x_2485_ = lean_array_get(v___x_2484_, v_argKinds_2468_, v_i_2463_);
lean_dec(v_i_2463_);
lean_dec(v___x_2484_);
v___x_2486_ = lean_unbox(v___x_2485_);
lean_dec(v___x_2485_);
if (v___x_2486_ == 4)
{
v___y_2472_ = v___x_2459_;
goto v___jp_2471_;
}
else
{
uint8_t v___x_2487_; 
v___x_2487_ = 0;
v___y_2472_ = v___x_2487_;
goto v___jp_2471_;
}
v___jp_2471_:
{
lean_object* v___x_2473_; 
lean_inc_ref(v___x_2470_);
lean_inc_ref(v___x_2469_);
v___x_2473_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___x_2469_, v___x_2470_, v___y_2472_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2482_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2476_ = v___x_2473_;
v_isShared_2477_ = v_isSharedCheck_2482_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2473_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2482_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2478_; lean_object* v___x_2480_; 
v___x_2478_ = l_Lean_mkApp3(v_a_2467_, v___x_2469_, v___x_2470_, v_a_2474_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 0, v___x_2478_);
v___x_2480_ = v___x_2476_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2478_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
else
{
lean_dec_ref(v___x_2470_);
lean_dec_ref(v___x_2469_);
lean_dec(v_a_2467_);
return v___x_2473_;
}
}
}
else
{
lean_dec(v_i_2463_);
return v___x_2466_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(lean_object* v_f_2491_, lean_object* v_g_2492_, lean_object* v_numArgs_2493_, lean_object* v_lhs_2494_, lean_object* v_rhs_2495_, uint8_t v_heq_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v___x_2508_; 
lean_inc(v_numArgs_2493_);
lean_inc_ref(v_f_2491_);
v___x_2508_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(v_f_2491_, v_numArgs_2493_, v_a_2500_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v_argKinds_2510_; lean_object* v___x_2511_; uint8_t v___x_2512_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2509_);
lean_dec_ref_known(v___x_2508_, 1);
v_argKinds_2510_ = lean_ctor_get(v_a_2509_, 2);
v___x_2511_ = lean_array_get_size(v_argKinds_2510_);
v___x_2512_ = lean_nat_dec_eq(v___x_2511_, v_numArgs_2493_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
lean_dec(v_a_2509_);
lean_dec_ref(v_rhs_2495_);
lean_dec_ref(v_lhs_2494_);
lean_dec(v_numArgs_2493_);
lean_dec_ref(v_g_2492_);
lean_dec_ref(v_f_2491_);
v___x_2513_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2);
v___x_2514_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2513_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
return v___x_2514_;
}
else
{
lean_object* v___x_2515_; 
v___x_2515_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_2509_, v_lhs_2494_, v_rhs_2495_, v_numArgs_2493_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
lean_dec(v_a_2509_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; size_t v___x_2517_; size_t v___x_2518_; uint8_t v___x_2519_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref_known(v___x_2515_, 1);
v___x_2517_ = lean_ptr_addr(v_f_2491_);
v___x_2518_ = lean_ptr_addr(v_g_2492_);
v___x_2519_ = lean_usize_dec_eq(v___x_2517_, v___x_2518_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__4));
v___x_2521_ = l_Lean_Core_mkFreshUserName(v___x_2520_, v_a_2505_, v_a_2506_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___x_2523_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_a_2522_);
lean_dec_ref_known(v___x_2521_, 1);
lean_inc(v_a_2506_);
lean_inc_ref(v_a_2505_);
lean_inc(v_a_2504_);
lean_inc_ref(v_a_2503_);
lean_inc_ref(v_f_2491_);
v___x_2523_ = lean_infer_type(v_f_2491_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___f_2527_; lean_object* v___x_2528_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2523_, 1);
v___x_2525_ = lean_box(v___x_2519_);
v___x_2526_ = lean_box(v___x_2512_);
v___f_2527_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___boxed), 17, 5);
lean_closure_set(v___f_2527_, 0, v_numArgs_2493_);
lean_closure_set(v___f_2527_, 1, v_rhs_2495_);
lean_closure_set(v___f_2527_, 2, v_lhs_2494_);
lean_closure_set(v___f_2527_, 3, v___x_2525_);
lean_closure_set(v___f_2527_, 4, v___x_2526_);
v___x_2528_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_a_2522_, v_a_2524_, v___f_2527_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2530_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref_known(v___x_2528_, 1);
v___x_2530_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_f_2491_, v_g_2492_, v___x_2519_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2532_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2530_, 1);
v___x_2532_ = l_Lean_Meta_mkEqNDRec(v_a_2529_, v_a_2516_, v_a_2531_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2534_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v___x_2532_, 1);
v___x_2534_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_2533_, v_heq_2496_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
return v___x_2534_;
}
else
{
return v___x_2532_;
}
}
else
{
lean_dec(v_a_2529_);
lean_dec(v_a_2516_);
return v___x_2530_;
}
}
else
{
lean_dec(v_a_2516_);
lean_dec_ref(v_g_2492_);
lean_dec_ref(v_f_2491_);
return v___x_2528_;
}
}
else
{
lean_dec(v_a_2522_);
lean_dec(v_a_2516_);
lean_dec_ref(v_rhs_2495_);
lean_dec_ref(v_lhs_2494_);
lean_dec(v_numArgs_2493_);
lean_dec_ref(v_g_2492_);
lean_dec_ref(v_f_2491_);
return v___x_2523_;
}
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec(v_a_2516_);
lean_dec_ref(v_rhs_2495_);
lean_dec_ref(v_lhs_2494_);
lean_dec(v_numArgs_2493_);
lean_dec_ref(v_g_2492_);
lean_dec_ref(v_f_2491_);
v_a_2535_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2521_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2521_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
else
{
lean_object* v___x_2543_; 
lean_dec_ref(v_rhs_2495_);
lean_dec_ref(v_lhs_2494_);
lean_dec(v_numArgs_2493_);
lean_dec_ref(v_g_2492_);
lean_dec_ref(v_f_2491_);
v___x_2543_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_2516_, v_heq_2496_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
return v___x_2543_;
}
}
else
{
lean_dec_ref(v_rhs_2495_);
lean_dec_ref(v_lhs_2494_);
lean_dec(v_numArgs_2493_);
lean_dec_ref(v_g_2492_);
lean_dec_ref(v_f_2491_);
return v___x_2515_;
}
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec_ref(v_rhs_2495_);
lean_dec_ref(v_lhs_2494_);
lean_dec(v_numArgs_2493_);
lean_dec_ref(v_g_2492_);
lean_dec_ref(v_f_2491_);
v_a_2544_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2508_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2508_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1(void){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2553_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2554_ = lean_unsigned_to_nat(27u);
v___x_2555_ = lean_unsigned_to_nat(237u);
v___x_2556_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0));
v___x_2557_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2558_ = l_mkPanicMessageWithDecl(v___x_2557_, v___x_2556_, v___x_2555_, v___x_2554_, v___x_2553_);
return v___x_2558_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2(void){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2559_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2));
v___x_2560_ = lean_unsigned_to_nat(27u);
v___x_2561_ = lean_unsigned_to_nat(236u);
v___x_2562_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0));
v___x_2563_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0));
v___x_2564_ = l_mkPanicMessageWithDecl(v___x_2563_, v___x_2562_, v___x_2561_, v___x_2560_, v___x_2559_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(lean_object* v_lhs_2565_, lean_object* v_rhs_2566_, uint8_t v_heq_2567_, lean_object* v_e_u2081_2568_, lean_object* v_e_u2082_2569_, lean_object* v_numArgs_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_){
_start:
{
if (lean_obj_tag(v_e_u2081_2568_) == 5)
{
if (lean_obj_tag(v_e_u2082_2569_) == 5)
{
lean_object* v_fn_2582_; lean_object* v_fn_2583_; lean_object* v___x_2584_; lean_object* v_numArgs_2585_; size_t v___x_2586_; size_t v___x_2587_; uint8_t v___x_2588_; 
v_fn_2582_ = lean_ctor_get(v_e_u2081_2568_, 0);
lean_inc_ref(v_fn_2582_);
lean_dec_ref_known(v_e_u2081_2568_, 2);
v_fn_2583_ = lean_ctor_get(v_e_u2082_2569_, 0);
lean_inc_ref(v_fn_2583_);
lean_dec_ref_known(v_e_u2082_2569_, 2);
v___x_2584_ = lean_unsigned_to_nat(1u);
v_numArgs_2585_ = lean_nat_add(v_numArgs_2570_, v___x_2584_);
lean_dec(v_numArgs_2570_);
v___x_2586_ = lean_ptr_addr(v_fn_2582_);
v___x_2587_ = lean_ptr_addr(v_fn_2583_);
v___x_2588_ = lean_usize_dec_eq(v___x_2586_, v___x_2587_);
if (v___x_2588_ == 0)
{
lean_object* v___x_2589_; 
lean_inc_ref(v_fn_2583_);
lean_inc_ref(v_fn_2582_);
v___x_2589_ = l_Lean_Meta_Grind_hasSameType(v_fn_2582_, v_fn_2583_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; uint8_t v___x_2591_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref_known(v___x_2589_, 1);
v___x_2591_ = lean_unbox(v_a_2590_);
lean_dec(v_a_2590_);
if (v___x_2591_ == 0)
{
v_e_u2081_2568_ = v_fn_2582_;
v_e_u2082_2569_ = v_fn_2583_;
v_numArgs_2570_ = v_numArgs_2585_;
goto _start;
}
else
{
lean_object* v___x_2593_; 
v___x_2593_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_2582_, v_fn_2583_, v_numArgs_2585_, v_lhs_2565_, v_rhs_2566_, v_heq_2567_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_);
return v___x_2593_;
}
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec(v_numArgs_2585_);
lean_dec_ref(v_fn_2583_);
lean_dec_ref(v_fn_2582_);
lean_dec_ref(v_rhs_2566_);
lean_dec_ref(v_lhs_2565_);
v_a_2594_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2589_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2589_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
else
{
lean_object* v___x_2602_; 
v___x_2602_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_2582_, v_fn_2583_, v_numArgs_2585_, v_lhs_2565_, v_rhs_2566_, v_heq_2567_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_);
return v___x_2602_;
}
}
else
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
lean_dec_ref_known(v_e_u2081_2568_, 2);
lean_dec(v_numArgs_2570_);
lean_dec_ref(v_e_u2082_2569_);
lean_dec_ref(v_rhs_2566_);
lean_dec_ref(v_lhs_2565_);
v___x_2603_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1);
v___x_2604_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2603_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_);
return v___x_2604_;
}
}
else
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
lean_dec(v_numArgs_2570_);
lean_dec_ref(v_e_u2082_2569_);
lean_dec_ref(v_e_u2081_2568_);
lean_dec_ref(v_rhs_2566_);
lean_dec_ref(v_lhs_2565_);
v___x_2605_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2);
v___x_2606_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2605_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_);
return v___x_2606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(lean_object* v_lhs_2607_, lean_object* v_rhs_2608_, uint8_t v_heq_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_rhs_2608_);
lean_inc_ref(v_lhs_2607_);
v___x_2622_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(v_lhs_2607_, v_rhs_2608_, v_heq_2609_, v_lhs_2607_, v_rhs_2608_, v___x_2621_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC___boxed(lean_object* v_lhs_2623_, lean_object* v_rhs_2624_, lean_object* v_heq_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_){
_start:
{
uint8_t v_heq_boxed_2637_; lean_object* v_res_2638_; 
v_heq_boxed_2637_ = lean_unbox(v_heq_2625_);
v_res_2638_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_2623_, v_rhs_2624_, v_heq_boxed_2637_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_);
lean_dec(v_a_2635_);
lean_dec_ref(v_a_2634_);
lean_dec(v_a_2633_);
lean_dec_ref(v_a_2632_);
lean_dec(v_a_2631_);
lean_dec_ref(v_a_2630_);
lean_dec(v_a_2629_);
lean_dec_ref(v_a_2628_);
lean_dec(v_a_2627_);
lean_dec(v_a_2626_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___boxed(lean_object* v_lhs_2639_, lean_object* v_rhs_2640_, lean_object* v_heq_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_){
_start:
{
uint8_t v_heq_boxed_2653_; lean_object* v_res_2654_; 
v_heq_boxed_2653_ = lean_unbox(v_heq_2641_);
v_res_2654_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_2639_, v_rhs_2640_, v_heq_boxed_2653_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
lean_dec(v_a_2651_);
lean_dec_ref(v_a_2650_);
lean_dec(v_a_2649_);
lean_dec_ref(v_a_2648_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec(v_a_2642_);
lean_dec_ref(v_rhs_2640_);
lean_dec_ref(v_lhs_2639_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___boxed(lean_object* v_lhs_2655_, lean_object* v_rhs_2656_, lean_object* v_heq_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
uint8_t v_heq_boxed_2669_; lean_object* v_res_2670_; 
v_heq_boxed_2669_ = lean_unbox(v_heq_2657_);
v_res_2670_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_2655_, v_rhs_2656_, v_heq_boxed_2669_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
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
lean_dec_ref(v_rhs_2656_);
lean_dec_ref(v_lhs_2655_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof___boxed(lean_object* v_lhs_2671_, lean_object* v_rhs_2672_, lean_object* v_h_2673_, lean_object* v_flipped_2674_, lean_object* v_heq_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
uint8_t v_flipped_boxed_2687_; uint8_t v_heq_boxed_2688_; lean_object* v_res_2689_; 
v_flipped_boxed_2687_ = lean_unbox(v_flipped_2674_);
v_heq_boxed_2688_ = lean_unbox(v_heq_2675_);
v_res_2689_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_lhs_2671_, v_rhs_2672_, v_h_2673_, v_flipped_boxed_2687_, v_heq_boxed_2688_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec(v_a_2676_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___boxed(lean_object* v_lhs_2690_, lean_object* v_rhs_2691_, lean_object* v_heq_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_){
_start:
{
uint8_t v_heq_boxed_2704_; lean_object* v_res_2705_; 
v_heq_boxed_2704_ = lean_unbox(v_heq_2692_);
v_res_2705_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_2690_, v_rhs_2691_, v_heq_boxed_2704_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
lean_dec(v_a_2702_);
lean_dec_ref(v_a_2701_);
lean_dec(v_a_2700_);
lean_dec_ref(v_a_2699_);
lean_dec(v_a_2698_);
lean_dec_ref(v_a_2697_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
lean_dec(v_a_2694_);
lean_dec(v_a_2693_);
lean_dec_ref(v_rhs_2691_);
lean_dec_ref(v_lhs_2690_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper___boxed(lean_object* v_thm_2706_, lean_object* v_lhs_2707_, lean_object* v_rhs_2708_, lean_object* v_i_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_2706_, v_lhs_2707_, v_rhs_2708_, v_i_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
lean_dec(v_a_2711_);
lean_dec(v_a_2710_);
lean_dec(v_i_2709_);
lean_dec_ref(v_rhs_2708_);
lean_dec_ref(v_lhs_2707_);
lean_dec_ref(v_thm_2706_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___boxed(lean_object** _args){
lean_object* v_lhs_2722_ = _args[0];
lean_object* v_rhs_2723_ = _args[1];
lean_object* v_heq_2724_ = _args[2];
lean_object* v_e_u2081_2725_ = _args[3];
lean_object* v_e_u2082_2726_ = _args[4];
lean_object* v_numArgs_2727_ = _args[5];
lean_object* v_a_2728_ = _args[6];
lean_object* v_a_2729_ = _args[7];
lean_object* v_a_2730_ = _args[8];
lean_object* v_a_2731_ = _args[9];
lean_object* v_a_2732_ = _args[10];
lean_object* v_a_2733_ = _args[11];
lean_object* v_a_2734_ = _args[12];
lean_object* v_a_2735_ = _args[13];
lean_object* v_a_2736_ = _args[14];
lean_object* v_a_2737_ = _args[15];
lean_object* v_a_2738_ = _args[16];
_start:
{
uint8_t v_heq_boxed_2739_; lean_object* v_res_2740_; 
v_heq_boxed_2739_ = lean_unbox(v_heq_2724_);
v_res_2740_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(v_lhs_2722_, v_rhs_2723_, v_heq_boxed_2739_, v_e_u2081_2725_, v_e_u2082_2726_, v_numArgs_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
lean_dec(v_a_2737_);
lean_dec_ref(v_a_2736_);
lean_dec(v_a_2735_);
lean_dec_ref(v_a_2734_);
lean_dec(v_a_2733_);
lean_dec_ref(v_a_2732_);
lean_dec(v_a_2731_);
lean_dec_ref(v_a_2730_);
lean_dec(v_a_2729_);
lean_dec(v_a_2728_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___boxed(lean_object* v_lhs_2741_, lean_object* v_common_2742_, lean_object* v_acc_2743_, lean_object* v_heq_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_){
_start:
{
uint8_t v_heq_boxed_2756_; lean_object* v_res_2757_; 
v_heq_boxed_2756_ = lean_unbox(v_heq_2744_);
v_res_2757_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_2741_, v_common_2742_, v_acc_2743_, v_heq_boxed_2756_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_);
lean_dec(v_a_2754_);
lean_dec_ref(v_a_2753_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
lean_dec(v_a_2746_);
lean_dec(v_a_2745_);
lean_dec_ref(v_common_2742_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___boxed(lean_object** _args){
lean_object* v_f_2758_ = _args[0];
lean_object* v_g_2759_ = _args[1];
lean_object* v_numArgs_2760_ = _args[2];
lean_object* v_lhs_2761_ = _args[3];
lean_object* v_rhs_2762_ = _args[4];
lean_object* v_heq_2763_ = _args[5];
lean_object* v_a_2764_ = _args[6];
lean_object* v_a_2765_ = _args[7];
lean_object* v_a_2766_ = _args[8];
lean_object* v_a_2767_ = _args[9];
lean_object* v_a_2768_ = _args[10];
lean_object* v_a_2769_ = _args[11];
lean_object* v_a_2770_ = _args[12];
lean_object* v_a_2771_ = _args[13];
lean_object* v_a_2772_ = _args[14];
lean_object* v_a_2773_ = _args[15];
lean_object* v_a_2774_ = _args[16];
_start:
{
uint8_t v_heq_boxed_2775_; lean_object* v_res_2776_; 
v_heq_boxed_2775_ = lean_unbox(v_heq_2763_);
v_res_2776_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_2758_, v_g_2759_, v_numArgs_2760_, v_lhs_2761_, v_rhs_2762_, v_heq_boxed_2775_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_a_2765_);
lean_dec(v_a_2764_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___boxed(lean_object* v_rhs_2777_, lean_object* v_common_2778_, lean_object* v_lhsEqCommon_x3f_2779_, lean_object* v_heq_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
uint8_t v_heq_boxed_2792_; lean_object* v_res_2793_; 
v_heq_boxed_2792_ = lean_unbox(v_heq_2780_);
v_res_2793_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_2777_, v_common_2778_, v_lhsEqCommon_x3f_2779_, v_heq_boxed_2792_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_);
lean_dec(v_a_2790_);
lean_dec_ref(v_a_2789_);
lean_dec(v_a_2788_);
lean_dec_ref(v_a_2787_);
lean_dec(v_a_2786_);
lean_dec_ref(v_a_2785_);
lean_dec(v_a_2784_);
lean_dec_ref(v_a_2783_);
lean_dec(v_a_2782_);
lean_dec(v_a_2781_);
lean_dec_ref(v_common_2778_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___boxed(lean_object* v_lhs_2794_, lean_object* v_rhs_2795_, lean_object* v_heq_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_){
_start:
{
uint8_t v_heq_boxed_2808_; lean_object* v_res_2809_; 
v_heq_boxed_2808_ = lean_unbox(v_heq_2796_);
v_res_2809_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_2794_, v_rhs_2795_, v_heq_boxed_2808_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
lean_dec(v_a_2798_);
lean_dec(v_a_2797_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop___boxed(lean_object* v_lhs_2810_, lean_object* v_rhs_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_2810_, v_rhs_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
lean_dec(v_a_2821_);
lean_dec_ref(v_a_2820_);
lean_dec(v_a_2819_);
lean_dec_ref(v_a_2818_);
lean_dec(v_a_2817_);
lean_dec_ref(v_a_2816_);
lean_dec(v_a_2815_);
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2813_);
lean_dec(v_a_2812_);
lean_dec_ref(v_rhs_2811_);
lean_dec_ref(v_lhs_2810_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___boxed(lean_object* v_lhs_2824_, lean_object* v_rhs_2825_, lean_object* v_heq_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_){
_start:
{
uint8_t v_heq_boxed_2838_; lean_object* v_res_2839_; 
v_heq_boxed_2838_ = lean_unbox(v_heq_2826_);
v_res_2839_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_lhs_2824_, v_rhs_2825_, v_heq_boxed_2838_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
lean_dec(v_a_2836_);
lean_dec_ref(v_a_2835_);
lean_dec(v_a_2834_);
lean_dec_ref(v_a_2833_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
lean_dec(v_a_2828_);
lean_dec(v_a_2827_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrProof___boxed(lean_object* v_lhs_2840_, lean_object* v_rhs_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_Meta_Grind_mkEqCongrProof(v_lhs_2840_, v_rhs_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
lean_dec(v_a_2847_);
lean_dec_ref(v_a_2846_);
lean_dec(v_a_2845_);
lean_dec_ref(v_a_2844_);
lean_dec(v_a_2843_);
lean_dec(v_a_2842_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___boxed(lean_object* v_lhs_2854_, lean_object* v_rhs_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(v_lhs_2854_, v_rhs_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_);
lean_dec(v_a_2865_);
lean_dec_ref(v_a_2864_);
lean_dec(v_a_2863_);
lean_dec_ref(v_a_2862_);
lean_dec(v_a_2861_);
lean_dec_ref(v_a_2860_);
lean_dec(v_a_2859_);
lean_dec_ref(v_a_2858_);
lean_dec(v_a_2857_);
lean_dec(v_a_2856_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___boxed(lean_object* v_lhs_2868_, lean_object* v_rhs_2869_, lean_object* v_heq_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_){
_start:
{
uint8_t v_heq_boxed_2882_; lean_object* v_res_2883_; 
v_heq_boxed_2882_ = lean_unbox(v_heq_2870_);
v_res_2883_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(v_lhs_2868_, v_rhs_2869_, v_heq_boxed_2882_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_);
lean_dec(v_a_2880_);
lean_dec_ref(v_a_2879_);
lean_dec(v_a_2878_);
lean_dec_ref(v_a_2877_);
lean_dec(v_a_2876_);
lean_dec_ref(v_a_2875_);
lean_dec(v_a_2874_);
lean_dec_ref(v_a_2873_);
lean_dec(v_a_2872_);
lean_dec(v_a_2871_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(lean_object* v_00_u03b1_2884_, lean_object* v_ref_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_2885_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___boxed(lean_object* v_00_u03b1_2898_, lean_object* v_ref_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(v_00_u03b1_2898_, v_ref_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(lean_object* v_00_u03b1_2912_, lean_object* v_name_2913_, uint8_t v_bi_2914_, lean_object* v_type_2915_, lean_object* v_k_2916_, uint8_t v_kind_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_2913_, v_bi_2914_, v_type_2915_, v_k_2916_, v_kind_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___boxed(lean_object** _args){
lean_object* v_00_u03b1_2930_ = _args[0];
lean_object* v_name_2931_ = _args[1];
lean_object* v_bi_2932_ = _args[2];
lean_object* v_type_2933_ = _args[3];
lean_object* v_k_2934_ = _args[4];
lean_object* v_kind_2935_ = _args[5];
lean_object* v___y_2936_ = _args[6];
lean_object* v___y_2937_ = _args[7];
lean_object* v___y_2938_ = _args[8];
lean_object* v___y_2939_ = _args[9];
lean_object* v___y_2940_ = _args[10];
lean_object* v___y_2941_ = _args[11];
lean_object* v___y_2942_ = _args[12];
lean_object* v___y_2943_ = _args[13];
lean_object* v___y_2944_ = _args[14];
lean_object* v___y_2945_ = _args[15];
lean_object* v___y_2946_ = _args[16];
_start:
{
uint8_t v_bi_boxed_2947_; uint8_t v_kind_boxed_2948_; lean_object* v_res_2949_; 
v_bi_boxed_2947_ = lean_unbox(v_bi_2932_);
v_kind_boxed_2948_ = lean_unbox(v_kind_2935_);
v_res_2949_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(v_00_u03b1_2930_, v_name_2931_, v_bi_boxed_2947_, v_type_2933_, v_k_2934_, v_kind_boxed_2948_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec(v___y_2936_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(lean_object* v_00_u03b1_2950_, lean_object* v_name_2951_, lean_object* v_type_2952_, lean_object* v_k_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_name_2951_, v_type_2952_, v_k_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___boxed(lean_object* v_00_u03b1_2966_, lean_object* v_name_2967_, lean_object* v_type_2968_, lean_object* v_k_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(v_00_u03b1_2966_, v_name_2967_, v_type_2968_, v_k_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec(v___y_2970_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(lean_object* v_00_u03b1_2982_, lean_object* v_msg_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v_msg_2983_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___boxed(lean_object* v_00_u03b1_2996_, lean_object* v_msg_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(v_00_u03b1_2996_, v_msg_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
return v_res_3009_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__1(void){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3011_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__0));
v___x_3012_ = l_Lean_stringToMessageData(v___x_3011_);
return v___x_3012_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__3(void){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3014_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__2));
v___x_3015_ = l_Lean_stringToMessageData(v___x_3014_);
return v___x_3015_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__5(void){
_start:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__4));
v___x_3018_ = l_Lean_stringToMessageData(v___x_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* lean_grind_mk_eq_proof(lean_object* v_a_3019_, lean_object* v_b_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_){
_start:
{
lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___x_3045_; 
lean_inc_ref(v_b_3020_);
lean_inc_ref(v_a_3019_);
v___x_3045_ = l_Lean_Meta_Grind_hasSameType(v_a_3019_, v_b_3020_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; uint8_t v___x_3047_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_a_3046_);
lean_dec_ref_known(v___x_3045_, 1);
v___x_3047_ = lean_unbox(v_a_3046_);
lean_dec(v_a_3046_);
if (v___x_3047_ == 0)
{
lean_object* v___x_3048_; 
lean_dec(v_a_3026_);
lean_dec_ref(v_a_3025_);
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
lean_dec(v_a_3022_);
lean_dec(v_a_3021_);
lean_inc(v_a_3030_);
lean_inc_ref(v_a_3029_);
lean_inc(v_a_3028_);
lean_inc_ref(v_a_3027_);
lean_inc_ref(v_a_3019_);
v___x_3048_ = lean_infer_type(v_a_3019_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3050_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3048_, 1);
lean_inc(v_a_3030_);
lean_inc_ref(v_a_3029_);
lean_inc(v_a_3028_);
lean_inc_ref(v_a_3027_);
lean_inc_ref(v_b_3020_);
v___x_3050_ = lean_infer_type(v_b_3020_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref_known(v___x_3050_, 1);
v___x_3052_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__1, &l_Lean_Meta_Grind_mkEqProofImpl___closed__1_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__1);
v___x_3053_ = l_Lean_indentExpr(v_a_3019_);
v___x_3054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3052_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__3, &l_Lean_Meta_Grind_mkEqProofImpl___closed__3_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__3);
v___x_3056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3054_);
lean_ctor_set(v___x_3056_, 1, v___x_3055_);
v___x_3057_ = l_Lean_indentExpr(v_a_3049_);
v___x_3058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3056_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
v___x_3059_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__5, &l_Lean_Meta_Grind_mkEqProofImpl___closed__5_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__5);
v___x_3060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3058_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
v___x_3061_ = l_Lean_indentExpr(v_b_3020_);
v___x_3062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3060_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
v___x_3063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
lean_ctor_set(v___x_3063_, 1, v___x_3055_);
v___x_3064_ = l_Lean_indentExpr(v_a_3051_);
v___x_3065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3063_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
v___x_3066_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v___x_3065_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
lean_dec(v_a_3028_);
lean_dec_ref(v_a_3027_);
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3066_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3066_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
else
{
lean_dec(v_a_3049_);
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
lean_dec(v_a_3028_);
lean_dec_ref(v_a_3027_);
lean_dec_ref(v_b_3020_);
lean_dec_ref(v_a_3019_);
return v___x_3050_;
}
}
else
{
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
lean_dec(v_a_3028_);
lean_dec_ref(v_a_3027_);
lean_dec_ref(v_b_3020_);
lean_dec_ref(v_a_3019_);
return v___x_3048_;
}
}
else
{
v___y_3033_ = v_a_3021_;
v___y_3034_ = v_a_3022_;
v___y_3035_ = v_a_3023_;
v___y_3036_ = v_a_3024_;
v___y_3037_ = v_a_3025_;
v___y_3038_ = v_a_3026_;
v___y_3039_ = v_a_3027_;
v___y_3040_ = v_a_3028_;
v___y_3041_ = v_a_3029_;
v___y_3042_ = v_a_3030_;
goto v___jp_3032_;
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
lean_dec(v_a_3028_);
lean_dec_ref(v_a_3027_);
lean_dec(v_a_3026_);
lean_dec_ref(v_a_3025_);
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
lean_dec(v_a_3022_);
lean_dec(v_a_3021_);
lean_dec_ref(v_b_3020_);
lean_dec_ref(v_a_3019_);
v_a_3075_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_3045_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3045_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
v___jp_3032_:
{
uint8_t v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = 0;
v___x_3044_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_3019_, v_b_3020_, v___x_3043_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec(v___y_3033_);
return v___x_3044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqProofImpl___boxed(lean_object* v_a_3083_, lean_object* v_b_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = lean_grind_mk_eq_proof(v_a_3083_, v_b_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* lean_grind_mk_heq_proof(lean_object* v_a_3097_, lean_object* v_b_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_){
_start:
{
uint8_t v___x_3110_; lean_object* v___x_3111_; 
v___x_3110_ = 1;
v___x_3111_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_3097_, v_b_3098_, v___x_3110_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_, v_a_3108_);
lean_dec(v_a_3108_);
lean_dec_ref(v_a_3107_);
lean_dec(v_a_3106_);
lean_dec_ref(v_a_3105_);
lean_dec(v_a_3104_);
lean_dec_ref(v_a_3103_);
lean_dec(v_a_3102_);
lean_dec_ref(v_a_3101_);
lean_dec(v_a_3100_);
lean_dec(v_a_3099_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHEqProofImpl___boxed(lean_object* v_a_3112_, lean_object* v_b_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = lean_grind_mk_heq_proof(v_a_3112_, v_b_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_);
return v_res_3125_;
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
