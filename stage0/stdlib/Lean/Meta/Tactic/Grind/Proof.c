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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Meta.Tactic.Grind.Proof"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "_private.Lean.Meta.Tactic.Grind.Proof.0.Lean.Meta.Grind.findCommon"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__1_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__3;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_10_);
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
lean_dec_ref(v___x_101_);
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
lean_dec_ref(v___x_104_);
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
lean_dec_ref(v_h_u2081_163_);
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
lean_object* v___x_215_; lean_object* v___x_8578__overap_216_; lean_object* v___x_217_; 
v___x_215_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0);
v___x_8578__overap_216_ = lean_panic_fn_borrowed(v___x_215_, v_msg_203_);
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
v___x_217_ = lean_apply_11(v___x_8578__overap_216_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, lean_box(0));
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
lean_object* v___x_244_; lean_object* v___x_9377__overap_245_; lean_object* v___x_246_; 
v___x_244_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0);
v___x_9377__overap_245_ = lean_panic_fn_borrowed(v___x_244_, v_msg_232_);
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
v___x_246_ = lean_apply_11(v___x_9377__overap_245_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, lean_box(0));
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(lean_object* v_k_260_, lean_object* v_v_261_, lean_object* v_t_262_){
_start:
{
if (lean_obj_tag(v_t_262_) == 0)
{
lean_object* v_size_263_; lean_object* v_k_264_; lean_object* v_v_265_; lean_object* v_l_266_; lean_object* v_r_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_548_; 
v_size_263_ = lean_ctor_get(v_t_262_, 0);
v_k_264_ = lean_ctor_get(v_t_262_, 1);
v_v_265_ = lean_ctor_get(v_t_262_, 2);
v_l_266_ = lean_ctor_get(v_t_262_, 3);
v_r_267_ = lean_ctor_get(v_t_262_, 4);
v_isSharedCheck_548_ = !lean_is_exclusive(v_t_262_);
if (v_isSharedCheck_548_ == 0)
{
v___x_269_ = v_t_262_;
v_isShared_270_ = v_isSharedCheck_548_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_r_267_);
lean_inc(v_l_266_);
lean_inc(v_v_265_);
lean_inc(v_k_264_);
lean_inc(v_size_263_);
lean_dec(v_t_262_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_548_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
uint8_t v___x_271_; 
v___x_271_ = lean_nat_dec_lt(v_k_260_, v_k_264_);
if (v___x_271_ == 0)
{
uint8_t v___x_272_; 
v___x_272_ = lean_nat_dec_eq(v_k_260_, v_k_264_);
if (v___x_272_ == 0)
{
lean_object* v_impl_273_; lean_object* v___x_274_; 
lean_dec(v_size_263_);
v_impl_273_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_k_260_, v_v_261_, v_r_267_);
v___x_274_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_266_) == 0)
{
lean_object* v_size_275_; lean_object* v_size_276_; lean_object* v_k_277_; lean_object* v_v_278_; lean_object* v_l_279_; lean_object* v_r_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v_size_275_ = lean_ctor_get(v_l_266_, 0);
v_size_276_ = lean_ctor_get(v_impl_273_, 0);
lean_inc(v_size_276_);
v_k_277_ = lean_ctor_get(v_impl_273_, 1);
lean_inc(v_k_277_);
v_v_278_ = lean_ctor_get(v_impl_273_, 2);
lean_inc(v_v_278_);
v_l_279_ = lean_ctor_get(v_impl_273_, 3);
lean_inc(v_l_279_);
v_r_280_ = lean_ctor_get(v_impl_273_, 4);
lean_inc(v_r_280_);
v___x_281_ = lean_unsigned_to_nat(3u);
v___x_282_ = lean_nat_mul(v___x_281_, v_size_275_);
v___x_283_ = lean_nat_dec_lt(v___x_282_, v_size_276_);
lean_dec(v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
lean_dec(v_r_280_);
lean_dec(v_l_279_);
lean_dec(v_v_278_);
lean_dec(v_k_277_);
v___x_284_ = lean_nat_add(v___x_274_, v_size_275_);
v___x_285_ = lean_nat_add(v___x_284_, v_size_276_);
lean_dec(v_size_276_);
lean_dec(v___x_284_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 4, v_impl_273_);
lean_ctor_set(v___x_269_, 0, v___x_285_);
v___x_287_ = v___x_269_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_k_264_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v_v_265_);
lean_ctor_set(v_reuseFailAlloc_288_, 3, v_l_266_);
lean_ctor_set(v_reuseFailAlloc_288_, 4, v_impl_273_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
else
{
lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_352_; 
v_isSharedCheck_352_ = !lean_is_exclusive(v_impl_273_);
if (v_isSharedCheck_352_ == 0)
{
lean_object* v_unused_353_; lean_object* v_unused_354_; lean_object* v_unused_355_; lean_object* v_unused_356_; lean_object* v_unused_357_; 
v_unused_353_ = lean_ctor_get(v_impl_273_, 4);
lean_dec(v_unused_353_);
v_unused_354_ = lean_ctor_get(v_impl_273_, 3);
lean_dec(v_unused_354_);
v_unused_355_ = lean_ctor_get(v_impl_273_, 2);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v_impl_273_, 1);
lean_dec(v_unused_356_);
v_unused_357_ = lean_ctor_get(v_impl_273_, 0);
lean_dec(v_unused_357_);
v___x_290_ = v_impl_273_;
v_isShared_291_ = v_isSharedCheck_352_;
goto v_resetjp_289_;
}
else
{
lean_dec(v_impl_273_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_352_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v_size_292_; lean_object* v_k_293_; lean_object* v_v_294_; lean_object* v_l_295_; lean_object* v_r_296_; lean_object* v_size_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v_size_292_ = lean_ctor_get(v_l_279_, 0);
v_k_293_ = lean_ctor_get(v_l_279_, 1);
v_v_294_ = lean_ctor_get(v_l_279_, 2);
v_l_295_ = lean_ctor_get(v_l_279_, 3);
v_r_296_ = lean_ctor_get(v_l_279_, 4);
v_size_297_ = lean_ctor_get(v_r_280_, 0);
v___x_298_ = lean_unsigned_to_nat(2u);
v___x_299_ = lean_nat_mul(v___x_298_, v_size_297_);
v___x_300_ = lean_nat_dec_lt(v_size_292_, v___x_299_);
lean_dec(v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_328_; 
lean_inc(v_r_296_);
lean_inc(v_l_295_);
lean_inc(v_v_294_);
lean_inc(v_k_293_);
v_isSharedCheck_328_ = !lean_is_exclusive(v_l_279_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; lean_object* v_unused_330_; lean_object* v_unused_331_; lean_object* v_unused_332_; lean_object* v_unused_333_; 
v_unused_329_ = lean_ctor_get(v_l_279_, 4);
lean_dec(v_unused_329_);
v_unused_330_ = lean_ctor_get(v_l_279_, 3);
lean_dec(v_unused_330_);
v_unused_331_ = lean_ctor_get(v_l_279_, 2);
lean_dec(v_unused_331_);
v_unused_332_ = lean_ctor_get(v_l_279_, 1);
lean_dec(v_unused_332_);
v_unused_333_ = lean_ctor_get(v_l_279_, 0);
lean_dec(v_unused_333_);
v___x_302_ = v_l_279_;
v_isShared_303_ = v_isSharedCheck_328_;
goto v_resetjp_301_;
}
else
{
lean_dec(v_l_279_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_328_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_318_; 
v___x_304_ = lean_nat_add(v___x_274_, v_size_275_);
v___x_305_ = lean_nat_add(v___x_304_, v_size_276_);
lean_dec(v_size_276_);
if (lean_obj_tag(v_l_295_) == 0)
{
lean_object* v_size_326_; 
v_size_326_ = lean_ctor_get(v_l_295_, 0);
lean_inc(v_size_326_);
v___y_318_ = v_size_326_;
goto v___jp_317_;
}
else
{
lean_object* v___x_327_; 
v___x_327_ = lean_unsigned_to_nat(0u);
v___y_318_ = v___x_327_;
goto v___jp_317_;
}
v___jp_306_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = lean_nat_add(v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec(v___y_308_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 4, v_r_280_);
lean_ctor_set(v___x_302_, 3, v_r_296_);
lean_ctor_set(v___x_302_, 2, v_v_278_);
lean_ctor_set(v___x_302_, 1, v_k_277_);
lean_ctor_set(v___x_302_, 0, v___x_310_);
v___x_312_ = v___x_302_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_k_277_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_v_278_);
lean_ctor_set(v_reuseFailAlloc_316_, 3, v_r_296_);
lean_ctor_set(v_reuseFailAlloc_316_, 4, v_r_280_);
v___x_312_ = v_reuseFailAlloc_316_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_314_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 4, v___x_312_);
lean_ctor_set(v___x_290_, 3, v___y_307_);
lean_ctor_set(v___x_290_, 2, v_v_294_);
lean_ctor_set(v___x_290_, 1, v_k_293_);
lean_ctor_set(v___x_290_, 0, v___x_305_);
v___x_314_ = v___x_290_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_k_293_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_v_294_);
lean_ctor_set(v_reuseFailAlloc_315_, 3, v___y_307_);
lean_ctor_set(v_reuseFailAlloc_315_, 4, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
v___jp_317_:
{
lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_319_ = lean_nat_add(v___x_304_, v___y_318_);
lean_dec(v___y_318_);
lean_dec(v___x_304_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 4, v_l_295_);
lean_ctor_set(v___x_269_, 0, v___x_319_);
v___x_321_ = v___x_269_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_k_264_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v_v_265_);
lean_ctor_set(v_reuseFailAlloc_325_, 3, v_l_266_);
lean_ctor_set(v_reuseFailAlloc_325_, 4, v_l_295_);
v___x_321_ = v_reuseFailAlloc_325_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_322_; 
v___x_322_ = lean_nat_add(v___x_274_, v_size_297_);
if (lean_obj_tag(v_r_296_) == 0)
{
lean_object* v_size_323_; 
v_size_323_ = lean_ctor_get(v_r_296_, 0);
lean_inc(v_size_323_);
v___y_307_ = v___x_321_;
v___y_308_ = v___x_322_;
v___y_309_ = v_size_323_;
goto v___jp_306_;
}
else
{
lean_object* v___x_324_; 
v___x_324_ = lean_unsigned_to_nat(0u);
v___y_307_ = v___x_321_;
v___y_308_ = v___x_322_;
v___y_309_ = v___x_324_;
goto v___jp_306_;
}
}
}
}
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
lean_del_object(v___x_269_);
v___x_334_ = lean_nat_add(v___x_274_, v_size_275_);
v___x_335_ = lean_nat_add(v___x_334_, v_size_276_);
lean_dec(v_size_276_);
v___x_336_ = lean_nat_add(v___x_334_, v_size_292_);
lean_dec(v___x_334_);
lean_inc_ref(v_l_266_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 4, v_l_279_);
lean_ctor_set(v___x_290_, 3, v_l_266_);
lean_ctor_set(v___x_290_, 2, v_v_265_);
lean_ctor_set(v___x_290_, 1, v_k_264_);
lean_ctor_set(v___x_290_, 0, v___x_336_);
v___x_338_ = v___x_290_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_k_264_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v_v_265_);
lean_ctor_set(v_reuseFailAlloc_351_, 3, v_l_266_);
lean_ctor_set(v_reuseFailAlloc_351_, 4, v_l_279_);
v___x_338_ = v_reuseFailAlloc_351_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
v_isSharedCheck_345_ = !lean_is_exclusive(v_l_266_);
if (v_isSharedCheck_345_ == 0)
{
lean_object* v_unused_346_; lean_object* v_unused_347_; lean_object* v_unused_348_; lean_object* v_unused_349_; lean_object* v_unused_350_; 
v_unused_346_ = lean_ctor_get(v_l_266_, 4);
lean_dec(v_unused_346_);
v_unused_347_ = lean_ctor_get(v_l_266_, 3);
lean_dec(v_unused_347_);
v_unused_348_ = lean_ctor_get(v_l_266_, 2);
lean_dec(v_unused_348_);
v_unused_349_ = lean_ctor_get(v_l_266_, 1);
lean_dec(v_unused_349_);
v_unused_350_ = lean_ctor_get(v_l_266_, 0);
lean_dec(v_unused_350_);
v___x_340_ = v_l_266_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_dec(v_l_266_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 4, v_r_280_);
lean_ctor_set(v___x_340_, 3, v___x_338_);
lean_ctor_set(v___x_340_, 2, v_v_278_);
lean_ctor_set(v___x_340_, 1, v_k_277_);
lean_ctor_set(v___x_340_, 0, v___x_335_);
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_k_277_);
lean_ctor_set(v_reuseFailAlloc_344_, 2, v_v_278_);
lean_ctor_set(v_reuseFailAlloc_344_, 3, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_344_, 4, v_r_280_);
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
}
else
{
lean_object* v_l_358_; 
v_l_358_ = lean_ctor_get(v_impl_273_, 3);
lean_inc(v_l_358_);
if (lean_obj_tag(v_l_358_) == 0)
{
lean_object* v_r_359_; lean_object* v_k_360_; lean_object* v_v_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_384_; 
v_r_359_ = lean_ctor_get(v_impl_273_, 4);
v_k_360_ = lean_ctor_get(v_impl_273_, 1);
v_v_361_ = lean_ctor_get(v_impl_273_, 2);
v_isSharedCheck_384_ = !lean_is_exclusive(v_impl_273_);
if (v_isSharedCheck_384_ == 0)
{
lean_object* v_unused_385_; lean_object* v_unused_386_; 
v_unused_385_ = lean_ctor_get(v_impl_273_, 3);
lean_dec(v_unused_385_);
v_unused_386_ = lean_ctor_get(v_impl_273_, 0);
lean_dec(v_unused_386_);
v___x_363_ = v_impl_273_;
v_isShared_364_ = v_isSharedCheck_384_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_r_359_);
lean_inc(v_v_361_);
lean_inc(v_k_360_);
lean_dec(v_impl_273_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_384_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v_k_365_; lean_object* v_v_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_380_; 
v_k_365_ = lean_ctor_get(v_l_358_, 1);
v_v_366_ = lean_ctor_get(v_l_358_, 2);
v_isSharedCheck_380_ = !lean_is_exclusive(v_l_358_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; lean_object* v_unused_382_; lean_object* v_unused_383_; 
v_unused_381_ = lean_ctor_get(v_l_358_, 4);
lean_dec(v_unused_381_);
v_unused_382_ = lean_ctor_get(v_l_358_, 3);
lean_dec(v_unused_382_);
v_unused_383_ = lean_ctor_get(v_l_358_, 0);
lean_dec(v_unused_383_);
v___x_368_ = v_l_358_;
v_isShared_369_ = v_isSharedCheck_380_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_v_366_);
lean_inc(v_k_365_);
lean_dec(v_l_358_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_380_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_370_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_359_, 2);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 4, v_r_359_);
lean_ctor_set(v___x_368_, 3, v_r_359_);
lean_ctor_set(v___x_368_, 2, v_v_265_);
lean_ctor_set(v___x_368_, 1, v_k_264_);
lean_ctor_set(v___x_368_, 0, v___x_274_);
v___x_372_ = v___x_368_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_k_264_);
lean_ctor_set(v_reuseFailAlloc_379_, 2, v_v_265_);
lean_ctor_set(v_reuseFailAlloc_379_, 3, v_r_359_);
lean_ctor_set(v_reuseFailAlloc_379_, 4, v_r_359_);
v___x_372_ = v_reuseFailAlloc_379_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_374_; 
lean_inc(v_r_359_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 3, v_r_359_);
lean_ctor_set(v___x_363_, 0, v___x_274_);
v___x_374_ = v___x_363_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_k_360_);
lean_ctor_set(v_reuseFailAlloc_378_, 2, v_v_361_);
lean_ctor_set(v_reuseFailAlloc_378_, 3, v_r_359_);
lean_ctor_set(v_reuseFailAlloc_378_, 4, v_r_359_);
v___x_374_ = v_reuseFailAlloc_378_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_376_; 
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 4, v___x_374_);
lean_ctor_set(v___x_269_, 3, v___x_372_);
lean_ctor_set(v___x_269_, 2, v_v_366_);
lean_ctor_set(v___x_269_, 1, v_k_365_);
lean_ctor_set(v___x_269_, 0, v___x_370_);
v___x_376_ = v___x_269_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_370_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_k_365_);
lean_ctor_set(v_reuseFailAlloc_377_, 2, v_v_366_);
lean_ctor_set(v_reuseFailAlloc_377_, 3, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_377_, 4, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
}
else
{
lean_object* v_r_387_; 
v_r_387_ = lean_ctor_get(v_impl_273_, 4);
lean_inc(v_r_387_);
if (lean_obj_tag(v_r_387_) == 0)
{
lean_object* v_k_388_; lean_object* v_v_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_400_; 
v_k_388_ = lean_ctor_get(v_impl_273_, 1);
v_v_389_ = lean_ctor_get(v_impl_273_, 2);
v_isSharedCheck_400_ = !lean_is_exclusive(v_impl_273_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; lean_object* v_unused_402_; lean_object* v_unused_403_; 
v_unused_401_ = lean_ctor_get(v_impl_273_, 4);
lean_dec(v_unused_401_);
v_unused_402_ = lean_ctor_get(v_impl_273_, 3);
lean_dec(v_unused_402_);
v_unused_403_ = lean_ctor_get(v_impl_273_, 0);
lean_dec(v_unused_403_);
v___x_391_ = v_impl_273_;
v_isShared_392_ = v_isSharedCheck_400_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_v_389_);
lean_inc(v_k_388_);
lean_dec(v_impl_273_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_400_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_393_ = lean_unsigned_to_nat(3u);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 4, v_l_358_);
lean_ctor_set(v___x_391_, 2, v_v_265_);
lean_ctor_set(v___x_391_, 1, v_k_264_);
lean_ctor_set(v___x_391_, 0, v___x_274_);
v___x_395_ = v___x_391_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_k_264_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v_v_265_);
lean_ctor_set(v_reuseFailAlloc_399_, 3, v_l_358_);
lean_ctor_set(v_reuseFailAlloc_399_, 4, v_l_358_);
v___x_395_ = v_reuseFailAlloc_399_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_397_; 
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 4, v_r_387_);
lean_ctor_set(v___x_269_, 3, v___x_395_);
lean_ctor_set(v___x_269_, 2, v_v_389_);
lean_ctor_set(v___x_269_, 1, v_k_388_);
lean_ctor_set(v___x_269_, 0, v___x_393_);
v___x_397_ = v___x_269_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_k_388_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_v_389_);
lean_ctor_set(v_reuseFailAlloc_398_, 3, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_398_, 4, v_r_387_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
else
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = lean_unsigned_to_nat(2u);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 4, v_impl_273_);
lean_ctor_set(v___x_269_, 3, v_r_387_);
lean_ctor_set(v___x_269_, 0, v___x_404_);
v___x_406_ = v___x_269_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_k_264_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_v_265_);
lean_ctor_set(v_reuseFailAlloc_407_, 3, v_r_387_);
lean_ctor_set(v_reuseFailAlloc_407_, 4, v_impl_273_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
else
{
lean_object* v___x_409_; 
lean_dec(v_v_265_);
lean_dec(v_k_264_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 2, v_v_261_);
lean_ctor_set(v___x_269_, 1, v_k_260_);
v___x_409_ = v___x_269_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_size_263_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_k_260_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_v_261_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v_l_266_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v_r_267_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
else
{
lean_object* v_impl_411_; lean_object* v___x_412_; 
lean_dec(v_size_263_);
v_impl_411_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_k_260_, v_v_261_, v_l_266_);
v___x_412_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_267_) == 0)
{
lean_object* v_size_413_; lean_object* v_size_414_; lean_object* v_k_415_; lean_object* v_v_416_; lean_object* v_l_417_; lean_object* v_r_418_; lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v_size_413_ = lean_ctor_get(v_r_267_, 0);
v_size_414_ = lean_ctor_get(v_impl_411_, 0);
lean_inc(v_size_414_);
v_k_415_ = lean_ctor_get(v_impl_411_, 1);
lean_inc(v_k_415_);
v_v_416_ = lean_ctor_get(v_impl_411_, 2);
lean_inc(v_v_416_);
v_l_417_ = lean_ctor_get(v_impl_411_, 3);
lean_inc(v_l_417_);
v_r_418_ = lean_ctor_get(v_impl_411_, 4);
lean_inc(v_r_418_);
v___x_419_ = lean_unsigned_to_nat(3u);
v___x_420_ = lean_nat_mul(v___x_419_, v_size_413_);
v___x_421_ = lean_nat_dec_lt(v___x_420_, v_size_414_);
lean_dec(v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
lean_dec(v_r_418_);
lean_dec(v_l_417_);
lean_dec(v_v_416_);
lean_dec(v_k_415_);
v___x_422_ = lean_nat_add(v___x_412_, v_size_414_);
lean_dec(v_size_414_);
v___x_423_ = lean_nat_add(v___x_422_, v_size_413_);
lean_dec(v___x_422_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 3, v_impl_411_);
lean_ctor_set(v___x_269_, 0, v___x_423_);
v___x_425_ = v___x_269_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_k_264_);
lean_ctor_set(v_reuseFailAlloc_426_, 2, v_v_265_);
lean_ctor_set(v_reuseFailAlloc_426_, 3, v_impl_411_);
lean_ctor_set(v_reuseFailAlloc_426_, 4, v_r_267_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
else
{
lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_492_; 
v_isSharedCheck_492_ = !lean_is_exclusive(v_impl_411_);
if (v_isSharedCheck_492_ == 0)
{
lean_object* v_unused_493_; lean_object* v_unused_494_; lean_object* v_unused_495_; lean_object* v_unused_496_; lean_object* v_unused_497_; 
v_unused_493_ = lean_ctor_get(v_impl_411_, 4);
lean_dec(v_unused_493_);
v_unused_494_ = lean_ctor_get(v_impl_411_, 3);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v_impl_411_, 2);
lean_dec(v_unused_495_);
v_unused_496_ = lean_ctor_get(v_impl_411_, 1);
lean_dec(v_unused_496_);
v_unused_497_ = lean_ctor_get(v_impl_411_, 0);
lean_dec(v_unused_497_);
v___x_428_ = v_impl_411_;
v_isShared_429_ = v_isSharedCheck_492_;
goto v_resetjp_427_;
}
else
{
lean_dec(v_impl_411_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_492_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v_size_430_; lean_object* v_size_431_; lean_object* v_k_432_; lean_object* v_v_433_; lean_object* v_l_434_; lean_object* v_r_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v_size_430_ = lean_ctor_get(v_l_417_, 0);
v_size_431_ = lean_ctor_get(v_r_418_, 0);
v_k_432_ = lean_ctor_get(v_r_418_, 1);
v_v_433_ = lean_ctor_get(v_r_418_, 2);
v_l_434_ = lean_ctor_get(v_r_418_, 3);
v_r_435_ = lean_ctor_get(v_r_418_, 4);
v___x_436_ = lean_unsigned_to_nat(2u);
v___x_437_ = lean_nat_mul(v___x_436_, v_size_430_);
v___x_438_ = lean_nat_dec_lt(v_size_431_, v___x_437_);
lean_dec(v___x_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_467_; 
lean_inc(v_r_435_);
lean_inc(v_l_434_);
lean_inc(v_v_433_);
lean_inc(v_k_432_);
v_isSharedCheck_467_ = !lean_is_exclusive(v_r_418_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; lean_object* v_unused_469_; lean_object* v_unused_470_; lean_object* v_unused_471_; lean_object* v_unused_472_; 
v_unused_468_ = lean_ctor_get(v_r_418_, 4);
lean_dec(v_unused_468_);
v_unused_469_ = lean_ctor_get(v_r_418_, 3);
lean_dec(v_unused_469_);
v_unused_470_ = lean_ctor_get(v_r_418_, 2);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_r_418_, 1);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v_r_418_, 0);
lean_dec(v_unused_472_);
v___x_440_ = v_r_418_;
v_isShared_441_ = v_isSharedCheck_467_;
goto v_resetjp_439_;
}
else
{
lean_dec(v_r_418_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_467_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___x_455_; lean_object* v___y_457_; 
v___x_442_ = lean_nat_add(v___x_412_, v_size_414_);
lean_dec(v_size_414_);
v___x_443_ = lean_nat_add(v___x_442_, v_size_413_);
lean_dec(v___x_442_);
v___x_455_ = lean_nat_add(v___x_412_, v_size_430_);
if (lean_obj_tag(v_l_434_) == 0)
{
lean_object* v_size_465_; 
v_size_465_ = lean_ctor_get(v_l_434_, 0);
lean_inc(v_size_465_);
v___y_457_ = v_size_465_;
goto v___jp_456_;
}
else
{
lean_object* v___x_466_; 
v___x_466_ = lean_unsigned_to_nat(0u);
v___y_457_ = v___x_466_;
goto v___jp_456_;
}
v___jp_444_:
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = lean_nat_add(v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec(v___y_446_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 4, v_r_267_);
lean_ctor_set(v___x_440_, 3, v_r_435_);
lean_ctor_set(v___x_440_, 2, v_v_265_);
lean_ctor_set(v___x_440_, 1, v_k_264_);
lean_ctor_set(v___x_440_, 0, v___x_448_);
v___x_450_ = v___x_440_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_k_264_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_v_265_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v_r_435_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v_r_267_);
v___x_450_ = v_reuseFailAlloc_454_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_452_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 4, v___x_450_);
lean_ctor_set(v___x_428_, 3, v___y_445_);
lean_ctor_set(v___x_428_, 2, v_v_433_);
lean_ctor_set(v___x_428_, 1, v_k_432_);
lean_ctor_set(v___x_428_, 0, v___x_443_);
v___x_452_ = v___x_428_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_k_432_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v_v_433_);
lean_ctor_set(v_reuseFailAlloc_453_, 3, v___y_445_);
lean_ctor_set(v_reuseFailAlloc_453_, 4, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
v___jp_456_:
{
lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_458_ = lean_nat_add(v___x_455_, v___y_457_);
lean_dec(v___y_457_);
lean_dec(v___x_455_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 4, v_l_434_);
lean_ctor_set(v___x_269_, 3, v_l_417_);
lean_ctor_set(v___x_269_, 2, v_v_416_);
lean_ctor_set(v___x_269_, 1, v_k_415_);
lean_ctor_set(v___x_269_, 0, v___x_458_);
v___x_460_ = v___x_269_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_k_415_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v_v_416_);
lean_ctor_set(v_reuseFailAlloc_464_, 3, v_l_417_);
lean_ctor_set(v_reuseFailAlloc_464_, 4, v_l_434_);
v___x_460_ = v_reuseFailAlloc_464_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; 
v___x_461_ = lean_nat_add(v___x_412_, v_size_413_);
if (lean_obj_tag(v_r_435_) == 0)
{
lean_object* v_size_462_; 
v_size_462_ = lean_ctor_get(v_r_435_, 0);
lean_inc(v_size_462_);
v___y_445_ = v___x_460_;
v___y_446_ = v___x_461_;
v___y_447_ = v_size_462_;
goto v___jp_444_;
}
else
{
lean_object* v___x_463_; 
v___x_463_ = lean_unsigned_to_nat(0u);
v___y_445_ = v___x_460_;
v___y_446_ = v___x_461_;
v___y_447_ = v___x_463_;
goto v___jp_444_;
}
}
}
}
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_478_; 
lean_del_object(v___x_269_);
v___x_473_ = lean_nat_add(v___x_412_, v_size_414_);
lean_dec(v_size_414_);
v___x_474_ = lean_nat_add(v___x_473_, v_size_413_);
lean_dec(v___x_473_);
v___x_475_ = lean_nat_add(v___x_412_, v_size_413_);
v___x_476_ = lean_nat_add(v___x_475_, v_size_431_);
lean_dec(v___x_475_);
lean_inc_ref(v_r_267_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 4, v_r_267_);
lean_ctor_set(v___x_428_, 3, v_r_418_);
lean_ctor_set(v___x_428_, 2, v_v_265_);
lean_ctor_set(v___x_428_, 1, v_k_264_);
lean_ctor_set(v___x_428_, 0, v___x_476_);
v___x_478_ = v___x_428_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_k_264_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_v_265_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v_r_418_);
lean_ctor_set(v_reuseFailAlloc_491_, 4, v_r_267_);
v___x_478_ = v_reuseFailAlloc_491_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
v_isSharedCheck_485_ = !lean_is_exclusive(v_r_267_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; lean_object* v_unused_487_; lean_object* v_unused_488_; lean_object* v_unused_489_; lean_object* v_unused_490_; 
v_unused_486_ = lean_ctor_get(v_r_267_, 4);
lean_dec(v_unused_486_);
v_unused_487_ = lean_ctor_get(v_r_267_, 3);
lean_dec(v_unused_487_);
v_unused_488_ = lean_ctor_get(v_r_267_, 2);
lean_dec(v_unused_488_);
v_unused_489_ = lean_ctor_get(v_r_267_, 1);
lean_dec(v_unused_489_);
v_unused_490_ = lean_ctor_get(v_r_267_, 0);
lean_dec(v_unused_490_);
v___x_480_ = v_r_267_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_dec(v_r_267_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 4, v___x_478_);
lean_ctor_set(v___x_480_, 3, v_l_417_);
lean_ctor_set(v___x_480_, 2, v_v_416_);
lean_ctor_set(v___x_480_, 1, v_k_415_);
lean_ctor_set(v___x_480_, 0, v___x_474_);
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_k_415_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v_v_416_);
lean_ctor_set(v_reuseFailAlloc_484_, 3, v_l_417_);
lean_ctor_set(v_reuseFailAlloc_484_, 4, v___x_478_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_498_; 
v_l_498_ = lean_ctor_get(v_impl_411_, 3);
lean_inc(v_l_498_);
if (lean_obj_tag(v_l_498_) == 0)
{
lean_object* v_r_499_; lean_object* v_k_500_; lean_object* v_v_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_512_; 
v_r_499_ = lean_ctor_get(v_impl_411_, 4);
v_k_500_ = lean_ctor_get(v_impl_411_, 1);
v_v_501_ = lean_ctor_get(v_impl_411_, 2);
v_isSharedCheck_512_ = !lean_is_exclusive(v_impl_411_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; lean_object* v_unused_514_; 
v_unused_513_ = lean_ctor_get(v_impl_411_, 3);
lean_dec(v_unused_513_);
v_unused_514_ = lean_ctor_get(v_impl_411_, 0);
lean_dec(v_unused_514_);
v___x_503_ = v_impl_411_;
v_isShared_504_ = v_isSharedCheck_512_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_r_499_);
lean_inc(v_v_501_);
lean_inc(v_k_500_);
lean_dec(v_impl_411_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_512_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_505_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_499_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 3, v_r_499_);
lean_ctor_set(v___x_503_, 2, v_v_265_);
lean_ctor_set(v___x_503_, 1, v_k_264_);
lean_ctor_set(v___x_503_, 0, v___x_412_);
v___x_507_ = v___x_503_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_k_264_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_v_265_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v_r_499_);
lean_ctor_set(v_reuseFailAlloc_511_, 4, v_r_499_);
v___x_507_ = v_reuseFailAlloc_511_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_509_; 
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 4, v___x_507_);
lean_ctor_set(v___x_269_, 3, v_l_498_);
lean_ctor_set(v___x_269_, 2, v_v_501_);
lean_ctor_set(v___x_269_, 1, v_k_500_);
lean_ctor_set(v___x_269_, 0, v___x_505_);
v___x_509_ = v___x_269_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_k_500_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v_v_501_);
lean_ctor_set(v_reuseFailAlloc_510_, 3, v_l_498_);
lean_ctor_set(v_reuseFailAlloc_510_, 4, v___x_507_);
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
else
{
lean_object* v_r_515_; 
v_r_515_ = lean_ctor_get(v_impl_411_, 4);
lean_inc(v_r_515_);
if (lean_obj_tag(v_r_515_) == 0)
{
lean_object* v_k_516_; lean_object* v_v_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_540_; 
v_k_516_ = lean_ctor_get(v_impl_411_, 1);
v_v_517_ = lean_ctor_get(v_impl_411_, 2);
v_isSharedCheck_540_ = !lean_is_exclusive(v_impl_411_);
if (v_isSharedCheck_540_ == 0)
{
lean_object* v_unused_541_; lean_object* v_unused_542_; lean_object* v_unused_543_; 
v_unused_541_ = lean_ctor_get(v_impl_411_, 4);
lean_dec(v_unused_541_);
v_unused_542_ = lean_ctor_get(v_impl_411_, 3);
lean_dec(v_unused_542_);
v_unused_543_ = lean_ctor_get(v_impl_411_, 0);
lean_dec(v_unused_543_);
v___x_519_ = v_impl_411_;
v_isShared_520_ = v_isSharedCheck_540_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_v_517_);
lean_inc(v_k_516_);
lean_dec(v_impl_411_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_540_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v_k_521_; lean_object* v_v_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_536_; 
v_k_521_ = lean_ctor_get(v_r_515_, 1);
v_v_522_ = lean_ctor_get(v_r_515_, 2);
v_isSharedCheck_536_ = !lean_is_exclusive(v_r_515_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; lean_object* v_unused_538_; lean_object* v_unused_539_; 
v_unused_537_ = lean_ctor_get(v_r_515_, 4);
lean_dec(v_unused_537_);
v_unused_538_ = lean_ctor_get(v_r_515_, 3);
lean_dec(v_unused_538_);
v_unused_539_ = lean_ctor_get(v_r_515_, 0);
lean_dec(v_unused_539_);
v___x_524_ = v_r_515_;
v_isShared_525_ = v_isSharedCheck_536_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_v_522_);
lean_inc(v_k_521_);
lean_dec(v_r_515_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_536_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = lean_unsigned_to_nat(3u);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 4, v_l_498_);
lean_ctor_set(v___x_524_, 3, v_l_498_);
lean_ctor_set(v___x_524_, 2, v_v_517_);
lean_ctor_set(v___x_524_, 1, v_k_516_);
lean_ctor_set(v___x_524_, 0, v___x_412_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_k_516_);
lean_ctor_set(v_reuseFailAlloc_535_, 2, v_v_517_);
lean_ctor_set(v_reuseFailAlloc_535_, 3, v_l_498_);
lean_ctor_set(v_reuseFailAlloc_535_, 4, v_l_498_);
v___x_528_ = v_reuseFailAlloc_535_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_530_; 
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 4, v_l_498_);
lean_ctor_set(v___x_519_, 2, v_v_265_);
lean_ctor_set(v___x_519_, 1, v_k_264_);
lean_ctor_set(v___x_519_, 0, v___x_412_);
v___x_530_ = v___x_519_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_k_264_);
lean_ctor_set(v_reuseFailAlloc_534_, 2, v_v_265_);
lean_ctor_set(v_reuseFailAlloc_534_, 3, v_l_498_);
lean_ctor_set(v_reuseFailAlloc_534_, 4, v_l_498_);
v___x_530_ = v_reuseFailAlloc_534_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_532_; 
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 4, v___x_530_);
lean_ctor_set(v___x_269_, 3, v___x_528_);
lean_ctor_set(v___x_269_, 2, v_v_522_);
lean_ctor_set(v___x_269_, 1, v_k_521_);
lean_ctor_set(v___x_269_, 0, v___x_526_);
v___x_532_ = v___x_269_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_k_521_);
lean_ctor_set(v_reuseFailAlloc_533_, 2, v_v_522_);
lean_ctor_set(v_reuseFailAlloc_533_, 3, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_533_, 4, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = lean_unsigned_to_nat(2u);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 4, v_r_515_);
lean_ctor_set(v___x_269_, 3, v_impl_411_);
lean_ctor_set(v___x_269_, 0, v___x_544_);
v___x_546_ = v___x_269_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_k_264_);
lean_ctor_set(v_reuseFailAlloc_547_, 2, v_v_265_);
lean_ctor_set(v_reuseFailAlloc_547_, 3, v_impl_411_);
lean_ctor_set(v_reuseFailAlloc_547_, 4, v_r_515_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v_k_260_);
lean_ctor_set(v___x_550_, 2, v_v_261_);
lean_ctor_set(v___x_550_, 3, v_t_262_);
lean_ctor_set(v___x_550_, 4, v_t_262_);
return v___x_550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(lean_object* v_b_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v___x_558_; lean_object* v_fst_559_; lean_object* v_snd_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_593_; 
v___x_558_ = lean_st_ref_get(v___y_552_);
v_fst_559_ = lean_ctor_get(v_b_551_, 0);
v_snd_560_ = lean_ctor_get(v_b_551_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v_b_551_);
if (v_isSharedCheck_593_ == 0)
{
v___x_562_ = v_b_551_;
v_isShared_563_ = v_isSharedCheck_593_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_snd_560_);
lean_inc(v_fst_559_);
lean_dec(v_b_551_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_593_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; 
lean_inc(v_snd_560_);
v___x_564_ = l_Lean_Meta_Grind_Goal_getENode(v___x_558_, v_snd_560_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_584_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_584_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_584_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_584_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v_self_569_; lean_object* v_target_x3f_570_; lean_object* v_idx_571_; lean_object* v___x_572_; 
v_self_569_ = lean_ctor_get(v_a_565_, 0);
lean_inc_ref(v_self_569_);
v_target_x3f_570_ = lean_ctor_get(v_a_565_, 4);
lean_inc(v_target_x3f_570_);
v_idx_571_ = lean_ctor_get(v_a_565_, 7);
lean_inc(v_idx_571_);
lean_dec(v_a_565_);
v___x_572_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_idx_571_, v_self_569_, v_fst_559_);
if (lean_obj_tag(v_target_x3f_570_) == 1)
{
lean_object* v_val_573_; lean_object* v___x_575_; 
lean_del_object(v___x_567_);
lean_dec(v_snd_560_);
v_val_573_ = lean_ctor_get(v_target_x3f_570_, 0);
lean_inc(v_val_573_);
lean_dec_ref(v_target_x3f_570_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v_val_573_);
lean_ctor_set(v___x_562_, 0, v___x_572_);
v___x_575_ = v___x_562_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_val_573_);
v___x_575_ = v_reuseFailAlloc_577_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
v_b_551_ = v___x_575_;
goto _start;
}
}
else
{
lean_object* v___x_579_; 
lean_dec(v_target_x3f_570_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_572_);
v___x_579_ = v___x_562_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_snd_560_);
v___x_579_ = v_reuseFailAlloc_583_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_581_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_579_);
v___x_581_ = v___x_567_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_del_object(v___x_562_);
lean_dec(v_snd_560_);
lean_dec(v_fst_559_);
v_a_585_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_564_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_564_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg___boxed(lean_object* v_b_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(v_b_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(lean_object* v_t_602_, lean_object* v_k_603_){
_start:
{
if (lean_obj_tag(v_t_602_) == 0)
{
lean_object* v_k_604_; lean_object* v_v_605_; lean_object* v_l_606_; lean_object* v_r_607_; uint8_t v___x_608_; 
v_k_604_ = lean_ctor_get(v_t_602_, 1);
v_v_605_ = lean_ctor_get(v_t_602_, 2);
v_l_606_ = lean_ctor_get(v_t_602_, 3);
v_r_607_ = lean_ctor_get(v_t_602_, 4);
v___x_608_ = lean_nat_dec_lt(v_k_603_, v_k_604_);
if (v___x_608_ == 0)
{
uint8_t v___x_609_; 
v___x_609_ = lean_nat_dec_eq(v_k_603_, v_k_604_);
if (v___x_609_ == 0)
{
v_t_602_ = v_r_607_;
goto _start;
}
else
{
lean_object* v___x_611_; 
lean_inc(v_v_605_);
v___x_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_611_, 0, v_v_605_);
return v___x_611_;
}
}
else
{
v_t_602_ = v_l_606_;
goto _start;
}
}
else
{
lean_object* v___x_613_; 
v___x_613_ = lean_box(0);
return v___x_613_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg___boxed(lean_object* v_t_614_, lean_object* v_k_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(v_t_614_, v_k_615_);
lean_dec(v_k_615_);
lean_dec(v_t_614_);
return v_res_616_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__3(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_620_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_621_ = lean_unsigned_to_nat(35u);
v___x_622_ = lean_unsigned_to_nat(87u);
v___x_623_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__1));
v___x_624_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_625_ = l_mkPanicMessageWithDecl(v___x_624_, v___x_623_, v___x_622_, v___x_621_, v___x_620_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4(lean_object* v___x_626_, lean_object* v_b_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v___x_639_; lean_object* v_snd_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_687_; 
v___x_639_ = lean_st_ref_get(v___y_628_);
v_snd_640_ = lean_ctor_get(v_b_627_, 1);
v_isSharedCheck_687_ = !lean_is_exclusive(v_b_627_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; 
v_unused_688_ = lean_ctor_get(v_b_627_, 0);
lean_dec(v_unused_688_);
v___x_642_ = v_b_627_;
v_isShared_643_ = v_isSharedCheck_687_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_snd_640_);
lean_dec(v_b_627_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_687_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; 
lean_inc(v_snd_640_);
v___x_644_ = l_Lean_Meta_Grind_Goal_getENode(v___x_639_, v_snd_640_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_678_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_678_ == 0)
{
v___x_647_ = v___x_644_;
v_isShared_648_ = v_isSharedCheck_678_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_678_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v_target_x3f_649_; lean_object* v_idx_650_; lean_object* v___x_651_; 
v_target_x3f_649_ = lean_ctor_get(v_a_645_, 4);
lean_inc(v_target_x3f_649_);
v_idx_650_ = lean_ctor_get(v_a_645_, 7);
lean_inc(v_idx_650_);
lean_dec(v_a_645_);
v___x_651_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(v___x_626_, v_idx_650_);
lean_dec(v_idx_650_);
if (lean_obj_tag(v___x_651_) == 1)
{
lean_object* v___x_653_; 
lean_dec(v_target_x3f_649_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_651_);
v___x_653_ = v___x_642_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_snd_640_);
v___x_653_ = v_reuseFailAlloc_657_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_655_; 
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_653_);
v___x_655_ = v___x_647_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
else
{
lean_object* v___x_658_; 
lean_dec(v___x_651_);
lean_del_object(v___x_647_);
v___x_658_ = lean_box(0);
if (lean_obj_tag(v_target_x3f_649_) == 1)
{
lean_object* v_val_659_; lean_object* v___x_661_; 
lean_dec(v_snd_640_);
v_val_659_ = lean_ctor_get(v_target_x3f_649_, 0);
lean_inc(v_val_659_);
lean_dec_ref(v_target_x3f_649_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 1, v_val_659_);
lean_ctor_set(v___x_642_, 0, v___x_658_);
v___x_661_ = v___x_642_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_val_659_);
v___x_661_ = v_reuseFailAlloc_663_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
v_b_627_ = v___x_661_;
goto _start;
}
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; 
lean_dec(v_target_x3f_649_);
v___x_664_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__3, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__3_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__3);
v___x_665_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3(v___x_664_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v___x_667_; 
lean_dec_ref(v___x_665_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_658_);
v___x_667_ = v___x_642_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_snd_640_);
v___x_667_ = v_reuseFailAlloc_669_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
v_b_627_ = v___x_667_;
goto _start;
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_del_object(v___x_642_);
lean_dec(v_snd_640_);
v_a_670_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_665_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_665_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_del_object(v___x_642_);
lean_dec(v_snd_640_);
v_a_679_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_644_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_644_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
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
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___boxed(lean_object* v___x_689_, lean_object* v_b_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4(v___x_689_, v_b_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec(v___y_691_);
lean_dec(v___x_689_);
return v_res_702_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_703_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_704_ = lean_unsigned_to_nat(2u);
v___x_705_ = lean_unsigned_to_nat(89u);
v___x_706_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__1));
v___x_707_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
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
v___x_724_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(v___x_723_, v_a_711_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v_fst_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_755_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_725_);
lean_dec_ref(v___x_724_);
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
v___x_733_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4(v_fst_726_, v___x_732_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
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
lean_dec_ref(v_fst_738_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1(lean_object* v_b_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(v_b_785_, v___y_786_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___boxed(lean_object* v_b_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1(v_b_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec(v___y_799_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2(lean_object* v_00_u03b4_811_, lean_object* v_t_812_, lean_object* v_k_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(v_t_812_, v_k_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___boxed(lean_object* v_00_u03b4_815_, lean_object* v_t_816_, lean_object* v_k_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2(v_00_u03b4_815_, v_t_816_, v_k_817_);
lean_dec(v_k_817_);
lean_dec(v_t_816_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(lean_object* v_info_819_, lean_object* v_lhs_820_, lean_object* v_rhs_821_, lean_object* v_i_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
uint8_t v___x_834_; 
v___x_834_ = l_Lean_Expr_isApp(v_lhs_820_);
if (v___x_834_ == 0)
{
uint8_t v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec(v_i_822_);
lean_dec_ref(v_rhs_821_);
lean_dec_ref(v_lhs_820_);
v___x_835_ = 1;
v___x_836_ = lean_box(v___x_835_);
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
return v___x_837_;
}
else
{
lean_object* v_a_u2081_838_; lean_object* v_a_u2082_839_; lean_object* v___x_840_; lean_object* v_i_841_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; uint8_t v___x_856_; 
v_a_u2081_838_ = l_Lean_Expr_appArg_x21(v_lhs_820_);
v_a_u2082_839_ = l_Lean_Expr_appArg_x21(v_rhs_821_);
v___x_840_ = lean_unsigned_to_nat(1u);
v_i_841_ = lean_nat_sub(v_i_822_, v___x_840_);
lean_dec(v_i_822_);
v___x_856_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_u2081_838_, v_a_u2082_839_);
lean_dec_ref(v_a_u2082_839_);
lean_dec_ref(v_a_u2081_838_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_857_ = lean_array_get_size(v_info_819_);
v___x_858_ = lean_nat_dec_lt(v_i_841_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; 
lean_dec(v_i_841_);
lean_dec_ref(v_rhs_821_);
lean_dec_ref(v_lhs_820_);
v___x_859_ = lean_box(v___x_856_);
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
return v___x_860_;
}
else
{
lean_object* v___x_861_; uint8_t v_hasFwdDeps_862_; 
v___x_861_ = lean_array_fget_borrowed(v_info_819_, v_i_841_);
v_hasFwdDeps_862_ = lean_ctor_get_uint8(v___x_861_, sizeof(void*)*1 + 1);
if (v_hasFwdDeps_862_ == 0)
{
v___y_843_ = v_a_823_;
v___y_844_ = v_a_824_;
v___y_845_ = v_a_825_;
v___y_846_ = v_a_826_;
v___y_847_ = v_a_827_;
v___y_848_ = v_a_828_;
v___y_849_ = v_a_829_;
v___y_850_ = v_a_830_;
v___y_851_ = v_a_831_;
v___y_852_ = v_a_832_;
goto v___jp_842_;
}
else
{
lean_object* v___x_863_; lean_object* v___x_864_; 
lean_dec(v_i_841_);
lean_dec_ref(v_rhs_821_);
lean_dec_ref(v_lhs_820_);
v___x_863_ = lean_box(v___x_856_);
v___x_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
return v___x_864_;
}
}
}
else
{
v___y_843_ = v_a_823_;
v___y_844_ = v_a_824_;
v___y_845_ = v_a_825_;
v___y_846_ = v_a_826_;
v___y_847_ = v_a_827_;
v___y_848_ = v_a_828_;
v___y_849_ = v_a_829_;
v___y_850_ = v_a_830_;
v___y_851_ = v_a_831_;
v___y_852_ = v_a_832_;
goto v___jp_842_;
}
v___jp_842_:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = l_Lean_Expr_appFn_x21(v_lhs_820_);
lean_dec_ref(v_lhs_820_);
v___x_854_ = l_Lean_Expr_appFn_x21(v_rhs_821_);
lean_dec_ref(v_rhs_821_);
v_lhs_820_ = v___x_853_;
v_rhs_821_ = v___x_854_;
v_i_822_ = v_i_841_;
v_a_823_ = v___y_843_;
v_a_824_ = v___y_844_;
v_a_825_ = v___y_845_;
v_a_826_ = v___y_846_;
v_a_827_ = v___y_847_;
v_a_828_ = v___y_848_;
v_a_829_ = v___y_849_;
v_a_830_ = v___y_850_;
v_a_831_ = v___y_851_;
v_a_832_ = v___y_852_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop___boxed(lean_object* v_info_865_, lean_object* v_lhs_866_, lean_object* v_rhs_867_, lean_object* v_i_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(v_info_865_, v_lhs_866_, v_rhs_867_, v_i_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
lean_dec(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_info_865_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(lean_object* v_lhs_881_, lean_object* v_rhs_882_, lean_object* v_f_883_, lean_object* v_g_884_, lean_object* v_numArgs_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
uint8_t v___x_897_; 
v___x_897_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_f_883_, v_g_884_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec(v_numArgs_885_);
lean_dec_ref(v_f_883_);
lean_dec_ref(v_rhs_882_);
lean_dec_ref(v_lhs_881_);
v___x_898_ = lean_box(v___x_897_);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = lean_box(0);
v___x_901_ = l_Lean_Meta_getFunInfo(v_f_883_, v___x_900_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v_paramInfo_903_; lean_object* v___x_904_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
lean_dec_ref(v___x_901_);
v_paramInfo_903_ = lean_ctor_get(v_a_902_, 0);
lean_inc_ref(v_paramInfo_903_);
lean_dec(v_a_902_);
v___x_904_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(v_paramInfo_903_, v_lhs_881_, v_rhs_882_, v_numArgs_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
lean_dec_ref(v_paramInfo_903_);
return v___x_904_;
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec(v_numArgs_885_);
lean_dec_ref(v_rhs_882_);
lean_dec_ref(v_lhs_881_);
v_a_905_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_901_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_901_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget___boxed(lean_object* v_lhs_913_, lean_object* v_rhs_914_, lean_object* v_f_915_, lean_object* v_g_916_, lean_object* v_numArgs_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(v_lhs_913_, v_rhs_914_, v_f_915_, v_g_916_, v_numArgs_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_g_916_);
return v_res_929_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0(void){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(lean_object* v_msg_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v___x_943_; lean_object* v___x_125372__overap_944_; lean_object* v___x_945_; 
v___x_943_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0);
v___x_125372__overap_944_ = lean_panic_fn_borrowed(v___x_943_, v_msg_931_);
lean_inc(v___y_941_);
lean_inc_ref(v___y_940_);
lean_inc(v___y_939_);
lean_inc_ref(v___y_938_);
lean_inc(v___y_937_);
lean_inc_ref(v___y_936_);
lean_inc(v___y_935_);
lean_inc_ref(v___y_934_);
lean_inc(v___y_933_);
lean_inc(v___y_932_);
v___x_945_ = lean_apply_11(v___x_125372__overap_944_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, lean_box(0));
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___boxed(lean_object* v_msg_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v_msg_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec(v___y_947_);
return v_res_958_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = l_Lean_maxRecDepthErrorMessage;
v___x_965_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3);
v___x_967_ = l_Lean_MessageData_ofFormat(v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_968_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4);
v___x_969_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__2));
v___x_970_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
lean_ctor_set(v___x_970_, 1, v___x_968_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(lean_object* v_ref_971_){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5);
v___x_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_974_, 0, v_ref_971_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___boxed(lean_object* v_ref_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_976_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0(lean_object* v_k_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v_b_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v___x_992_; 
lean_inc(v___y_990_);
lean_inc_ref(v___y_989_);
lean_inc(v___y_988_);
lean_inc_ref(v___y_987_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
lean_inc(v___y_981_);
lean_inc(v___y_980_);
v___x_992_ = lean_apply_12(v_k_979_, v_b_986_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, lean_box(0));
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0___boxed(lean_object* v_k_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v_b_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0(v_k_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v_b_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec(v___y_994_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(lean_object* v_name_1007_, uint8_t v_bi_1008_, lean_object* v_type_1009_, lean_object* v_k_1010_, uint8_t v_kind_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___f_1023_; lean_object* v___x_1024_; 
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
lean_inc(v___y_1015_);
lean_inc_ref(v___y_1014_);
lean_inc(v___y_1013_);
lean_inc(v___y_1012_);
v___f_1023_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_1023_, 0, v_k_1010_);
lean_closure_set(v___f_1023_, 1, v___y_1012_);
lean_closure_set(v___f_1023_, 2, v___y_1013_);
lean_closure_set(v___f_1023_, 3, v___y_1014_);
lean_closure_set(v___f_1023_, 4, v___y_1015_);
lean_closure_set(v___f_1023_, 5, v___y_1016_);
lean_closure_set(v___f_1023_, 6, v___y_1017_);
v___x_1024_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1007_, v_bi_1008_, v_type_1009_, v___f_1023_, v_kind_1011_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1024_) == 0)
{
return v___x_1024_;
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___boxed(lean_object* v_name_1033_, lean_object* v_bi_1034_, lean_object* v_type_1035_, lean_object* v_k_1036_, lean_object* v_kind_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
uint8_t v_bi_boxed_1049_; uint8_t v_kind_boxed_1050_; lean_object* v_res_1051_; 
v_bi_boxed_1049_ = lean_unbox(v_bi_1034_);
v_kind_boxed_1050_ = lean_unbox(v_kind_1037_);
v_res_1051_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_1033_, v_bi_boxed_1049_, v_type_1035_, v_k_1036_, v_kind_boxed_1050_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec(v___y_1038_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(lean_object* v_name_1052_, lean_object* v_type_1053_, lean_object* v_k_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
uint8_t v___x_1066_; uint8_t v___x_1067_; lean_object* v___x_1068_; 
v___x_1066_ = 0;
v___x_1067_ = 0;
v___x_1068_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_1052_, v___x_1066_, v_type_1053_, v_k_1054_, v___x_1067_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg___boxed(lean_object* v_name_1069_, lean_object* v_type_1070_, lean_object* v_k_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_name_1069_, v_type_1070_, v_k_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec(v___y_1072_);
return v_res_1083_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1084_; lean_object* v_dummy_1085_; 
v___x_1084_ = lean_box(0);
v_dummy_1085_ = l_Lean_Expr_sort___override(v___x_1084_);
return v_dummy_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0(lean_object* v_numArgs_1086_, lean_object* v_rhs_1087_, lean_object* v_lhs_1088_, uint8_t v___x_1089_, uint8_t v___x_1090_, lean_object* v_x_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_dummy_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v_dummy_1103_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0);
lean_inc(v_numArgs_1086_);
v___x_1104_ = lean_mk_array(v_numArgs_1086_, v_dummy_1103_);
v___x_1105_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_numArgs_1086_, v_rhs_1087_, v___x_1104_);
lean_inc_ref(v_x_1091_);
v___x_1106_ = l_Lean_mkAppN(v_x_1091_, v___x_1105_);
lean_dec_ref(v___x_1105_);
v___x_1107_ = l_Lean_Meta_mkHEq(v_lhs_1088_, v___x_1106_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; lean_object* v___x_1113_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
lean_dec_ref(v___x_1107_);
v___x_1109_ = lean_unsigned_to_nat(1u);
v___x_1110_ = lean_mk_empty_array_with_capacity(v___x_1109_);
v___x_1111_ = lean_array_push(v___x_1110_, v_x_1091_);
v___x_1112_ = 1;
v___x_1113_ = l_Lean_Meta_mkLambdaFVars(v___x_1111_, v_a_1108_, v___x_1089_, v___x_1090_, v___x_1089_, v___x_1090_, v___x_1112_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec_ref(v___x_1111_);
return v___x_1113_;
}
else
{
lean_dec_ref(v_x_1091_);
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___boxed(lean_object** _args){
lean_object* v_numArgs_1114_ = _args[0];
lean_object* v_rhs_1115_ = _args[1];
lean_object* v_lhs_1116_ = _args[2];
lean_object* v___x_1117_ = _args[3];
lean_object* v___x_1118_ = _args[4];
lean_object* v_x_1119_ = _args[5];
lean_object* v___y_1120_ = _args[6];
lean_object* v___y_1121_ = _args[7];
lean_object* v___y_1122_ = _args[8];
lean_object* v___y_1123_ = _args[9];
lean_object* v___y_1124_ = _args[10];
lean_object* v___y_1125_ = _args[11];
lean_object* v___y_1126_ = _args[12];
lean_object* v___y_1127_ = _args[13];
lean_object* v___y_1128_ = _args[14];
lean_object* v___y_1129_ = _args[15];
lean_object* v___y_1130_ = _args[16];
_start:
{
uint8_t v___x_133262__boxed_1131_; uint8_t v___x_133263__boxed_1132_; lean_object* v_res_1133_; 
v___x_133262__boxed_1131_ = lean_unbox(v___x_1117_);
v___x_133263__boxed_1132_ = lean_unbox(v___x_1118_);
v_res_1133_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0(v_numArgs_1114_, v_rhs_1115_, v_lhs_1116_, v___x_133262__boxed_1131_, v___x_133263__boxed_1132_, v_x_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec(v___y_1120_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_spec__13(lean_object* v_msg_1134_){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = l_Lean_instInhabitedExpr;
v___x_1136_ = lean_panic_fn_borrowed(v___x_1135_, v_msg_1134_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(lean_object* v_msgData_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v___x_1143_; lean_object* v_env_1144_; lean_object* v___x_1145_; lean_object* v_mctx_1146_; lean_object* v_lctx_1147_; lean_object* v_options_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1143_ = lean_st_ref_get(v___y_1141_);
v_env_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc_ref(v_env_1144_);
lean_dec(v___x_1143_);
v___x_1145_ = lean_st_ref_get(v___y_1139_);
v_mctx_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc_ref(v_mctx_1146_);
lean_dec(v___x_1145_);
v_lctx_1147_ = lean_ctor_get(v___y_1138_, 2);
v_options_1148_ = lean_ctor_get(v___y_1140_, 2);
lean_inc_ref(v_options_1148_);
lean_inc_ref(v_lctx_1147_);
v___x_1149_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1149_, 0, v_env_1144_);
lean_ctor_set(v___x_1149_, 1, v_mctx_1146_);
lean_ctor_set(v___x_1149_, 2, v_lctx_1147_);
lean_ctor_set(v___x_1149_, 3, v_options_1148_);
v___x_1150_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
lean_ctor_set(v___x_1150_, 1, v_msgData_1137_);
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16___boxed(lean_object* v_msgData_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(v_msgData_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(lean_object* v_msg_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_ref_1165_; lean_object* v___x_1166_; lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1175_; 
v_ref_1165_ = lean_ctor_get(v___y_1162_, 5);
v___x_1166_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(v_msg_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1175_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1175_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1173_; 
lean_inc(v_ref_1165_);
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v_ref_1165_);
lean_ctor_set(v___x_1171_, 1, v_a_1167_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set_tag(v___x_1169_, 1);
lean_ctor_set(v___x_1169_, 0, v___x_1171_);
v___x_1173_ = v___x_1169_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg___boxed(lean_object* v_msg_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v_msg_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
return v_res_1182_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__0));
v___x_1185_ = l_Lean_stringToMessageData(v___x_1184_);
return v___x_1185_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__2));
v___x_1188_ = l_Lean_stringToMessageData(v___x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(lean_object* v_lhs_1189_, lean_object* v_rhs_1190_, lean_object* v_00_u03b1_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1203_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1);
v___x_1204_ = l_Lean_indentExpr(v_lhs_1189_);
v___x_1205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3);
v___x_1207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1205_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = l_Lean_indentExpr(v_rhs_1190_);
v___x_1209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1207_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v___x_1209_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___boxed(lean_object* v_lhs_1211_, lean_object* v_rhs_1212_, lean_object* v_00_u03b1_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1211_, v_rhs_1212_, v_00_u03b1_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec(v___y_1214_);
return v_res_1225_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1228_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__1));
v___x_1229_ = lean_unsigned_to_nat(4u);
v___x_1230_ = lean_unsigned_to_nat(198u);
v___x_1231_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__0));
v___x_1232_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1233_ = l_mkPanicMessageWithDecl(v___x_1232_, v___x_1231_, v___x_1230_, v___x_1229_, v___x_1228_);
return v___x_1233_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1236_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__1));
v___x_1237_ = lean_unsigned_to_nat(4u);
v___x_1238_ = lean_unsigned_to_nat(318u);
v___x_1239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0));
v___x_1240_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1241_ = l_mkPanicMessageWithDecl(v___x_1240_, v___x_1239_, v___x_1238_, v___x_1237_, v___x_1236_);
return v___x_1241_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1243_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_1244_ = lean_unsigned_to_nat(36u);
v___x_1245_ = lean_unsigned_to_nat(153u);
v___x_1246_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0));
v___x_1247_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1248_ = l_mkPanicMessageWithDecl(v___x_1247_, v___x_1246_, v___x_1245_, v___x_1244_, v___x_1243_);
return v___x_1248_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1249_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_1250_ = lean_unsigned_to_nat(34u);
v___x_1251_ = lean_unsigned_to_nat(154u);
v___x_1252_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0));
v___x_1253_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1254_ = l_mkPanicMessageWithDecl(v___x_1253_, v___x_1252_, v___x_1251_, v___x_1250_, v___x_1249_);
return v___x_1254_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1256_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__3));
v___x_1257_ = lean_unsigned_to_nat(4u);
v___x_1258_ = lean_unsigned_to_nat(155u);
v___x_1259_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0));
v___x_1260_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1261_ = l_mkPanicMessageWithDecl(v___x_1260_, v___x_1259_, v___x_1258_, v___x_1257_, v___x_1256_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof(lean_object* v_lhs_1274_, lean_object* v_rhs_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1314_; uint8_t v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; uint8_t v___y_1323_; lean_object* v_fileName_1357_; lean_object* v_fileMap_1358_; lean_object* v_options_1359_; lean_object* v_currRecDepth_1360_; lean_object* v_maxRecDepth_1361_; lean_object* v_ref_1362_; lean_object* v_currNamespace_1363_; lean_object* v_openDecls_1364_; lean_object* v_initHeartbeats_1365_; lean_object* v_maxHeartbeats_1366_; lean_object* v_quotContext_1367_; lean_object* v_currMacroScope_1368_; uint8_t v_diag_1369_; lean_object* v_cancelTk_x3f_1370_; uint8_t v_suppressElabErrors_1371_; lean_object* v_inheritedTraceOptions_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v_fileName_1357_ = lean_ctor_get(v_a_1284_, 0);
v_fileMap_1358_ = lean_ctor_get(v_a_1284_, 1);
v_options_1359_ = lean_ctor_get(v_a_1284_, 2);
v_currRecDepth_1360_ = lean_ctor_get(v_a_1284_, 3);
v_maxRecDepth_1361_ = lean_ctor_get(v_a_1284_, 4);
v_ref_1362_ = lean_ctor_get(v_a_1284_, 5);
v_currNamespace_1363_ = lean_ctor_get(v_a_1284_, 6);
v_openDecls_1364_ = lean_ctor_get(v_a_1284_, 7);
v_initHeartbeats_1365_ = lean_ctor_get(v_a_1284_, 8);
v_maxHeartbeats_1366_ = lean_ctor_get(v_a_1284_, 9);
v_quotContext_1367_ = lean_ctor_get(v_a_1284_, 10);
v_currMacroScope_1368_ = lean_ctor_get(v_a_1284_, 11);
v_diag_1369_ = lean_ctor_get_uint8(v_a_1284_, sizeof(void*)*14);
v_cancelTk_x3f_1370_ = lean_ctor_get(v_a_1284_, 12);
v_suppressElabErrors_1371_ = lean_ctor_get_uint8(v_a_1284_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1372_ = lean_ctor_get(v_a_1284_, 13);
v___x_1373_ = l_Lean_Expr_cleanupAnnotations(v_lhs_1274_);
v___x_1374_ = l_Lean_Expr_isApp(v___x_1373_);
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = lean_nat_dec_eq(v_maxRecDepth_1361_, v___x_1404_);
if (v___x_1405_ == 0)
{
uint8_t v___x_1406_; 
v___x_1406_ = lean_nat_dec_eq(v_currRecDepth_1360_, v_maxRecDepth_1361_);
if (v___x_1406_ == 0)
{
goto v___jp_1375_;
}
else
{
lean_object* v___x_1407_; 
lean_dec_ref(v___x_1373_);
lean_dec_ref(v_rhs_1275_);
lean_inc(v_ref_1362_);
v___x_1407_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1362_);
return v___x_1407_;
}
}
else
{
goto v___jp_1375_;
}
v___jp_1287_:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1);
v___x_1299_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1298_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec_ref(v___y_1296_);
return v___x_1299_;
}
v___jp_1300_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2);
v___x_1312_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1311_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
lean_dec_ref(v___y_1309_);
return v___x_1312_;
}
v___jp_1313_:
{
if (v___y_1323_ == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_dec_ref(v___y_1322_);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec_ref(v___y_1314_);
v___x_1324_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4);
v___x_1325_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1324_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v___y_1321_, v_a_1285_);
lean_dec_ref(v___y_1321_);
return v___x_1325_;
}
else
{
lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1326_ = l_Lean_Expr_constLevels_x21(v___y_1319_);
lean_dec_ref(v___y_1319_);
v___x_1327_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___y_1316_, v___y_1322_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
lean_inc_ref(v___y_1317_);
lean_inc_ref(v___y_1320_);
v___x_1328_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1320_, v___y_1317_, v___y_1315_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v___y_1321_, v_a_1285_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1330_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref(v___x_1328_);
lean_inc_ref(v___y_1314_);
lean_inc_ref(v___y_1318_);
v___x_1330_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1318_, v___y_1314_, v___y_1315_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v___y_1321_, v_a_1285_);
lean_dec_ref(v___y_1321_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1341_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1341_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1341_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1335_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6));
v___x_1336_ = l_Lean_mkConst(v___x_1335_, v___x_1326_);
v___x_1337_ = l_Lean_mkApp8(v___x_1336_, v___y_1316_, v___y_1322_, v___y_1320_, v___y_1318_, v___y_1314_, v___y_1317_, v_a_1329_, v_a_1331_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1337_);
v___x_1339_ = v___x_1333_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
else
{
lean_dec(v_a_1329_);
lean_dec(v___x_1326_);
lean_dec_ref(v___y_1322_);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec_ref(v___y_1314_);
return v___x_1330_;
}
}
else
{
lean_dec(v___x_1326_);
lean_dec_ref(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec_ref(v___y_1314_);
return v___x_1328_;
}
}
else
{
uint8_t v___x_1342_; lean_object* v___x_1343_; 
lean_dec_ref(v___y_1322_);
v___x_1342_ = 0;
lean_inc_ref(v___y_1317_);
lean_inc_ref(v___y_1320_);
v___x_1343_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1320_, v___y_1317_, v___x_1342_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v___y_1321_, v_a_1285_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1345_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref(v___x_1343_);
lean_inc_ref(v___y_1314_);
lean_inc_ref(v___y_1318_);
v___x_1345_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1318_, v___y_1314_, v___x_1342_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v___y_1321_, v_a_1285_);
lean_dec_ref(v___y_1321_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1356_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1356_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1356_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1350_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8));
v___x_1351_ = l_Lean_mkConst(v___x_1350_, v___x_1326_);
v___x_1352_ = l_Lean_mkApp7(v___x_1351_, v___y_1316_, v___y_1320_, v___y_1318_, v___y_1314_, v___y_1317_, v_a_1344_, v_a_1346_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1352_);
v___x_1354_ = v___x_1348_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
else
{
lean_dec(v_a_1344_);
lean_dec(v___x_1326_);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec_ref(v___y_1314_);
return v___x_1345_;
}
}
else
{
lean_dec(v___x_1326_);
lean_dec_ref(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec_ref(v___y_1314_);
return v___x_1343_;
}
}
}
}
v___jp_1375_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1376_ = lean_unsigned_to_nat(1u);
v___x_1377_ = lean_nat_add(v_currRecDepth_1360_, v___x_1376_);
lean_inc_ref(v_inheritedTraceOptions_1372_);
lean_inc(v_cancelTk_x3f_1370_);
lean_inc(v_currMacroScope_1368_);
lean_inc(v_quotContext_1367_);
lean_inc(v_maxHeartbeats_1366_);
lean_inc(v_initHeartbeats_1365_);
lean_inc(v_openDecls_1364_);
lean_inc(v_currNamespace_1363_);
lean_inc(v_ref_1362_);
lean_inc(v_maxRecDepth_1361_);
lean_inc_ref(v_options_1359_);
lean_inc_ref(v_fileMap_1358_);
lean_inc_ref(v_fileName_1357_);
v___x_1378_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1378_, 0, v_fileName_1357_);
lean_ctor_set(v___x_1378_, 1, v_fileMap_1358_);
lean_ctor_set(v___x_1378_, 2, v_options_1359_);
lean_ctor_set(v___x_1378_, 3, v___x_1377_);
lean_ctor_set(v___x_1378_, 4, v_maxRecDepth_1361_);
lean_ctor_set(v___x_1378_, 5, v_ref_1362_);
lean_ctor_set(v___x_1378_, 6, v_currNamespace_1363_);
lean_ctor_set(v___x_1378_, 7, v_openDecls_1364_);
lean_ctor_set(v___x_1378_, 8, v_initHeartbeats_1365_);
lean_ctor_set(v___x_1378_, 9, v_maxHeartbeats_1366_);
lean_ctor_set(v___x_1378_, 10, v_quotContext_1367_);
lean_ctor_set(v___x_1378_, 11, v_currMacroScope_1368_);
lean_ctor_set(v___x_1378_, 12, v_cancelTk_x3f_1370_);
lean_ctor_set(v___x_1378_, 13, v_inheritedTraceOptions_1372_);
lean_ctor_set_uint8(v___x_1378_, sizeof(void*)*14, v_diag_1369_);
lean_ctor_set_uint8(v___x_1378_, sizeof(void*)*14 + 1, v_suppressElabErrors_1371_);
if (v___x_1374_ == 0)
{
lean_dec_ref(v___x_1373_);
lean_dec_ref(v_rhs_1275_);
v___y_1288_ = v_a_1276_;
v___y_1289_ = v_a_1277_;
v___y_1290_ = v_a_1278_;
v___y_1291_ = v_a_1279_;
v___y_1292_ = v_a_1280_;
v___y_1293_ = v_a_1281_;
v___y_1294_ = v_a_1282_;
v___y_1295_ = v_a_1283_;
v___y_1296_ = v___x_1378_;
v___y_1297_ = v_a_1285_;
goto v___jp_1287_;
}
else
{
lean_object* v_arg_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v_arg_1379_ = lean_ctor_get(v___x_1373_, 1);
lean_inc_ref(v_arg_1379_);
v___x_1380_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1373_);
v___x_1381_ = l_Lean_Expr_isApp(v___x_1380_);
if (v___x_1381_ == 0)
{
lean_dec_ref(v___x_1380_);
lean_dec_ref(v_arg_1379_);
lean_dec_ref(v_rhs_1275_);
v___y_1288_ = v_a_1276_;
v___y_1289_ = v_a_1277_;
v___y_1290_ = v_a_1278_;
v___y_1291_ = v_a_1279_;
v___y_1292_ = v_a_1280_;
v___y_1293_ = v_a_1281_;
v___y_1294_ = v_a_1282_;
v___y_1295_ = v_a_1283_;
v___y_1296_ = v___x_1378_;
v___y_1297_ = v_a_1285_;
goto v___jp_1287_;
}
else
{
lean_object* v_arg_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; 
v_arg_1382_ = lean_ctor_get(v___x_1380_, 1);
lean_inc_ref(v_arg_1382_);
v___x_1383_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1380_);
v___x_1384_ = l_Lean_Expr_isApp(v___x_1383_);
if (v___x_1384_ == 0)
{
lean_dec_ref(v___x_1383_);
lean_dec_ref(v_arg_1382_);
lean_dec_ref(v_arg_1379_);
lean_dec_ref(v_rhs_1275_);
v___y_1288_ = v_a_1276_;
v___y_1289_ = v_a_1277_;
v___y_1290_ = v_a_1278_;
v___y_1291_ = v_a_1279_;
v___y_1292_ = v_a_1280_;
v___y_1293_ = v_a_1281_;
v___y_1294_ = v_a_1282_;
v___y_1295_ = v_a_1283_;
v___y_1296_ = v___x_1378_;
v___y_1297_ = v_a_1285_;
goto v___jp_1287_;
}
else
{
lean_object* v_arg_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v_arg_1385_ = lean_ctor_get(v___x_1383_, 1);
lean_inc_ref(v_arg_1385_);
v___x_1386_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1383_);
v___x_1387_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_1388_ = l_Lean_Expr_isConstOf(v___x_1386_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_dec_ref(v___x_1386_);
lean_dec_ref(v_arg_1385_);
lean_dec_ref(v_arg_1382_);
lean_dec_ref(v_arg_1379_);
lean_dec_ref(v_rhs_1275_);
v___y_1288_ = v_a_1276_;
v___y_1289_ = v_a_1277_;
v___y_1290_ = v_a_1278_;
v___y_1291_ = v_a_1279_;
v___y_1292_ = v_a_1280_;
v___y_1293_ = v_a_1281_;
v___y_1294_ = v_a_1282_;
v___y_1295_ = v_a_1283_;
v___y_1296_ = v___x_1378_;
v___y_1297_ = v_a_1285_;
goto v___jp_1287_;
}
else
{
lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1389_ = l_Lean_Expr_cleanupAnnotations(v_rhs_1275_);
v___x_1390_ = l_Lean_Expr_isApp(v___x_1389_);
if (v___x_1390_ == 0)
{
lean_dec_ref(v___x_1389_);
lean_dec_ref(v___x_1386_);
lean_dec_ref(v_arg_1385_);
lean_dec_ref(v_arg_1382_);
lean_dec_ref(v_arg_1379_);
v___y_1301_ = v_a_1276_;
v___y_1302_ = v_a_1277_;
v___y_1303_ = v_a_1278_;
v___y_1304_ = v_a_1279_;
v___y_1305_ = v_a_1280_;
v___y_1306_ = v_a_1281_;
v___y_1307_ = v_a_1282_;
v___y_1308_ = v_a_1283_;
v___y_1309_ = v___x_1378_;
v___y_1310_ = v_a_1285_;
goto v___jp_1300_;
}
else
{
lean_object* v_arg_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
v_arg_1391_ = lean_ctor_get(v___x_1389_, 1);
lean_inc_ref(v_arg_1391_);
v___x_1392_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1389_);
v___x_1393_ = l_Lean_Expr_isApp(v___x_1392_);
if (v___x_1393_ == 0)
{
lean_dec_ref(v___x_1392_);
lean_dec_ref(v_arg_1391_);
lean_dec_ref(v___x_1386_);
lean_dec_ref(v_arg_1385_);
lean_dec_ref(v_arg_1382_);
lean_dec_ref(v_arg_1379_);
v___y_1301_ = v_a_1276_;
v___y_1302_ = v_a_1277_;
v___y_1303_ = v_a_1278_;
v___y_1304_ = v_a_1279_;
v___y_1305_ = v_a_1280_;
v___y_1306_ = v_a_1281_;
v___y_1307_ = v_a_1282_;
v___y_1308_ = v_a_1283_;
v___y_1309_ = v___x_1378_;
v___y_1310_ = v_a_1285_;
goto v___jp_1300_;
}
else
{
lean_object* v_arg_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v_arg_1394_ = lean_ctor_get(v___x_1392_, 1);
lean_inc_ref(v_arg_1394_);
v___x_1395_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1392_);
v___x_1396_ = l_Lean_Expr_isApp(v___x_1395_);
if (v___x_1396_ == 0)
{
lean_dec_ref(v___x_1395_);
lean_dec_ref(v_arg_1394_);
lean_dec_ref(v_arg_1391_);
lean_dec_ref(v___x_1386_);
lean_dec_ref(v_arg_1385_);
lean_dec_ref(v_arg_1382_);
lean_dec_ref(v_arg_1379_);
v___y_1301_ = v_a_1276_;
v___y_1302_ = v_a_1277_;
v___y_1303_ = v_a_1278_;
v___y_1304_ = v_a_1279_;
v___y_1305_ = v_a_1280_;
v___y_1306_ = v_a_1281_;
v___y_1307_ = v_a_1282_;
v___y_1308_ = v_a_1283_;
v___y_1309_ = v___x_1378_;
v___y_1310_ = v_a_1285_;
goto v___jp_1300_;
}
else
{
lean_object* v_arg_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v_arg_1397_ = lean_ctor_get(v___x_1395_, 1);
lean_inc_ref(v_arg_1397_);
v___x_1398_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1395_);
v___x_1399_ = l_Lean_Expr_isConstOf(v___x_1398_, v___x_1387_);
lean_dec_ref(v___x_1398_);
if (v___x_1399_ == 0)
{
lean_dec_ref(v_arg_1397_);
lean_dec_ref(v_arg_1394_);
lean_dec_ref(v_arg_1391_);
lean_dec_ref(v___x_1386_);
lean_dec_ref(v_arg_1385_);
lean_dec_ref(v_arg_1382_);
lean_dec_ref(v_arg_1379_);
v___y_1301_ = v_a_1276_;
v___y_1302_ = v_a_1277_;
v___y_1303_ = v_a_1278_;
v___y_1304_ = v_a_1279_;
v___y_1305_ = v_a_1280_;
v___y_1306_ = v_a_1281_;
v___y_1307_ = v_a_1282_;
v___y_1308_ = v_a_1283_;
v___y_1309_ = v___x_1378_;
v___y_1310_ = v_a_1285_;
goto v___jp_1300_;
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v___x_1400_ = lean_st_ref_get(v_a_1276_);
v___x_1401_ = lean_st_ref_get(v_a_1276_);
v___x_1402_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1400_, v_arg_1382_, v_arg_1391_);
if (v___x_1402_ == 0)
{
lean_dec(v___x_1401_);
v___y_1314_ = v_arg_1394_;
v___y_1315_ = v___x_1399_;
v___y_1316_ = v_arg_1385_;
v___y_1317_ = v_arg_1391_;
v___y_1318_ = v_arg_1379_;
v___y_1319_ = v___x_1386_;
v___y_1320_ = v_arg_1382_;
v___y_1321_ = v___x_1378_;
v___y_1322_ = v_arg_1397_;
v___y_1323_ = v___x_1402_;
goto v___jp_1313_;
}
else
{
uint8_t v___x_1403_; 
v___x_1403_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1401_, v_arg_1379_, v_arg_1394_);
v___y_1314_ = v_arg_1394_;
v___y_1315_ = v___x_1399_;
v___y_1316_ = v_arg_1385_;
v___y_1317_ = v_arg_1391_;
v___y_1318_ = v_arg_1379_;
v___y_1319_ = v___x_1386_;
v___y_1320_ = v_arg_1382_;
v___y_1321_ = v___x_1378_;
v___y_1322_ = v_arg_1397_;
v___y_1323_ = v___x_1403_;
goto v___jp_1313_;
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
uint8_t v___x_1411_; uint64_t v___x_1412_; 
v___x_1411_ = 1;
v___x_1412_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1411_);
return v___x_1412_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1414_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_1415_ = lean_unsigned_to_nat(38u);
v___x_1416_ = lean_unsigned_to_nat(250u);
v___x_1417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3));
v___x_1418_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1419_ = l_mkPanicMessageWithDecl(v___x_1418_, v___x_1417_, v___x_1416_, v___x_1415_, v___x_1414_);
return v___x_1419_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6(void){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5));
v___x_1422_ = lean_unsigned_to_nat(6u);
v___x_1423_ = lean_unsigned_to_nat(260u);
v___x_1424_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3));
v___x_1425_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1426_ = l_mkPanicMessageWithDecl(v___x_1425_, v___x_1424_, v___x_1423_, v___x_1422_, v___x_1421_);
return v___x_1426_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2(void){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1429_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__1));
v___x_1430_ = lean_unsigned_to_nat(4u);
v___x_1431_ = lean_unsigned_to_nat(219u);
v___x_1432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__0));
v___x_1433_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1434_ = l_mkPanicMessageWithDecl(v___x_1433_, v___x_1432_, v___x_1431_, v___x_1430_, v___x_1429_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(lean_object* v_lhs_1435_, lean_object* v_rhs_1436_, uint8_t v_heq_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v_numArgs_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v_numArgs_1449_ = l_Lean_Expr_getAppNumArgs(v_lhs_1435_);
v___x_1450_ = l_Lean_Expr_getAppNumArgs(v_rhs_1436_);
v___x_1451_ = lean_nat_dec_eq(v___x_1450_, v_numArgs_1449_);
lean_dec(v___x_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_dec(v_numArgs_1449_);
lean_dec_ref(v_rhs_1436_);
lean_dec_ref(v_lhs_1435_);
v___x_1452_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2);
v___x_1453_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1452_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
return v___x_1453_;
}
else
{
lean_object* v_f_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_f_1454_ = l_Lean_Expr_getAppFn(v_lhs_1435_);
v___x_1455_ = lean_box(0);
lean_inc_ref(v_f_1454_);
v___x_1456_ = l_Lean_Meta_getFunInfo(v_f_1454_, v___x_1455_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref(v___x_1456_);
v___x_1458_ = l_Lean_Meta_FunInfo_getArity(v_a_1457_);
lean_dec(v_a_1457_);
v___x_1459_ = lean_nat_dec_lt(v___x_1458_, v_numArgs_1449_);
lean_dec(v___x_1458_);
if (v___x_1459_ == 0)
{
lean_object* v_g_1460_; lean_object* v___x_1461_; 
v_g_1460_ = l_Lean_Expr_getAppFn(v_rhs_1436_);
v___x_1461_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_1454_, v_g_1460_, v_numArgs_1449_, v_lhs_1435_, v_rhs_1436_, v_heq_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
return v___x_1461_;
}
else
{
lean_object* v___x_1462_; 
lean_dec_ref(v_f_1454_);
lean_dec(v_numArgs_1449_);
lean_inc_ref(v_lhs_1435_);
v___x_1462_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(v_lhs_1435_, v_rhs_1436_);
if (lean_obj_tag(v___x_1462_) == 1)
{
lean_object* v_val_1463_; lean_object* v_fst_1464_; lean_object* v_snd_1465_; lean_object* v___y_1467_; lean_object* v___x_1480_; 
v_val_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_val_1463_);
lean_dec_ref(v___x_1462_);
v_fst_1464_ = lean_ctor_get(v_val_1463_, 0);
lean_inc(v_fst_1464_);
v_snd_1465_ = lean_ctor_get(v_val_1463_, 1);
lean_inc_n(v_snd_1465_, 2);
lean_dec(v_val_1463_);
v___x_1480_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(v_fst_1464_, v_snd_1465_, v_a_1441_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
if (lean_obj_tag(v___x_1480_) == 0)
{
v___y_1467_ = v___x_1480_;
goto v___jp_1466_;
}
else
{
lean_object* v_a_1481_; uint8_t v___y_1483_; uint8_t v___x_1485_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1481_);
v___x_1485_ = l_Lean_Exception_isInterrupt(v_a_1481_);
if (v___x_1485_ == 0)
{
uint8_t v___x_1486_; 
v___x_1486_ = l_Lean_Exception_isRuntime(v_a_1481_);
v___y_1483_ = v___x_1486_;
goto v___jp_1482_;
}
else
{
lean_dec(v_a_1481_);
v___y_1483_ = v___x_1485_;
goto v___jp_1482_;
}
v___jp_1482_:
{
if (v___y_1483_ == 0)
{
lean_object* v___x_1484_; 
lean_dec_ref(v___x_1480_);
lean_inc_ref(v_rhs_1436_);
lean_inc_ref(v_lhs_1435_);
v___x_1484_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1435_, v_rhs_1436_, lean_box(0), v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
v___y_1467_ = v___x_1484_;
goto v___jp_1466_;
}
else
{
v___y_1467_ = v___x_1480_;
goto v___jp_1466_;
}
}
}
v___jp_1466_:
{
if (lean_obj_tag(v___y_1467_) == 0)
{
lean_object* v_a_1468_; lean_object* v___x_1469_; 
v_a_1468_ = lean_ctor_get(v___y_1467_, 0);
lean_inc(v_a_1468_);
lean_dec_ref(v___y_1467_);
v___x_1469_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_1468_, v_lhs_1435_, v_rhs_1436_, v_snd_1465_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
lean_dec(v_snd_1465_);
lean_dec_ref(v_rhs_1436_);
lean_dec_ref(v_lhs_1435_);
lean_dec(v_a_1468_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1471_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref(v___x_1469_);
v___x_1471_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_1470_, v_heq_1437_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
return v___x_1471_;
}
else
{
return v___x_1469_;
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec(v_snd_1465_);
lean_dec_ref(v_rhs_1436_);
lean_dec_ref(v_lhs_1435_);
v_a_1472_ = lean_ctor_get(v___y_1467_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___y_1467_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___y_1467_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___y_1467_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
else
{
lean_object* v___x_1487_; 
lean_dec(v___x_1462_);
v___x_1487_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1435_, v_rhs_1436_, lean_box(0), v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
return v___x_1487_;
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec_ref(v_f_1454_);
lean_dec(v_numArgs_1449_);
lean_dec_ref(v_rhs_1436_);
lean_dec_ref(v_lhs_1435_);
v_a_1488_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1456_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1456_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(lean_object* v_lhs_1496_, lean_object* v_rhs_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
uint8_t v___x_1509_; 
v___x_1509_ = l_Lean_Expr_isApp(v_lhs_1496_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = lean_box(0);
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
return v___x_1511_;
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1512_ = l_Lean_Expr_appFn_x21(v_lhs_1496_);
v___x_1513_ = l_Lean_Expr_appFn_x21(v_rhs_1497_);
v___x_1514_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v___x_1512_, v___x_1513_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
lean_dec_ref(v___x_1513_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1610_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1610_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1610_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v_a_u2081_1519_; lean_object* v_a_u2082_1520_; 
v_a_u2081_1519_ = l_Lean_Expr_appArg_x21(v_lhs_1496_);
v_a_u2082_1520_ = l_Lean_Expr_appArg_x21(v_rhs_1497_);
if (lean_obj_tag(v_a_1515_) == 1)
{
lean_object* v_val_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1576_; 
lean_del_object(v___x_1517_);
lean_dec_ref(v___x_1512_);
v_val_1521_ = lean_ctor_get(v_a_1515_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_a_1515_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1523_ = v_a_1515_;
v_isShared_1524_ = v_isSharedCheck_1576_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_val_1521_);
lean_dec(v_a_1515_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1576_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
uint8_t v___x_1525_; 
v___x_1525_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_u2081_1519_, v_a_u2082_1520_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; 
v___x_1526_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_1519_, v_a_u2082_1520_, v___x_1525_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1528_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref(v___x_1526_);
v___x_1528_ = l_Lean_Meta_mkCongr(v_val_1521_, v_a_1527_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1539_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1531_ = v___x_1528_;
v_isShared_1532_ = v_isSharedCheck_1539_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1528_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1539_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v_a_1529_);
v___x_1534_ = v___x_1523_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1536_; 
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1534_);
v___x_1536_ = v___x_1531_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
lean_del_object(v___x_1523_);
v_a_1540_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1528_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1528_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_del_object(v___x_1523_);
lean_dec(v_val_1521_);
v_a_1548_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1526_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1526_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
else
{
lean_object* v___x_1556_; 
lean_dec_ref(v_a_u2082_1520_);
v___x_1556_ = l_Lean_Meta_mkCongrFun(v_val_1521_, v_a_u2081_1519_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
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
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v_a_1557_);
v___x_1562_ = v___x_1523_;
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
lean_del_object(v___x_1523_);
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
}
}
else
{
uint8_t v___x_1577_; 
lean_dec(v_a_1515_);
v___x_1577_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_u2081_1519_, v_a_u2082_1520_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; 
lean_del_object(v___x_1517_);
v___x_1578_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_1519_, v_a_u2082_1520_, v___x_1577_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1580_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref(v___x_1578_);
v___x_1580_ = l_Lean_Meta_mkCongrArg(v___x_1512_, v_a_1579_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1589_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1589_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1589_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1585_; lean_object* v___x_1587_; 
v___x_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1585_, 0, v_a_1581_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v___x_1585_);
v___x_1587_ = v___x_1583_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
v_a_1590_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1580_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1580_);
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
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec_ref(v___x_1512_);
v_a_1598_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1578_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1578_);
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
else
{
lean_object* v___x_1606_; lean_object* v___x_1608_; 
lean_dec_ref(v_a_u2082_1520_);
lean_dec_ref(v_a_u2081_1519_);
lean_dec_ref(v___x_1512_);
v___x_1606_ = lean_box(0);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v___x_1606_);
v___x_1608_ = v___x_1517_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1512_);
return v___x_1514_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3(void){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1614_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__2));
v___x_1615_ = lean_unsigned_to_nat(14u);
v___x_1616_ = lean_unsigned_to_nat(22u);
v___x_1617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__1));
v___x_1618_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__0));
v___x_1619_ = l_mkPanicMessageWithDecl(v___x_1618_, v___x_1617_, v___x_1616_, v___x_1615_, v___x_1614_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(lean_object* v_lhs_1620_, lean_object* v_rhs_1621_, uint8_t v_heq_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_1620_, v_rhs_1621_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1648_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1648_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1648_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___y_1640_; 
if (lean_obj_tag(v_a_1635_) == 0)
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3);
v___x_1646_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_spec__13(v___x_1645_);
v___y_1640_ = v___x_1646_;
goto v___jp_1639_;
}
else
{
lean_object* v_val_1647_; 
v_val_1647_ = lean_ctor_get(v_a_1635_, 0);
lean_inc(v_val_1647_);
lean_dec_ref(v_a_1635_);
v___y_1640_ = v_val_1647_;
goto v___jp_1639_;
}
v___jp_1639_:
{
if (v_heq_1622_ == 0)
{
lean_object* v___x_1642_; 
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___y_1640_);
v___x_1642_ = v___x_1637_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___y_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
else
{
lean_object* v___x_1644_; 
lean_del_object(v___x_1637_);
v___x_1644_ = l_Lean_Meta_mkHEqOfEq(v___y_1640_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_);
return v___x_1644_;
}
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
v_a_1649_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1634_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1634_);
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
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__1(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1658_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_1659_ = lean_unsigned_to_nat(36u);
v___x_1660_ = lean_unsigned_to_nat(143u);
v___x_1661_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1662_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1663_ = l_mkPanicMessageWithDecl(v___x_1662_, v___x_1661_, v___x_1660_, v___x_1659_, v___x_1658_);
return v___x_1663_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__2(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1664_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_1665_ = lean_unsigned_to_nat(34u);
v___x_1666_ = lean_unsigned_to_nat(144u);
v___x_1667_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1668_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1669_ = l_mkPanicMessageWithDecl(v___x_1668_, v___x_1667_, v___x_1666_, v___x_1665_, v___x_1664_);
return v___x_1669_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__4(void){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1671_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__3));
v___x_1672_ = lean_unsigned_to_nat(4u);
v___x_1673_ = lean_unsigned_to_nat(145u);
v___x_1674_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1675_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1676_ = l_mkPanicMessageWithDecl(v___x_1675_, v___x_1674_, v___x_1673_, v___x_1672_, v___x_1671_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrProof(lean_object* v_lhs_1687_, lean_object* v_rhs_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; uint8_t v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; uint8_t v___y_1736_; lean_object* v_fileName_1770_; lean_object* v_fileMap_1771_; lean_object* v_options_1772_; lean_object* v_currRecDepth_1773_; lean_object* v_maxRecDepth_1774_; lean_object* v_ref_1775_; lean_object* v_currNamespace_1776_; lean_object* v_openDecls_1777_; lean_object* v_initHeartbeats_1778_; lean_object* v_maxHeartbeats_1779_; lean_object* v_quotContext_1780_; lean_object* v_currMacroScope_1781_; uint8_t v_diag_1782_; lean_object* v_cancelTk_x3f_1783_; uint8_t v_suppressElabErrors_1784_; lean_object* v_inheritedTraceOptions_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v_fileName_1770_ = lean_ctor_get(v_a_1697_, 0);
v_fileMap_1771_ = lean_ctor_get(v_a_1697_, 1);
v_options_1772_ = lean_ctor_get(v_a_1697_, 2);
v_currRecDepth_1773_ = lean_ctor_get(v_a_1697_, 3);
v_maxRecDepth_1774_ = lean_ctor_get(v_a_1697_, 4);
v_ref_1775_ = lean_ctor_get(v_a_1697_, 5);
v_currNamespace_1776_ = lean_ctor_get(v_a_1697_, 6);
v_openDecls_1777_ = lean_ctor_get(v_a_1697_, 7);
v_initHeartbeats_1778_ = lean_ctor_get(v_a_1697_, 8);
v_maxHeartbeats_1779_ = lean_ctor_get(v_a_1697_, 9);
v_quotContext_1780_ = lean_ctor_get(v_a_1697_, 10);
v_currMacroScope_1781_ = lean_ctor_get(v_a_1697_, 11);
v_diag_1782_ = lean_ctor_get_uint8(v_a_1697_, sizeof(void*)*14);
v_cancelTk_x3f_1783_ = lean_ctor_get(v_a_1697_, 12);
v_suppressElabErrors_1784_ = lean_ctor_get_uint8(v_a_1697_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1785_ = lean_ctor_get(v_a_1697_, 13);
v___x_1786_ = l_Lean_Expr_cleanupAnnotations(v_lhs_1687_);
v___x_1787_ = l_Lean_Expr_isApp(v___x_1786_);
v___x_1817_ = lean_unsigned_to_nat(0u);
v___x_1818_ = lean_nat_dec_eq(v_maxRecDepth_1774_, v___x_1817_);
if (v___x_1818_ == 0)
{
uint8_t v___x_1819_; 
v___x_1819_ = lean_nat_dec_eq(v_currRecDepth_1773_, v_maxRecDepth_1774_);
if (v___x_1819_ == 0)
{
goto v___jp_1788_;
}
else
{
lean_object* v___x_1820_; 
lean_dec_ref(v___x_1786_);
lean_dec_ref(v_rhs_1688_);
lean_inc(v_ref_1775_);
v___x_1820_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1775_);
return v___x_1820_;
}
}
else
{
goto v___jp_1788_;
}
v___jp_1700_:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__1, &l_Lean_Meta_Grind_mkEqCongrProof___closed__1_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__1);
v___x_1712_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1711_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
lean_dec_ref(v___y_1709_);
return v___x_1712_;
}
v___jp_1713_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__2, &l_Lean_Meta_Grind_mkEqCongrProof___closed__2_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__2);
v___x_1725_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1724_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
lean_dec_ref(v___y_1722_);
return v___x_1725_;
}
v___jp_1726_:
{
if (v___y_1736_ == 0)
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_dec_ref(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec_ref(v___y_1727_);
v___x_1737_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__4, &l_Lean_Meta_Grind_mkEqCongrProof___closed__4_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__4);
v___x_1738_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1737_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v___y_1728_, v_a_1698_);
lean_dec_ref(v___y_1728_);
return v___x_1738_;
}
else
{
lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1739_ = l_Lean_Expr_constLevels_x21(v___y_1727_);
lean_dec_ref(v___y_1727_);
v___x_1740_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___y_1734_, v___y_1729_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; 
lean_inc_ref(v___y_1735_);
lean_inc_ref(v___y_1732_);
v___x_1741_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1732_, v___y_1735_, v___y_1731_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v___y_1728_, v_a_1698_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___x_1743_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref(v___x_1741_);
lean_inc_ref(v___y_1733_);
lean_inc_ref(v___y_1730_);
v___x_1743_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1730_, v___y_1733_, v___y_1731_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v___y_1728_, v_a_1698_);
lean_dec_ref(v___y_1728_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1754_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1746_ = v___x_1743_;
v_isShared_1747_ = v_isSharedCheck_1754_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1743_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1754_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1748_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__6));
v___x_1749_ = l_Lean_mkConst(v___x_1748_, v___x_1739_);
v___x_1750_ = l_Lean_mkApp8(v___x_1749_, v___y_1734_, v___y_1729_, v___y_1732_, v___y_1730_, v___y_1735_, v___y_1733_, v_a_1742_, v_a_1744_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v___x_1750_);
v___x_1752_ = v___x_1746_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
else
{
lean_dec(v_a_1742_);
lean_dec(v___x_1739_);
lean_dec_ref(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v___y_1729_);
return v___x_1743_;
}
}
else
{
lean_dec(v___x_1739_);
lean_dec_ref(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec_ref(v___y_1728_);
return v___x_1741_;
}
}
else
{
uint8_t v___x_1755_; lean_object* v___x_1756_; 
lean_dec_ref(v___y_1729_);
v___x_1755_ = 0;
lean_inc_ref(v___y_1735_);
lean_inc_ref(v___y_1732_);
v___x_1756_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1732_, v___y_1735_, v___x_1755_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v___y_1728_, v_a_1698_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1758_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref(v___x_1756_);
lean_inc_ref(v___y_1733_);
lean_inc_ref(v___y_1730_);
v___x_1758_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_1730_, v___y_1733_, v___x_1755_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v___y_1728_, v_a_1698_);
lean_dec_ref(v___y_1728_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1769_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1769_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1769_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1763_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__8));
v___x_1764_ = l_Lean_mkConst(v___x_1763_, v___x_1739_);
v___x_1765_ = l_Lean_mkApp7(v___x_1764_, v___y_1734_, v___y_1732_, v___y_1730_, v___y_1735_, v___y_1733_, v_a_1757_, v_a_1759_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1765_);
v___x_1767_ = v___x_1761_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
else
{
lean_dec(v_a_1757_);
lean_dec(v___x_1739_);
lean_dec_ref(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec_ref(v___y_1730_);
return v___x_1758_;
}
}
else
{
lean_dec(v___x_1739_);
lean_dec_ref(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v___y_1728_);
return v___x_1756_;
}
}
}
}
v___jp_1788_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = lean_unsigned_to_nat(1u);
v___x_1790_ = lean_nat_add(v_currRecDepth_1773_, v___x_1789_);
lean_inc_ref(v_inheritedTraceOptions_1785_);
lean_inc(v_cancelTk_x3f_1783_);
lean_inc(v_currMacroScope_1781_);
lean_inc(v_quotContext_1780_);
lean_inc(v_maxHeartbeats_1779_);
lean_inc(v_initHeartbeats_1778_);
lean_inc(v_openDecls_1777_);
lean_inc(v_currNamespace_1776_);
lean_inc(v_ref_1775_);
lean_inc(v_maxRecDepth_1774_);
lean_inc_ref(v_options_1772_);
lean_inc_ref(v_fileMap_1771_);
lean_inc_ref(v_fileName_1770_);
v___x_1791_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1791_, 0, v_fileName_1770_);
lean_ctor_set(v___x_1791_, 1, v_fileMap_1771_);
lean_ctor_set(v___x_1791_, 2, v_options_1772_);
lean_ctor_set(v___x_1791_, 3, v___x_1790_);
lean_ctor_set(v___x_1791_, 4, v_maxRecDepth_1774_);
lean_ctor_set(v___x_1791_, 5, v_ref_1775_);
lean_ctor_set(v___x_1791_, 6, v_currNamespace_1776_);
lean_ctor_set(v___x_1791_, 7, v_openDecls_1777_);
lean_ctor_set(v___x_1791_, 8, v_initHeartbeats_1778_);
lean_ctor_set(v___x_1791_, 9, v_maxHeartbeats_1779_);
lean_ctor_set(v___x_1791_, 10, v_quotContext_1780_);
lean_ctor_set(v___x_1791_, 11, v_currMacroScope_1781_);
lean_ctor_set(v___x_1791_, 12, v_cancelTk_x3f_1783_);
lean_ctor_set(v___x_1791_, 13, v_inheritedTraceOptions_1785_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*14, v_diag_1782_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*14 + 1, v_suppressElabErrors_1784_);
if (v___x_1787_ == 0)
{
lean_dec_ref(v___x_1786_);
lean_dec_ref(v_rhs_1688_);
v___y_1701_ = v_a_1689_;
v___y_1702_ = v_a_1690_;
v___y_1703_ = v_a_1691_;
v___y_1704_ = v_a_1692_;
v___y_1705_ = v_a_1693_;
v___y_1706_ = v_a_1694_;
v___y_1707_ = v_a_1695_;
v___y_1708_ = v_a_1696_;
v___y_1709_ = v___x_1791_;
v___y_1710_ = v_a_1698_;
goto v___jp_1700_;
}
else
{
lean_object* v_arg_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v_arg_1792_ = lean_ctor_get(v___x_1786_, 1);
lean_inc_ref(v_arg_1792_);
v___x_1793_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1786_);
v___x_1794_ = l_Lean_Expr_isApp(v___x_1793_);
if (v___x_1794_ == 0)
{
lean_dec_ref(v___x_1793_);
lean_dec_ref(v_arg_1792_);
lean_dec_ref(v_rhs_1688_);
v___y_1701_ = v_a_1689_;
v___y_1702_ = v_a_1690_;
v___y_1703_ = v_a_1691_;
v___y_1704_ = v_a_1692_;
v___y_1705_ = v_a_1693_;
v___y_1706_ = v_a_1694_;
v___y_1707_ = v_a_1695_;
v___y_1708_ = v_a_1696_;
v___y_1709_ = v___x_1791_;
v___y_1710_ = v_a_1698_;
goto v___jp_1700_;
}
else
{
lean_object* v_arg_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v_arg_1795_ = lean_ctor_get(v___x_1793_, 1);
lean_inc_ref(v_arg_1795_);
v___x_1796_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1793_);
v___x_1797_ = l_Lean_Expr_isApp(v___x_1796_);
if (v___x_1797_ == 0)
{
lean_dec_ref(v___x_1796_);
lean_dec_ref(v_arg_1795_);
lean_dec_ref(v_arg_1792_);
lean_dec_ref(v_rhs_1688_);
v___y_1701_ = v_a_1689_;
v___y_1702_ = v_a_1690_;
v___y_1703_ = v_a_1691_;
v___y_1704_ = v_a_1692_;
v___y_1705_ = v_a_1693_;
v___y_1706_ = v_a_1694_;
v___y_1707_ = v_a_1695_;
v___y_1708_ = v_a_1696_;
v___y_1709_ = v___x_1791_;
v___y_1710_ = v_a_1698_;
goto v___jp_1700_;
}
else
{
lean_object* v_arg_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; 
v_arg_1798_ = lean_ctor_get(v___x_1796_, 1);
lean_inc_ref(v_arg_1798_);
v___x_1799_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1796_);
v___x_1800_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_1801_ = l_Lean_Expr_isConstOf(v___x_1799_, v___x_1800_);
if (v___x_1801_ == 0)
{
lean_dec_ref(v___x_1799_);
lean_dec_ref(v_arg_1798_);
lean_dec_ref(v_arg_1795_);
lean_dec_ref(v_arg_1792_);
lean_dec_ref(v_rhs_1688_);
v___y_1701_ = v_a_1689_;
v___y_1702_ = v_a_1690_;
v___y_1703_ = v_a_1691_;
v___y_1704_ = v_a_1692_;
v___y_1705_ = v_a_1693_;
v___y_1706_ = v_a_1694_;
v___y_1707_ = v_a_1695_;
v___y_1708_ = v_a_1696_;
v___y_1709_ = v___x_1791_;
v___y_1710_ = v_a_1698_;
goto v___jp_1700_;
}
else
{
lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1802_ = l_Lean_Expr_cleanupAnnotations(v_rhs_1688_);
v___x_1803_ = l_Lean_Expr_isApp(v___x_1802_);
if (v___x_1803_ == 0)
{
lean_dec_ref(v___x_1802_);
lean_dec_ref(v___x_1799_);
lean_dec_ref(v_arg_1798_);
lean_dec_ref(v_arg_1795_);
lean_dec_ref(v_arg_1792_);
v___y_1714_ = v_a_1689_;
v___y_1715_ = v_a_1690_;
v___y_1716_ = v_a_1691_;
v___y_1717_ = v_a_1692_;
v___y_1718_ = v_a_1693_;
v___y_1719_ = v_a_1694_;
v___y_1720_ = v_a_1695_;
v___y_1721_ = v_a_1696_;
v___y_1722_ = v___x_1791_;
v___y_1723_ = v_a_1698_;
goto v___jp_1713_;
}
else
{
lean_object* v_arg_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v_arg_1804_ = lean_ctor_get(v___x_1802_, 1);
lean_inc_ref(v_arg_1804_);
v___x_1805_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1802_);
v___x_1806_ = l_Lean_Expr_isApp(v___x_1805_);
if (v___x_1806_ == 0)
{
lean_dec_ref(v___x_1805_);
lean_dec_ref(v_arg_1804_);
lean_dec_ref(v___x_1799_);
lean_dec_ref(v_arg_1798_);
lean_dec_ref(v_arg_1795_);
lean_dec_ref(v_arg_1792_);
v___y_1714_ = v_a_1689_;
v___y_1715_ = v_a_1690_;
v___y_1716_ = v_a_1691_;
v___y_1717_ = v_a_1692_;
v___y_1718_ = v_a_1693_;
v___y_1719_ = v_a_1694_;
v___y_1720_ = v_a_1695_;
v___y_1721_ = v_a_1696_;
v___y_1722_ = v___x_1791_;
v___y_1723_ = v_a_1698_;
goto v___jp_1713_;
}
else
{
lean_object* v_arg_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v_arg_1807_ = lean_ctor_get(v___x_1805_, 1);
lean_inc_ref(v_arg_1807_);
v___x_1808_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1805_);
v___x_1809_ = l_Lean_Expr_isApp(v___x_1808_);
if (v___x_1809_ == 0)
{
lean_dec_ref(v___x_1808_);
lean_dec_ref(v_arg_1807_);
lean_dec_ref(v_arg_1804_);
lean_dec_ref(v___x_1799_);
lean_dec_ref(v_arg_1798_);
lean_dec_ref(v_arg_1795_);
lean_dec_ref(v_arg_1792_);
v___y_1714_ = v_a_1689_;
v___y_1715_ = v_a_1690_;
v___y_1716_ = v_a_1691_;
v___y_1717_ = v_a_1692_;
v___y_1718_ = v_a_1693_;
v___y_1719_ = v_a_1694_;
v___y_1720_ = v_a_1695_;
v___y_1721_ = v_a_1696_;
v___y_1722_ = v___x_1791_;
v___y_1723_ = v_a_1698_;
goto v___jp_1713_;
}
else
{
lean_object* v_arg_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v_arg_1810_ = lean_ctor_get(v___x_1808_, 1);
lean_inc_ref(v_arg_1810_);
v___x_1811_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1808_);
v___x_1812_ = l_Lean_Expr_isConstOf(v___x_1811_, v___x_1800_);
lean_dec_ref(v___x_1811_);
if (v___x_1812_ == 0)
{
lean_dec_ref(v_arg_1810_);
lean_dec_ref(v_arg_1807_);
lean_dec_ref(v_arg_1804_);
lean_dec_ref(v___x_1799_);
lean_dec_ref(v_arg_1798_);
lean_dec_ref(v_arg_1795_);
lean_dec_ref(v_arg_1792_);
v___y_1714_ = v_a_1689_;
v___y_1715_ = v_a_1690_;
v___y_1716_ = v_a_1691_;
v___y_1717_ = v_a_1692_;
v___y_1718_ = v_a_1693_;
v___y_1719_ = v_a_1694_;
v___y_1720_ = v_a_1695_;
v___y_1721_ = v_a_1696_;
v___y_1722_ = v___x_1791_;
v___y_1723_ = v_a_1698_;
goto v___jp_1713_;
}
else
{
lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1813_ = lean_st_ref_get(v_a_1689_);
v___x_1814_ = lean_st_ref_get(v_a_1689_);
v___x_1815_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1813_, v_arg_1795_, v_arg_1807_);
if (v___x_1815_ == 0)
{
lean_dec(v___x_1814_);
v___y_1727_ = v___x_1799_;
v___y_1728_ = v___x_1791_;
v___y_1729_ = v_arg_1810_;
v___y_1730_ = v_arg_1792_;
v___y_1731_ = v___x_1812_;
v___y_1732_ = v_arg_1795_;
v___y_1733_ = v_arg_1804_;
v___y_1734_ = v_arg_1798_;
v___y_1735_ = v_arg_1807_;
v___y_1736_ = v___x_1815_;
goto v___jp_1726_;
}
else
{
uint8_t v___x_1816_; 
v___x_1816_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1814_, v_arg_1792_, v_arg_1804_);
v___y_1727_ = v___x_1799_;
v___y_1728_ = v___x_1791_;
v___y_1729_ = v_arg_1810_;
v___y_1730_ = v_arg_1792_;
v___y_1731_ = v___x_1812_;
v___y_1732_ = v_arg_1795_;
v___y_1733_ = v_arg_1804_;
v___y_1734_ = v_arg_1798_;
v___y_1735_ = v_arg_1807_;
v___y_1736_ = v___x_1816_;
goto v___jp_1726_;
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
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1831_ = lean_box(0);
v___x_1832_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3));
v___x_1833_ = l_Lean_mkConst(v___x_1832_, v___x_1831_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(lean_object* v_lhs_1834_, lean_object* v_rhs_1835_, uint8_t v_heq_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v___x_1848_; lean_object* v_p_1849_; lean_object* v___x_1850_; lean_object* v_q_1851_; uint8_t v___x_1852_; lean_object* v___x_1853_; 
v___x_1848_ = l_Lean_Expr_appFn_x21(v_lhs_1834_);
v_p_1849_ = l_Lean_Expr_appArg_x21(v___x_1848_);
lean_dec_ref(v___x_1848_);
v___x_1850_ = l_Lean_Expr_appFn_x21(v_rhs_1835_);
v_q_1851_ = l_Lean_Expr_appArg_x21(v___x_1850_);
lean_dec_ref(v___x_1850_);
v___x_1852_ = 0;
lean_inc_ref(v_q_1851_);
lean_inc_ref(v_p_1849_);
v___x_1853_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_p_1849_, v_q_1851_, v___x_1852_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v_hp_1855_; lean_object* v_hq_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
lean_dec_ref(v___x_1853_);
v_hp_1855_ = l_Lean_Expr_appArg_x21(v_lhs_1834_);
v_hq_1856_ = l_Lean_Expr_appArg_x21(v_rhs_1835_);
v___x_1857_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4);
v___x_1858_ = l_Lean_mkApp5(v___x_1857_, v_p_1849_, v_q_1851_, v_a_1854_, v_hp_1855_, v_hq_1856_);
v___x_1859_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v___x_1858_, v_heq_1836_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_);
return v___x_1859_;
}
else
{
lean_dec_ref(v_q_1851_);
lean_dec_ref(v_p_1849_);
return v___x_1853_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2(void){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1870_ = lean_box(0);
v___x_1871_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1));
v___x_1872_ = l_Lean_mkConst(v___x_1871_, v___x_1870_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(lean_object* v_lhs_1873_, lean_object* v_rhs_1874_, uint8_t v_heq_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v___x_1887_; lean_object* v_p_1888_; lean_object* v___x_1889_; lean_object* v_q_1890_; uint8_t v___x_1891_; lean_object* v___x_1892_; 
v___x_1887_ = l_Lean_Expr_appFn_x21(v_lhs_1873_);
v_p_1888_ = l_Lean_Expr_appArg_x21(v___x_1887_);
lean_dec_ref(v___x_1887_);
v___x_1889_ = l_Lean_Expr_appFn_x21(v_rhs_1874_);
v_q_1890_ = l_Lean_Expr_appArg_x21(v___x_1889_);
lean_dec_ref(v___x_1889_);
v___x_1891_ = 0;
lean_inc_ref(v_q_1890_);
lean_inc_ref(v_p_1888_);
v___x_1892_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_p_1888_, v_q_1890_, v___x_1891_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v_hp_1894_; lean_object* v_hq_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref(v___x_1892_);
v_hp_1894_ = l_Lean_Expr_appArg_x21(v_lhs_1873_);
v_hq_1895_ = l_Lean_Expr_appArg_x21(v_rhs_1874_);
v___x_1896_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2);
v___x_1897_ = l_Lean_mkApp5(v___x_1896_, v_p_1888_, v_q_1890_, v_a_1893_, v_hp_1894_, v_hq_1895_);
v___x_1898_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v___x_1897_, v_heq_1875_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
return v___x_1898_;
}
else
{
lean_dec_ref(v_q_1890_);
lean_dec_ref(v_p_1888_);
return v___x_1892_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(lean_object* v_lhs_1899_, lean_object* v_rhs_1900_, uint8_t v_heq_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_){
_start:
{
if (lean_obj_tag(v_lhs_1899_) == 7)
{
if (lean_obj_tag(v_rhs_1900_) == 7)
{
lean_object* v_binderType_1913_; lean_object* v_body_1914_; lean_object* v_binderType_1915_; lean_object* v_body_1916_; lean_object* v___y_1918_; lean_object* v_a_1919_; lean_object* v___x_1938_; uint8_t v_foApprox_1939_; uint8_t v_ctxApprox_1940_; uint8_t v_quasiPatternApprox_1941_; uint8_t v_constApprox_1942_; uint8_t v_isDefEqStuckEx_1943_; uint8_t v_unificationHints_1944_; uint8_t v_proofIrrelevance_1945_; uint8_t v_assignSyntheticOpaque_1946_; uint8_t v_offsetCnstrs_1947_; uint8_t v_etaStruct_1948_; uint8_t v_univApprox_1949_; uint8_t v_iota_1950_; uint8_t v_beta_1951_; uint8_t v_proj_1952_; uint8_t v_zeta_1953_; uint8_t v_zetaDelta_1954_; uint8_t v_zetaUnused_1955_; uint8_t v_zetaHave_1956_; uint8_t v_trackZetaDelta_1957_; lean_object* v_zetaDeltaSet_1958_; lean_object* v_lctx_1959_; lean_object* v_localInstances_1960_; lean_object* v_defEqCtx_x3f_1961_; lean_object* v_synthPendingDepth_1962_; lean_object* v_canUnfold_x3f_1963_; uint8_t v_univApprox_1964_; uint8_t v_inTypeClassResolution_1965_; uint8_t v_cacheInferType_1966_; lean_object* v_a_1968_; uint8_t v___x_2014_; lean_object* v_config_2015_; uint64_t v___x_2016_; uint64_t v___x_2017_; uint64_t v___x_2018_; uint64_t v___x_2019_; uint64_t v___x_2020_; uint64_t v_key_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v_binderType_1913_ = lean_ctor_get(v_lhs_1899_, 1);
lean_inc_ref_n(v_binderType_1913_, 2);
v_body_1914_ = lean_ctor_get(v_lhs_1899_, 2);
lean_inc_ref(v_body_1914_);
lean_dec_ref(v_lhs_1899_);
v_binderType_1915_ = lean_ctor_get(v_rhs_1900_, 1);
lean_inc_ref(v_binderType_1915_);
v_body_1916_ = lean_ctor_get(v_rhs_1900_, 2);
lean_inc_ref(v_body_1916_);
lean_dec_ref(v_rhs_1900_);
v___x_1938_ = l_Lean_Meta_Context_config(v_a_1908_);
v_foApprox_1939_ = lean_ctor_get_uint8(v___x_1938_, 0);
v_ctxApprox_1940_ = lean_ctor_get_uint8(v___x_1938_, 1);
v_quasiPatternApprox_1941_ = lean_ctor_get_uint8(v___x_1938_, 2);
v_constApprox_1942_ = lean_ctor_get_uint8(v___x_1938_, 3);
v_isDefEqStuckEx_1943_ = lean_ctor_get_uint8(v___x_1938_, 4);
v_unificationHints_1944_ = lean_ctor_get_uint8(v___x_1938_, 5);
v_proofIrrelevance_1945_ = lean_ctor_get_uint8(v___x_1938_, 6);
v_assignSyntheticOpaque_1946_ = lean_ctor_get_uint8(v___x_1938_, 7);
v_offsetCnstrs_1947_ = lean_ctor_get_uint8(v___x_1938_, 8);
v_etaStruct_1948_ = lean_ctor_get_uint8(v___x_1938_, 10);
v_univApprox_1949_ = lean_ctor_get_uint8(v___x_1938_, 11);
v_iota_1950_ = lean_ctor_get_uint8(v___x_1938_, 12);
v_beta_1951_ = lean_ctor_get_uint8(v___x_1938_, 13);
v_proj_1952_ = lean_ctor_get_uint8(v___x_1938_, 14);
v_zeta_1953_ = lean_ctor_get_uint8(v___x_1938_, 15);
v_zetaDelta_1954_ = lean_ctor_get_uint8(v___x_1938_, 16);
v_zetaUnused_1955_ = lean_ctor_get_uint8(v___x_1938_, 17);
v_zetaHave_1956_ = lean_ctor_get_uint8(v___x_1938_, 18);
v_trackZetaDelta_1957_ = lean_ctor_get_uint8(v_a_1908_, sizeof(void*)*7);
v_zetaDeltaSet_1958_ = lean_ctor_get(v_a_1908_, 1);
v_lctx_1959_ = lean_ctor_get(v_a_1908_, 2);
v_localInstances_1960_ = lean_ctor_get(v_a_1908_, 3);
v_defEqCtx_x3f_1961_ = lean_ctor_get(v_a_1908_, 4);
v_synthPendingDepth_1962_ = lean_ctor_get(v_a_1908_, 5);
v_canUnfold_x3f_1963_ = lean_ctor_get(v_a_1908_, 6);
v_univApprox_1964_ = lean_ctor_get_uint8(v_a_1908_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1965_ = lean_ctor_get_uint8(v_a_1908_, sizeof(void*)*7 + 2);
v_cacheInferType_1966_ = lean_ctor_get_uint8(v_a_1908_, sizeof(void*)*7 + 3);
v___x_2014_ = 1;
v_config_2015_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_config_2015_, 0, v_foApprox_1939_);
lean_ctor_set_uint8(v_config_2015_, 1, v_ctxApprox_1940_);
lean_ctor_set_uint8(v_config_2015_, 2, v_quasiPatternApprox_1941_);
lean_ctor_set_uint8(v_config_2015_, 3, v_constApprox_1942_);
lean_ctor_set_uint8(v_config_2015_, 4, v_isDefEqStuckEx_1943_);
lean_ctor_set_uint8(v_config_2015_, 5, v_unificationHints_1944_);
lean_ctor_set_uint8(v_config_2015_, 6, v_proofIrrelevance_1945_);
lean_ctor_set_uint8(v_config_2015_, 7, v_assignSyntheticOpaque_1946_);
lean_ctor_set_uint8(v_config_2015_, 8, v_offsetCnstrs_1947_);
lean_ctor_set_uint8(v_config_2015_, 9, v___x_2014_);
lean_ctor_set_uint8(v_config_2015_, 10, v_etaStruct_1948_);
lean_ctor_set_uint8(v_config_2015_, 11, v_univApprox_1949_);
lean_ctor_set_uint8(v_config_2015_, 12, v_iota_1950_);
lean_ctor_set_uint8(v_config_2015_, 13, v_beta_1951_);
lean_ctor_set_uint8(v_config_2015_, 14, v_proj_1952_);
lean_ctor_set_uint8(v_config_2015_, 15, v_zeta_1953_);
lean_ctor_set_uint8(v_config_2015_, 16, v_zetaDelta_1954_);
lean_ctor_set_uint8(v_config_2015_, 17, v_zetaUnused_1955_);
lean_ctor_set_uint8(v_config_2015_, 18, v_zetaHave_1956_);
v___x_2016_ = l_Lean_Meta_Context_configKey(v_a_1908_);
v___x_2017_ = 2ULL;
v___x_2018_ = lean_uint64_shift_right(v___x_2016_, v___x_2017_);
v___x_2019_ = lean_uint64_shift_left(v___x_2018_, v___x_2017_);
v___x_2020_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2);
v_key_2021_ = lean_uint64_lor(v___x_2019_, v___x_2020_);
v___x_2022_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2022_, 0, v_config_2015_);
lean_ctor_set_uint64(v___x_2022_, sizeof(void*)*1, v_key_2021_);
lean_inc(v_canUnfold_x3f_1963_);
lean_inc(v_synthPendingDepth_1962_);
lean_inc(v_defEqCtx_x3f_1961_);
lean_inc_ref(v_localInstances_1960_);
lean_inc_ref(v_lctx_1959_);
lean_inc(v_zetaDeltaSet_1958_);
v___x_2023_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
lean_ctor_set(v___x_2023_, 1, v_zetaDeltaSet_1958_);
lean_ctor_set(v___x_2023_, 2, v_lctx_1959_);
lean_ctor_set(v___x_2023_, 3, v_localInstances_1960_);
lean_ctor_set(v___x_2023_, 4, v_defEqCtx_x3f_1961_);
lean_ctor_set(v___x_2023_, 5, v_synthPendingDepth_1962_);
lean_ctor_set(v___x_2023_, 6, v_canUnfold_x3f_1963_);
lean_ctor_set_uint8(v___x_2023_, sizeof(void*)*7, v_trackZetaDelta_1957_);
lean_ctor_set_uint8(v___x_2023_, sizeof(void*)*7 + 1, v_univApprox_1964_);
lean_ctor_set_uint8(v___x_2023_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1965_);
lean_ctor_set_uint8(v___x_2023_, sizeof(void*)*7 + 3, v_cacheInferType_1966_);
v___x_2024_ = l_Lean_Meta_getLevel(v_binderType_1913_, v___x_2023_, v_a_1909_, v_a_1910_, v_a_1911_);
lean_dec_ref(v___x_2023_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref(v___x_2024_);
v_a_1968_ = v_a_2025_;
goto v___jp_1967_;
}
else
{
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2026_; 
v_a_2026_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2026_);
lean_dec_ref(v___x_2024_);
v_a_1968_ = v_a_2026_;
goto v___jp_1967_;
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec_ref(v___x_1938_);
lean_dec_ref(v_body_1916_);
lean_dec_ref(v_binderType_1915_);
lean_dec_ref(v_body_1914_);
lean_dec_ref(v_binderType_1913_);
v_a_2027_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2024_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2024_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
v___jp_1917_:
{
uint8_t v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = 0;
lean_inc_ref(v_binderType_1915_);
lean_inc_ref(v_binderType_1913_);
v___x_1921_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_binderType_1913_, v_binderType_1915_, v___x_1920_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v___x_1923_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref(v___x_1921_);
lean_inc_ref(v_body_1916_);
lean_inc_ref(v_body_1914_);
v___x_1923_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_body_1914_, v_body_1916_, v___x_1920_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1937_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1926_ = v___x_1923_;
v_isShared_1927_ = v_isSharedCheck_1937_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1923_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1937_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1928_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__1));
v___x_1929_ = lean_box(0);
v___x_1930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1930_, 0, v_a_1919_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___y_1918_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = l_Lean_mkConst(v___x_1928_, v___x_1931_);
v___x_1933_ = l_Lean_mkApp6(v___x_1932_, v_binderType_1913_, v_binderType_1915_, v_body_1914_, v_body_1916_, v_a_1922_, v_a_1924_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_1933_);
v___x_1935_ = v___x_1926_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
else
{
lean_dec(v_a_1922_);
lean_dec(v_a_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v_body_1916_);
lean_dec_ref(v_binderType_1915_);
lean_dec_ref(v_body_1914_);
lean_dec_ref(v_binderType_1913_);
return v___x_1923_;
}
}
else
{
lean_dec(v_a_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v_body_1916_);
lean_dec_ref(v_binderType_1915_);
lean_dec_ref(v_body_1914_);
lean_dec_ref(v_binderType_1913_);
return v___x_1921_;
}
}
v___jp_1967_:
{
uint8_t v_foApprox_1969_; uint8_t v_ctxApprox_1970_; uint8_t v_quasiPatternApprox_1971_; uint8_t v_constApprox_1972_; uint8_t v_isDefEqStuckEx_1973_; uint8_t v_unificationHints_1974_; uint8_t v_proofIrrelevance_1975_; uint8_t v_assignSyntheticOpaque_1976_; uint8_t v_offsetCnstrs_1977_; uint8_t v_etaStruct_1978_; uint8_t v_univApprox_1979_; uint8_t v_iota_1980_; uint8_t v_beta_1981_; uint8_t v_proj_1982_; uint8_t v_zeta_1983_; uint8_t v_zetaDelta_1984_; uint8_t v_zetaUnused_1985_; uint8_t v_zetaHave_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2013_; 
v_foApprox_1969_ = lean_ctor_get_uint8(v___x_1938_, 0);
v_ctxApprox_1970_ = lean_ctor_get_uint8(v___x_1938_, 1);
v_quasiPatternApprox_1971_ = lean_ctor_get_uint8(v___x_1938_, 2);
v_constApprox_1972_ = lean_ctor_get_uint8(v___x_1938_, 3);
v_isDefEqStuckEx_1973_ = lean_ctor_get_uint8(v___x_1938_, 4);
v_unificationHints_1974_ = lean_ctor_get_uint8(v___x_1938_, 5);
v_proofIrrelevance_1975_ = lean_ctor_get_uint8(v___x_1938_, 6);
v_assignSyntheticOpaque_1976_ = lean_ctor_get_uint8(v___x_1938_, 7);
v_offsetCnstrs_1977_ = lean_ctor_get_uint8(v___x_1938_, 8);
v_etaStruct_1978_ = lean_ctor_get_uint8(v___x_1938_, 10);
v_univApprox_1979_ = lean_ctor_get_uint8(v___x_1938_, 11);
v_iota_1980_ = lean_ctor_get_uint8(v___x_1938_, 12);
v_beta_1981_ = lean_ctor_get_uint8(v___x_1938_, 13);
v_proj_1982_ = lean_ctor_get_uint8(v___x_1938_, 14);
v_zeta_1983_ = lean_ctor_get_uint8(v___x_1938_, 15);
v_zetaDelta_1984_ = lean_ctor_get_uint8(v___x_1938_, 16);
v_zetaUnused_1985_ = lean_ctor_get_uint8(v___x_1938_, 17);
v_zetaHave_1986_ = lean_ctor_get_uint8(v___x_1938_, 18);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_1988_ = v___x_1938_;
v_isShared_1989_ = v_isSharedCheck_2013_;
goto v_resetjp_1987_;
}
else
{
lean_dec(v___x_1938_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2013_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
uint8_t v___x_1990_; lean_object* v_config_1992_; 
v___x_1990_ = 1;
if (v_isShared_1989_ == 0)
{
v_config_1992_ = v___x_1988_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 0, v_foApprox_1969_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 1, v_ctxApprox_1970_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 2, v_quasiPatternApprox_1971_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 3, v_constApprox_1972_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 4, v_isDefEqStuckEx_1973_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 5, v_unificationHints_1974_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 6, v_proofIrrelevance_1975_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 7, v_assignSyntheticOpaque_1976_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 8, v_offsetCnstrs_1977_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 10, v_etaStruct_1978_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 11, v_univApprox_1979_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 12, v_iota_1980_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 13, v_beta_1981_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 14, v_proj_1982_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 15, v_zeta_1983_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 16, v_zetaDelta_1984_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 17, v_zetaUnused_1985_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 18, v_zetaHave_1986_);
v_config_1992_ = v_reuseFailAlloc_2012_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
uint64_t v___x_1993_; uint64_t v___x_1994_; uint64_t v___x_1995_; uint64_t v___x_1996_; uint64_t v___x_1997_; uint64_t v_key_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
lean_ctor_set_uint8(v_config_1992_, 9, v___x_1990_);
v___x_1993_ = l_Lean_Meta_Context_configKey(v_a_1908_);
v___x_1994_ = 2ULL;
v___x_1995_ = lean_uint64_shift_right(v___x_1993_, v___x_1994_);
v___x_1996_ = lean_uint64_shift_left(v___x_1995_, v___x_1994_);
v___x_1997_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2);
v_key_1998_ = lean_uint64_lor(v___x_1996_, v___x_1997_);
v___x_1999_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1999_, 0, v_config_1992_);
lean_ctor_set_uint64(v___x_1999_, sizeof(void*)*1, v_key_1998_);
lean_inc(v_canUnfold_x3f_1963_);
lean_inc(v_synthPendingDepth_1962_);
lean_inc(v_defEqCtx_x3f_1961_);
lean_inc_ref(v_localInstances_1960_);
lean_inc_ref(v_lctx_1959_);
lean_inc(v_zetaDeltaSet_1958_);
v___x_2000_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
lean_ctor_set(v___x_2000_, 1, v_zetaDeltaSet_1958_);
lean_ctor_set(v___x_2000_, 2, v_lctx_1959_);
lean_ctor_set(v___x_2000_, 3, v_localInstances_1960_);
lean_ctor_set(v___x_2000_, 4, v_defEqCtx_x3f_1961_);
lean_ctor_set(v___x_2000_, 5, v_synthPendingDepth_1962_);
lean_ctor_set(v___x_2000_, 6, v_canUnfold_x3f_1963_);
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*7, v_trackZetaDelta_1957_);
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*7 + 1, v_univApprox_1964_);
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1965_);
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*7 + 3, v_cacheInferType_1966_);
lean_inc_ref(v_body_1914_);
v___x_2001_ = l_Lean_Meta_getLevel(v_body_1914_, v___x_2000_, v_a_1909_, v_a_1910_, v_a_1911_);
lean_dec_ref(v___x_2000_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref(v___x_2001_);
v___y_1918_ = v_a_1968_;
v_a_1919_ = v_a_2002_;
goto v___jp_1917_;
}
else
{
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2003_; 
v_a_2003_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2003_);
lean_dec_ref(v___x_2001_);
v___y_1918_ = v_a_1968_;
v_a_1919_ = v_a_2003_;
goto v___jp_1917_;
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_dec(v_a_1968_);
lean_dec_ref(v_body_1916_);
lean_dec_ref(v_binderType_1915_);
lean_dec_ref(v_body_1914_);
lean_dec_ref(v_binderType_1913_);
v_a_2004_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_2001_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_2001_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
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
lean_object* v___x_2035_; lean_object* v___x_2036_; 
lean_dec_ref(v_lhs_1899_);
lean_dec_ref(v_rhs_1900_);
v___x_2035_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4);
v___x_2036_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2035_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
return v___x_2036_;
}
}
else
{
lean_object* v___x_2037_; 
lean_inc_ref(v_lhs_1899_);
v___x_2037_ = l_Lean_Meta_Grind_useFunCC___redArg(v_lhs_1899_, v_a_1902_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; uint8_t v___x_2039_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2038_);
lean_dec_ref(v___x_2037_);
v___x_2039_ = lean_unbox(v_a_2038_);
lean_dec(v_a_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
v___x_2040_ = l_Lean_Expr_getAppNumArgs(v_lhs_1899_);
v___x_2041_ = l_Lean_Expr_getAppNumArgs(v_rhs_1900_);
v___x_2042_ = lean_nat_dec_eq(v___x_2041_, v___x_2040_);
lean_dec(v___x_2041_);
if (v___x_2042_ == 0)
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
lean_dec(v___x_2040_);
lean_dec_ref(v_rhs_1900_);
lean_dec_ref(v_lhs_1899_);
v___x_2043_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6);
v___x_2044_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2043_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
return v___x_2044_;
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2046_; uint8_t v___y_2062_; uint8_t v___y_2074_; lean_object* v___x_2078_; uint8_t v___x_2079_; uint8_t v___y_2084_; 
v___x_2045_ = l_Lean_Expr_getAppFn(v_lhs_1899_);
v___x_2046_ = l_Lean_Expr_getAppFn(v_rhs_1900_);
v___x_2078_ = lean_unsigned_to_nat(2u);
v___x_2079_ = lean_nat_dec_eq(v___x_2040_, v___x_2078_);
if (v___x_2079_ == 0)
{
v___y_2084_ = v___x_2079_;
goto v___jp_2083_;
}
else
{
lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2088_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10));
v___x_2089_ = l_Lean_Expr_isConstOf(v___x_2045_, v___x_2088_);
v___y_2084_ = v___x_2089_;
goto v___jp_2083_;
}
v___jp_2047_:
{
lean_object* v___x_2048_; 
lean_inc_ref(v_rhs_1900_);
lean_inc_ref(v_lhs_1899_);
v___x_2048_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(v_lhs_1899_, v_rhs_1900_, v___x_2045_, v___x_2046_, v___x_2040_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
lean_dec_ref(v___x_2046_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; uint8_t v___x_2050_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2049_);
lean_dec_ref(v___x_2048_);
v___x_2050_ = lean_unbox(v_a_2049_);
lean_dec(v_a_2049_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; 
v___x_2051_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_1899_, v_rhs_1900_, v_heq_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
return v___x_2051_;
}
else
{
lean_object* v___x_2052_; 
v___x_2052_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_1899_, v_rhs_1900_, v_heq_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
lean_dec_ref(v_rhs_1900_);
lean_dec_ref(v_lhs_1899_);
return v___x_2052_;
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec_ref(v_rhs_1900_);
lean_dec_ref(v_lhs_1899_);
v_a_2053_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2048_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2048_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
v___jp_2061_:
{
if (v___y_2062_ == 0)
{
goto v___jp_2047_;
}
else
{
lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2063_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_2064_ = l_Lean_Expr_isConstOf(v___x_2046_, v___x_2063_);
if (v___x_2064_ == 0)
{
goto v___jp_2047_;
}
else
{
lean_object* v___x_2065_; 
lean_dec_ref(v___x_2046_);
lean_dec_ref(v___x_2045_);
lean_dec(v___x_2040_);
v___x_2065_ = l_Lean_Meta_Grind_mkEqCongrProof(v_lhs_1899_, v_rhs_1900_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_2065_) == 0)
{
if (v_heq_1901_ == 0)
{
return v___x_2065_;
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2067_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref(v___x_2065_);
v___x_2067_ = l_Lean_Meta_mkHEqOfEq(v_a_2066_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
return v___x_2067_;
}
}
else
{
return v___x_2065_;
}
}
}
}
v___jp_2068_:
{
lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2069_ = lean_unsigned_to_nat(3u);
v___x_2070_ = lean_nat_dec_eq(v___x_2040_, v___x_2069_);
if (v___x_2070_ == 0)
{
v___y_2062_ = v___x_2070_;
goto v___jp_2061_;
}
else
{
lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2071_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_2072_ = l_Lean_Expr_isConstOf(v___x_2045_, v___x_2071_);
v___y_2062_ = v___x_2072_;
goto v___jp_2061_;
}
}
v___jp_2073_:
{
if (v___y_2074_ == 0)
{
goto v___jp_2068_;
}
else
{
lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2075_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8));
v___x_2076_ = l_Lean_Expr_isConstOf(v___x_2046_, v___x_2075_);
if (v___x_2076_ == 0)
{
goto v___jp_2068_;
}
else
{
lean_object* v___x_2077_; 
lean_dec_ref(v___x_2046_);
lean_dec_ref(v___x_2045_);
lean_dec(v___x_2040_);
v___x_2077_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_1899_, v_rhs_1900_, v_heq_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
lean_dec_ref(v_rhs_1900_);
lean_dec_ref(v_lhs_1899_);
return v___x_2077_;
}
}
}
v___jp_2080_:
{
if (v___x_2079_ == 0)
{
v___y_2074_ = v___x_2079_;
goto v___jp_2073_;
}
else
{
lean_object* v___x_2081_; uint8_t v___x_2082_; 
v___x_2081_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8));
v___x_2082_ = l_Lean_Expr_isConstOf(v___x_2045_, v___x_2081_);
v___y_2074_ = v___x_2082_;
goto v___jp_2073_;
}
}
v___jp_2083_:
{
if (v___y_2084_ == 0)
{
goto v___jp_2080_;
}
else
{
lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2085_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10));
v___x_2086_ = l_Lean_Expr_isConstOf(v___x_2046_, v___x_2085_);
if (v___x_2086_ == 0)
{
goto v___jp_2080_;
}
else
{
lean_object* v___x_2087_; 
lean_dec_ref(v___x_2046_);
lean_dec_ref(v___x_2045_);
lean_dec(v___x_2040_);
v___x_2087_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_1899_, v_rhs_1900_, v_heq_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
lean_dec_ref(v_rhs_1900_);
lean_dec_ref(v_lhs_1899_);
return v___x_2087_;
}
}
}
}
}
else
{
lean_object* v___x_2090_; 
v___x_2090_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_1899_, v_rhs_1900_, v_heq_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
return v___x_2090_;
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec_ref(v_rhs_1900_);
lean_dec_ref(v_lhs_1899_);
v_a_2091_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2037_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2037_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(lean_object* v_lhs_2099_, lean_object* v_rhs_2100_, lean_object* v_h_2101_, uint8_t v_flipped_2102_, uint8_t v_heq_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2115_ = l_Lean_Meta_Grind_congrPlaceholderProof;
v___x_2116_ = lean_expr_eqv(v_h_2101_, v___x_2115_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2117_ = l_Lean_Meta_Grind_eqCongrSymmPlaceholderProof;
v___x_2118_ = lean_expr_eqv(v_h_2101_, v___x_2117_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; 
lean_dec_ref(v_rhs_2100_);
lean_dec_ref(v_lhs_2099_);
v___x_2119_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(v_h_2101_, v_flipped_2102_, v_heq_2103_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
return v___x_2119_;
}
else
{
lean_object* v___x_2120_; 
lean_dec_ref(v_h_2101_);
v___x_2120_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(v_lhs_2099_, v_rhs_2100_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
if (lean_obj_tag(v___x_2120_) == 0)
{
if (v_heq_2103_ == 0)
{
return v___x_2120_;
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2122_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref(v___x_2120_);
v___x_2122_ = l_Lean_Meta_mkHEqOfEq(v_a_2121_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
return v___x_2122_;
}
}
else
{
return v___x_2120_;
}
}
}
else
{
lean_object* v___x_2123_; 
lean_dec_ref(v_h_2101_);
v___x_2123_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(v_lhs_2099_, v_rhs_2100_, v_heq_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
return v___x_2123_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1(void){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2125_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2126_ = lean_unsigned_to_nat(29u);
v___x_2127_ = lean_unsigned_to_nat(288u);
v___x_2128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0));
v___x_2129_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2130_ = l_mkPanicMessageWithDecl(v___x_2129_, v___x_2128_, v___x_2127_, v___x_2126_, v___x_2125_);
return v___x_2130_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2(void){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2131_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2132_ = lean_unsigned_to_nat(35u);
v___x_2133_ = lean_unsigned_to_nat(287u);
v___x_2134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0));
v___x_2135_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2136_ = l_mkPanicMessageWithDecl(v___x_2135_, v___x_2134_, v___x_2133_, v___x_2132_, v___x_2131_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(lean_object* v_lhs_2137_, lean_object* v_common_2138_, lean_object* v_acc_2139_, uint8_t v_heq_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
uint8_t v___x_2152_; 
v___x_2152_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_lhs_2137_, v_common_2138_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = lean_st_ref_get(v_a_2141_);
lean_inc_ref(v_lhs_2137_);
v___x_2154_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2153_, v_lhs_2137_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v_target_x3f_2156_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref(v___x_2154_);
v_target_x3f_2156_ = lean_ctor_get(v_a_2155_, 4);
lean_inc(v_target_x3f_2156_);
if (lean_obj_tag(v_target_x3f_2156_) == 1)
{
lean_object* v_proof_x3f_2157_; 
v_proof_x3f_2157_ = lean_ctor_get(v_a_2155_, 5);
lean_inc(v_proof_x3f_2157_);
if (lean_obj_tag(v_proof_x3f_2157_) == 1)
{
uint8_t v_flipped_2158_; lean_object* v_val_2159_; lean_object* v_val_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2188_; 
v_flipped_2158_ = lean_ctor_get_uint8(v_a_2155_, sizeof(void*)*11);
lean_dec(v_a_2155_);
v_val_2159_ = lean_ctor_get(v_target_x3f_2156_, 0);
lean_inc(v_val_2159_);
lean_dec_ref(v_target_x3f_2156_);
v_val_2160_ = lean_ctor_get(v_proof_x3f_2157_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_proof_x3f_2157_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2162_ = v_proof_x3f_2157_;
v_isShared_2163_ = v_isSharedCheck_2188_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_val_2160_);
lean_dec(v_proof_x3f_2157_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2188_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2164_; 
lean_inc(v_val_2159_);
v___x_2164_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_lhs_2137_, v_val_2159_, v_val_2160_, v_flipped_2158_, v_heq_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2166_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref(v___x_2164_);
v___x_2166_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_acc_2139_, v_a_2165_, v_heq_2140_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2169_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2167_);
lean_dec_ref(v___x_2166_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v_a_2167_);
v___x_2169_ = v___x_2162_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2167_);
v___x_2169_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
v_lhs_2137_ = v_val_2159_;
v_acc_2139_ = v___x_2169_;
goto _start;
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_del_object(v___x_2162_);
lean_dec(v_val_2159_);
v_a_2172_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2166_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2166_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_del_object(v___x_2162_);
lean_dec(v_val_2159_);
lean_dec(v_acc_2139_);
v_a_2180_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2164_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2164_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
else
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
lean_dec(v_proof_x3f_2157_);
lean_dec_ref(v_target_x3f_2156_);
lean_dec(v_a_2155_);
lean_dec(v_acc_2139_);
lean_dec_ref(v_lhs_2137_);
v___x_2189_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1);
v___x_2190_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2189_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
return v___x_2190_;
}
}
else
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_dec(v_target_x3f_2156_);
lean_dec(v_a_2155_);
lean_dec(v_acc_2139_);
lean_dec_ref(v_lhs_2137_);
v___x_2191_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2);
v___x_2192_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2191_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
return v___x_2192_;
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec(v_acc_2139_);
lean_dec_ref(v_lhs_2137_);
v_a_2193_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2154_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2154_);
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
else
{
lean_object* v___x_2201_; 
lean_dec_ref(v_lhs_2137_);
v___x_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2201_, 0, v_acc_2139_);
return v___x_2201_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2203_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2204_ = lean_unsigned_to_nat(29u);
v___x_2205_ = lean_unsigned_to_nat(300u);
v___x_2206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0));
v___x_2207_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2208_ = l_mkPanicMessageWithDecl(v___x_2207_, v___x_2206_, v___x_2205_, v___x_2204_, v___x_2203_);
return v___x_2208_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2(void){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2209_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2210_ = lean_unsigned_to_nat(35u);
v___x_2211_ = lean_unsigned_to_nat(299u);
v___x_2212_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0));
v___x_2213_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2214_ = l_mkPanicMessageWithDecl(v___x_2213_, v___x_2212_, v___x_2211_, v___x_2210_, v___x_2209_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(lean_object* v_rhs_2215_, lean_object* v_common_2216_, lean_object* v_lhsEqCommon_x3f_2217_, uint8_t v_heq_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_){
_start:
{
uint8_t v___x_2230_; 
v___x_2230_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_rhs_2215_, v_common_2216_);
if (v___x_2230_ == 0)
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = lean_st_ref_get(v_a_2219_);
lean_inc_ref(v_rhs_2215_);
v___x_2232_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2231_, v_rhs_2215_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v_target_x3f_2234_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref(v___x_2232_);
v_target_x3f_2234_ = lean_ctor_get(v_a_2233_, 4);
lean_inc(v_target_x3f_2234_);
if (lean_obj_tag(v_target_x3f_2234_) == 1)
{
lean_object* v_proof_x3f_2235_; 
v_proof_x3f_2235_ = lean_ctor_get(v_a_2233_, 5);
lean_inc(v_proof_x3f_2235_);
if (lean_obj_tag(v_proof_x3f_2235_) == 1)
{
uint8_t v_flipped_2236_; lean_object* v_val_2237_; lean_object* v_val_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2277_; 
v_flipped_2236_ = lean_ctor_get_uint8(v_a_2233_, sizeof(void*)*11);
lean_dec(v_a_2233_);
v_val_2237_ = lean_ctor_get(v_target_x3f_2234_, 0);
lean_inc(v_val_2237_);
lean_dec_ref(v_target_x3f_2234_);
v_val_2238_ = lean_ctor_get(v_proof_x3f_2235_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v_proof_x3f_2235_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2240_ = v_proof_x3f_2235_;
v_isShared_2241_ = v_isSharedCheck_2277_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_val_2238_);
lean_dec(v_proof_x3f_2235_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2277_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
uint8_t v___y_2243_; 
if (v_flipped_2236_ == 0)
{
uint8_t v___x_2276_; 
v___x_2276_ = 1;
v___y_2243_ = v___x_2276_;
goto v___jp_2242_;
}
else
{
v___y_2243_ = v___x_2230_;
goto v___jp_2242_;
}
v___jp_2242_:
{
lean_object* v___x_2244_; 
lean_inc(v_val_2237_);
v___x_2244_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_val_2237_, v_rhs_2215_, v_val_2238_, v___y_2243_, v_heq_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v___x_2246_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
lean_dec_ref(v___x_2244_);
v___x_2246_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_val_2237_, v_common_2216_, v_lhsEqCommon_x3f_2217_, v_heq_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2248_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref(v___x_2246_);
v___x_2248_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_a_2247_, v_a_2245_, v_heq_2218_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2259_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2251_ = v___x_2248_;
v_isShared_2252_ = v_isSharedCheck_2259_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2248_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2259_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v_a_2249_);
v___x_2254_ = v___x_2240_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
lean_object* v___x_2256_; 
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2254_);
v___x_2256_ = v___x_2251_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
lean_del_object(v___x_2240_);
v_a_2260_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2248_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2248_);
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
lean_dec(v_a_2245_);
lean_del_object(v___x_2240_);
return v___x_2246_;
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_del_object(v___x_2240_);
lean_dec(v_val_2237_);
lean_dec(v_lhsEqCommon_x3f_2217_);
v_a_2268_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2244_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2244_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
}
else
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_dec_ref(v_target_x3f_2234_);
lean_dec(v_proof_x3f_2235_);
lean_dec(v_a_2233_);
lean_dec(v_lhsEqCommon_x3f_2217_);
lean_dec_ref(v_rhs_2215_);
v___x_2278_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1);
v___x_2279_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2278_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
return v___x_2279_;
}
}
else
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
lean_dec(v_target_x3f_2234_);
lean_dec(v_a_2233_);
lean_dec(v_lhsEqCommon_x3f_2217_);
lean_dec_ref(v_rhs_2215_);
v___x_2280_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2);
v___x_2281_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2280_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
return v___x_2281_;
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_dec(v_lhsEqCommon_x3f_2217_);
lean_dec_ref(v_rhs_2215_);
v_a_2282_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2232_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2232_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
else
{
lean_object* v___x_2290_; 
lean_dec_ref(v_rhs_2215_);
v___x_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2290_, 0, v_lhsEqCommon_x3f_2217_);
return v___x_2290_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3(void){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2291_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2292_ = lean_unsigned_to_nat(72u);
v___x_2293_ = lean_unsigned_to_nat(321u);
v___x_2294_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0));
v___x_2295_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2296_ = l_mkPanicMessageWithDecl(v___x_2295_, v___x_2294_, v___x_2293_, v___x_2292_, v___x_2291_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(lean_object* v_lhs_2297_, lean_object* v_rhs_2298_, uint8_t v_heq_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
uint8_t v___x_2311_; 
v___x_2311_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_lhs_2297_, v_rhs_2298_);
if (v___x_2311_ == 0)
{
lean_object* v___x_2312_; 
lean_inc_ref(v_lhs_2297_);
v___x_2312_ = l_Lean_Meta_Grind_getRootENode___redArg(v_lhs_2297_, v_a_2300_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
lean_dec_ref(v___x_2312_);
v___x_2314_ = lean_st_ref_get(v_a_2300_);
lean_inc_ref(v_lhs_2297_);
v___x_2315_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2314_, v_lhs_2297_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref(v___x_2315_);
v___x_2317_ = lean_st_ref_get(v_a_2300_);
lean_inc_ref(v_rhs_2298_);
v___x_2318_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2317_, v_rhs_2298_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v_root_2320_; lean_object* v_root_2321_; uint8_t v___x_2322_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref(v___x_2318_);
v_root_2320_ = lean_ctor_get(v_a_2316_, 2);
lean_inc_ref(v_root_2320_);
lean_dec(v_a_2316_);
v_root_2321_ = lean_ctor_get(v_a_2319_, 2);
lean_inc_ref(v_root_2321_);
lean_dec(v_a_2319_);
v___x_2322_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_root_2320_, v_root_2321_);
lean_dec_ref(v_root_2321_);
lean_dec_ref(v_root_2320_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
lean_dec(v_a_2313_);
lean_dec_ref(v_rhs_2298_);
lean_dec_ref(v_lhs_2297_);
v___x_2323_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2);
v___x_2324_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2323_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
return v___x_2324_;
}
else
{
lean_object* v___x_2325_; 
lean_inc_ref(v_rhs_2298_);
lean_inc_ref(v_lhs_2297_);
v___x_2325_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(v_lhs_2297_, v_rhs_2298_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; uint8_t v_heqProofs_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref(v___x_2325_);
v_heqProofs_2327_ = lean_ctor_get_uint8(v_a_2313_, sizeof(void*)*11 + 4);
lean_dec(v_a_2313_);
v___x_2328_ = lean_box(0);
v___x_2329_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_2297_, v_a_2326_, v___x_2328_, v_heqProofs_2327_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2331_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref(v___x_2329_);
v___x_2331_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_2298_, v_a_2326_, v_a_2330_, v_heqProofs_2327_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
lean_dec(v_a_2326_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2347_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2334_ = v___x_2331_;
v_isShared_2335_ = v_isSharedCheck_2347_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2331_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2347_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
if (lean_obj_tag(v_a_2332_) == 1)
{
lean_object* v_val_2336_; uint8_t v___y_2341_; 
v_val_2336_ = lean_ctor_get(v_a_2332_, 0);
lean_inc(v_val_2336_);
lean_dec_ref(v_a_2332_);
if (v_heq_2299_ == 0)
{
if (v_heqProofs_2327_ == 0)
{
v___y_2341_ = v___x_2322_;
goto v___jp_2340_;
}
else
{
lean_del_object(v___x_2334_);
goto v___jp_2337_;
}
}
else
{
v___y_2341_ = v_heqProofs_2327_;
goto v___jp_2340_;
}
v___jp_2337_:
{
if (v_heq_2299_ == 0)
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Lean_Meta_mkEqOfHEq(v_val_2336_, v_heq_2299_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
return v___x_2338_;
}
else
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_Meta_mkHEqOfEq(v_val_2336_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
return v___x_2339_;
}
}
v___jp_2340_:
{
if (v___y_2341_ == 0)
{
lean_del_object(v___x_2334_);
goto v___jp_2337_;
}
else
{
lean_object* v___x_2343_; 
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 0, v_val_2336_);
v___x_2343_ = v___x_2334_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_val_2336_);
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
lean_object* v___x_2345_; lean_object* v___x_2346_; 
lean_del_object(v___x_2334_);
lean_dec(v_a_2332_);
v___x_2345_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3);
v___x_2346_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2345_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
return v___x_2346_;
}
}
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
v_a_2348_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2331_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2331_);
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
lean_dec(v_a_2326_);
lean_dec_ref(v_rhs_2298_);
v_a_2356_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2329_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2329_);
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
lean_dec(v_a_2313_);
lean_dec_ref(v_rhs_2298_);
lean_dec_ref(v_lhs_2297_);
return v___x_2325_;
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec(v_a_2316_);
lean_dec(v_a_2313_);
lean_dec_ref(v_rhs_2298_);
lean_dec_ref(v_lhs_2297_);
v_a_2364_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2318_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2318_);
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
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_dec(v_a_2313_);
lean_dec_ref(v_rhs_2298_);
lean_dec_ref(v_lhs_2297_);
v_a_2372_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2315_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2315_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_dec_ref(v_rhs_2298_);
lean_dec_ref(v_lhs_2297_);
v_a_2380_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2312_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2312_);
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
lean_object* v___x_2388_; 
lean_dec_ref(v_rhs_2298_);
v___x_2388_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(v_lhs_2297_, v_heq_2299_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
return v___x_2388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(lean_object* v_thm_2389_, lean_object* v_lhs_2390_, lean_object* v_rhs_2391_, lean_object* v_i_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_){
_start:
{
lean_object* v___x_2404_; uint8_t v___x_2405_; 
v___x_2404_ = lean_unsigned_to_nat(0u);
v___x_2405_ = lean_nat_dec_lt(v___x_2404_, v_i_2392_);
if (v___x_2405_ == 0)
{
lean_object* v_proof_2406_; lean_object* v___x_2407_; 
v_proof_2406_ = lean_ctor_get(v_thm_2389_, 1);
lean_inc_ref(v_proof_2406_);
v___x_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2407_, 0, v_proof_2406_);
return v___x_2407_;
}
else
{
lean_object* v___x_2408_; lean_object* v_i_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2408_ = lean_unsigned_to_nat(1u);
v_i_2409_ = lean_nat_sub(v_i_2392_, v___x_2408_);
v___x_2410_ = l_Lean_Expr_appFn_x21(v_lhs_2390_);
v___x_2411_ = l_Lean_Expr_appFn_x21(v_rhs_2391_);
v___x_2412_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_2389_, v___x_2410_, v___x_2411_, v_i_2409_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
lean_dec_ref(v___x_2411_);
lean_dec_ref(v___x_2410_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v_argKinds_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; uint8_t v___y_2418_; uint8_t v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; uint8_t v___x_2432_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2413_);
lean_dec_ref(v___x_2412_);
v_argKinds_2414_ = lean_ctor_get(v_thm_2389_, 2);
v___x_2415_ = l_Lean_Expr_appArg_x21(v_lhs_2390_);
v___x_2416_ = l_Lean_Expr_appArg_x21(v_rhs_2391_);
v___x_2429_ = 0;
v___x_2430_ = lean_box(v___x_2429_);
v___x_2431_ = lean_array_get(v___x_2430_, v_argKinds_2414_, v_i_2409_);
lean_dec(v_i_2409_);
lean_dec(v___x_2430_);
v___x_2432_ = lean_unbox(v___x_2431_);
lean_dec(v___x_2431_);
if (v___x_2432_ == 4)
{
v___y_2418_ = v___x_2405_;
goto v___jp_2417_;
}
else
{
uint8_t v___x_2433_; 
v___x_2433_ = 0;
v___y_2418_ = v___x_2433_;
goto v___jp_2417_;
}
v___jp_2417_:
{
lean_object* v___x_2419_; 
lean_inc_ref(v___x_2416_);
lean_inc_ref(v___x_2415_);
v___x_2419_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___x_2415_, v___x_2416_, v___y_2418_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2428_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2422_ = v___x_2419_;
v_isShared_2423_ = v_isSharedCheck_2428_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2419_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2428_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2424_; lean_object* v___x_2426_; 
v___x_2424_ = l_Lean_mkApp3(v_a_2413_, v___x_2415_, v___x_2416_, v_a_2420_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2424_);
v___x_2426_ = v___x_2422_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
else
{
lean_dec_ref(v___x_2416_);
lean_dec_ref(v___x_2415_);
lean_dec(v_a_2413_);
return v___x_2419_;
}
}
}
else
{
lean_dec(v_i_2409_);
return v___x_2412_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(lean_object* v_f_2437_, lean_object* v_g_2438_, lean_object* v_numArgs_2439_, lean_object* v_lhs_2440_, lean_object* v_rhs_2441_, uint8_t v_heq_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v___x_2454_; 
lean_inc(v_numArgs_2439_);
lean_inc_ref(v_f_2437_);
v___x_2454_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(v_f_2437_, v_numArgs_2439_, v_a_2446_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v_argKinds_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
lean_dec_ref(v___x_2454_);
v_argKinds_2456_ = lean_ctor_get(v_a_2455_, 2);
v___x_2457_ = lean_array_get_size(v_argKinds_2456_);
v___x_2458_ = lean_nat_dec_eq(v___x_2457_, v_numArgs_2439_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
lean_dec(v_a_2455_);
lean_dec_ref(v_rhs_2441_);
lean_dec_ref(v_lhs_2440_);
lean_dec(v_numArgs_2439_);
lean_dec_ref(v_g_2438_);
lean_dec_ref(v_f_2437_);
v___x_2459_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2);
v___x_2460_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2459_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
return v___x_2460_;
}
else
{
lean_object* v___x_2461_; 
v___x_2461_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_2455_, v_lhs_2440_, v_rhs_2441_, v_numArgs_2439_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
lean_dec(v_a_2455_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; uint8_t v___x_2463_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_a_2462_);
lean_dec_ref(v___x_2461_);
v___x_2463_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_f_2437_, v_g_2438_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__4));
v___x_2465_ = l_Lean_Core_mkFreshUserName(v___x_2464_, v_a_2451_, v_a_2452_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2467_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref(v___x_2465_);
lean_inc(v_a_2452_);
lean_inc_ref(v_a_2451_);
lean_inc(v_a_2450_);
lean_inc_ref(v_a_2449_);
lean_inc_ref(v_f_2437_);
v___x_2467_ = lean_infer_type(v_f_2437_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___f_2471_; lean_object* v___x_2472_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2468_);
lean_dec_ref(v___x_2467_);
v___x_2469_ = lean_box(v___x_2463_);
v___x_2470_ = lean_box(v___x_2458_);
v___f_2471_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___boxed), 17, 5);
lean_closure_set(v___f_2471_, 0, v_numArgs_2439_);
lean_closure_set(v___f_2471_, 1, v_rhs_2441_);
lean_closure_set(v___f_2471_, 2, v_lhs_2440_);
lean_closure_set(v___f_2471_, 3, v___x_2469_);
lean_closure_set(v___f_2471_, 4, v___x_2470_);
v___x_2472_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_a_2466_, v_a_2468_, v___f_2471_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; lean_object* v___x_2474_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_a_2473_);
lean_dec_ref(v___x_2472_);
v___x_2474_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_f_2437_, v_g_2438_, v___x_2463_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v___x_2476_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref(v___x_2474_);
v___x_2476_ = l_Lean_Meta_mkEqNDRec(v_a_2473_, v_a_2462_, v_a_2475_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v___x_2478_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2477_);
lean_dec_ref(v___x_2476_);
v___x_2478_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_2477_, v_heq_2442_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
return v___x_2478_;
}
else
{
return v___x_2476_;
}
}
else
{
lean_dec(v_a_2473_);
lean_dec(v_a_2462_);
return v___x_2474_;
}
}
else
{
lean_dec(v_a_2462_);
lean_dec_ref(v_g_2438_);
lean_dec_ref(v_f_2437_);
return v___x_2472_;
}
}
else
{
lean_dec(v_a_2466_);
lean_dec(v_a_2462_);
lean_dec_ref(v_rhs_2441_);
lean_dec_ref(v_lhs_2440_);
lean_dec(v_numArgs_2439_);
lean_dec_ref(v_g_2438_);
lean_dec_ref(v_f_2437_);
return v___x_2467_;
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec(v_a_2462_);
lean_dec_ref(v_rhs_2441_);
lean_dec_ref(v_lhs_2440_);
lean_dec(v_numArgs_2439_);
lean_dec_ref(v_g_2438_);
lean_dec_ref(v_f_2437_);
v_a_2479_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2465_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2465_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
else
{
lean_object* v___x_2487_; 
lean_dec_ref(v_rhs_2441_);
lean_dec_ref(v_lhs_2440_);
lean_dec(v_numArgs_2439_);
lean_dec_ref(v_g_2438_);
lean_dec_ref(v_f_2437_);
v___x_2487_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_2462_, v_heq_2442_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
return v___x_2487_;
}
}
else
{
lean_dec_ref(v_rhs_2441_);
lean_dec_ref(v_lhs_2440_);
lean_dec(v_numArgs_2439_);
lean_dec_ref(v_g_2438_);
lean_dec_ref(v_f_2437_);
return v___x_2461_;
}
}
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
lean_dec_ref(v_rhs_2441_);
lean_dec_ref(v_lhs_2440_);
lean_dec(v_numArgs_2439_);
lean_dec_ref(v_g_2438_);
lean_dec_ref(v_f_2437_);
v_a_2488_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_2454_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2454_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1(void){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2497_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2498_ = lean_unsigned_to_nat(27u);
v___x_2499_ = lean_unsigned_to_nat(237u);
v___x_2500_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0));
v___x_2501_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2502_ = l_mkPanicMessageWithDecl(v___x_2501_, v___x_2500_, v___x_2499_, v___x_2498_, v___x_2497_);
return v___x_2502_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2(void){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2503_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2504_ = lean_unsigned_to_nat(27u);
v___x_2505_ = lean_unsigned_to_nat(236u);
v___x_2506_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0));
v___x_2507_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2508_ = l_mkPanicMessageWithDecl(v___x_2507_, v___x_2506_, v___x_2505_, v___x_2504_, v___x_2503_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(lean_object* v_lhs_2509_, lean_object* v_rhs_2510_, uint8_t v_heq_2511_, lean_object* v_e_u2081_2512_, lean_object* v_e_u2082_2513_, lean_object* v_numArgs_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_){
_start:
{
if (lean_obj_tag(v_e_u2081_2512_) == 5)
{
if (lean_obj_tag(v_e_u2082_2513_) == 5)
{
lean_object* v_fn_2526_; lean_object* v_fn_2527_; lean_object* v___x_2528_; lean_object* v_numArgs_2529_; uint8_t v___x_2530_; 
v_fn_2526_ = lean_ctor_get(v_e_u2081_2512_, 0);
lean_inc_ref(v_fn_2526_);
lean_dec_ref(v_e_u2081_2512_);
v_fn_2527_ = lean_ctor_get(v_e_u2082_2513_, 0);
lean_inc_ref(v_fn_2527_);
lean_dec_ref(v_e_u2082_2513_);
v___x_2528_ = lean_unsigned_to_nat(1u);
v_numArgs_2529_ = lean_nat_add(v_numArgs_2514_, v___x_2528_);
lean_dec(v_numArgs_2514_);
v___x_2530_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_2526_, v_fn_2527_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; 
lean_inc_ref(v_fn_2527_);
lean_inc_ref(v_fn_2526_);
v___x_2531_ = l_Lean_Meta_Grind_hasSameType(v_fn_2526_, v_fn_2527_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; uint8_t v___x_2533_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2532_);
lean_dec_ref(v___x_2531_);
v___x_2533_ = lean_unbox(v_a_2532_);
lean_dec(v_a_2532_);
if (v___x_2533_ == 0)
{
v_e_u2081_2512_ = v_fn_2526_;
v_e_u2082_2513_ = v_fn_2527_;
v_numArgs_2514_ = v_numArgs_2529_;
goto _start;
}
else
{
lean_object* v___x_2535_; 
v___x_2535_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_2526_, v_fn_2527_, v_numArgs_2529_, v_lhs_2509_, v_rhs_2510_, v_heq_2511_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
return v___x_2535_;
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec(v_numArgs_2529_);
lean_dec_ref(v_fn_2527_);
lean_dec_ref(v_fn_2526_);
lean_dec_ref(v_rhs_2510_);
lean_dec_ref(v_lhs_2509_);
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
v___x_2544_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_2526_, v_fn_2527_, v_numArgs_2529_, v_lhs_2509_, v_rhs_2510_, v_heq_2511_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
return v___x_2544_;
}
}
else
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
lean_dec_ref(v_e_u2081_2512_);
lean_dec(v_numArgs_2514_);
lean_dec_ref(v_e_u2082_2513_);
lean_dec_ref(v_rhs_2510_);
lean_dec_ref(v_lhs_2509_);
v___x_2545_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1);
v___x_2546_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2545_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
return v___x_2546_;
}
}
else
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
lean_dec(v_numArgs_2514_);
lean_dec_ref(v_e_u2082_2513_);
lean_dec_ref(v_e_u2081_2512_);
lean_dec_ref(v_rhs_2510_);
lean_dec_ref(v_lhs_2509_);
v___x_2547_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2);
v___x_2548_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2547_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop___boxed(lean_object* v_lhs_2736_, lean_object* v_rhs_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_2736_, v_rhs_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
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
lean_dec_ref(v_rhs_2737_);
lean_dec_ref(v_lhs_2736_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___boxed(lean_object* v_lhs_2750_, lean_object* v_rhs_2751_, lean_object* v_heq_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_){
_start:
{
uint8_t v_heq_boxed_2764_; lean_object* v_res_2765_; 
v_heq_boxed_2764_ = lean_unbox(v_heq_2752_);
v_res_2765_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_2750_, v_rhs_2751_, v_heq_boxed_2764_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
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
lean_dec_ref(v___x_2987_);
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
lean_dec_ref(v___x_2990_);
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
lean_dec_ref(v___x_2992_);
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
