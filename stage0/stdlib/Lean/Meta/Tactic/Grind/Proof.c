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
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "heq_congr'"};
static const lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__3_value),LEAN_SCALAR_PTR_LITERAL(12, 59, 80, 84, 143, 62, 233, 44)}};
static const lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 225, .m_capacity = 225, .m_length = 216, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Proof.1529172837._hygCtx._hyg.980.0 ).hasSameRoot a₁ b₂ && ( __do_lift._@.Lean.Meta.Tactic.Grind.Proof.1529172837._hygCtx._hyg.980.1 ).hasSameRoot b₁ a₂\n    "};
static const lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6;
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
static const lean_string_object l_Lean_Meta_Grind_mkEqCongrProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "heq_congr"};
static const lean_object* l_Lean_Meta_Grind_mkEqCongrProof___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_mkEqCongrProof___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkEqCongrProof___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkEqCongrProof___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkEqCongrProof___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkEqCongrProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkEqCongrProof___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_mkEqCongrProof___closed__3_value),LEAN_SCALAR_PTR_LITERAL(42, 237, 37, 65, 223, 91, 106, 181)}};
static const lean_object* l_Lean_Meta_Grind_mkEqCongrProof___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_mkEqCongrProof___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_mkEqCongrProof___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 225, .m_capacity = 225, .m_length = 216, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Proof.1529172837._hygCtx._hyg.502.0 ).hasSameRoot a₁ a₂ && ( __do_lift._@.Lean.Meta.Tactic.Grind.Proof.1529172837._hygCtx._hyg.502.1 ).hasSameRoot b₁ b₂\n    "};
static const lean_object* l_Lean_Meta_Grind_mkEqCongrProof___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_mkEqCongrProof___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkEqCongrProof___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkEqCongrProof___closed__6;
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
lean_dec(v_a_8_);
lean_dec_ref(v_a_7_);
lean_dec(v_a_6_);
lean_dec_ref(v_a_5_);
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
lean_inc(v_a_90_);
lean_inc_ref(v_a_89_);
lean_inc(v_a_88_);
lean_inc_ref(v_a_87_);
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
lean_inc(v_a_90_);
lean_inc_ref(v_a_89_);
lean_inc(v_a_88_);
lean_inc_ref(v_a_87_);
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
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
return v___x_104_;
}
}
}
else
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
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
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
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
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
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
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
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
lean_object* v___x_215_; lean_object* v___x_9159__overap_216_; lean_object* v___x_217_; 
v___x_215_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0);
v___x_9159__overap_216_ = lean_panic_fn(v___x_215_, v_msg_203_);
v___x_217_ = lean_apply_11(v___x_9159__overap_216_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, lean_box(0));
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___boxed(lean_object* v_msg_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3(v_msg_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
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
lean_object* v___x_244_; lean_object* v___x_10021__overap_245_; lean_object* v___x_246_; 
v___x_244_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0);
v___x_10021__overap_245_ = lean_panic_fn(v___x_244_, v_msg_232_);
v___x_246_ = lean_apply_11(v___x_10021__overap_245_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, lean_box(0));
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___boxed(lean_object* v_msg_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v_msg_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
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
v___x_448_ = lean_nat_add(v___y_445_, v___y_447_);
lean_dec(v___y_447_);
lean_dec(v___y_445_);
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
lean_ctor_set(v___x_428_, 3, v___y_446_);
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
lean_ctor_set(v_reuseFailAlloc_453_, 3, v___y_446_);
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
v___y_445_ = v___x_461_;
v___y_446_ = v___x_460_;
v___y_447_ = v_size_462_;
goto v___jp_444_;
}
else
{
lean_object* v___x_463_; 
v___x_463_ = lean_unsigned_to_nat(0u);
v___y_445_ = v___x_461_;
v___y_446_ = v___x_460_;
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
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec(v___y_628_);
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
lean_inc(v___y_637_);
lean_inc_ref(v___y_636_);
lean_inc(v___y_635_);
lean_inc_ref(v___y_634_);
lean_inc(v___y_633_);
lean_inc_ref(v___y_632_);
lean_inc(v___y_631_);
lean_inc_ref(v___y_630_);
lean_inc(v___y_629_);
lean_inc(v___y_628_);
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
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec(v___y_628_);
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
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec(v___y_628_);
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
lean_inc(v_a_720_);
lean_inc_ref(v_a_719_);
lean_inc(v_a_718_);
lean_inc_ref(v_a_717_);
lean_inc(v_a_716_);
lean_inc_ref(v_a_715_);
lean_inc(v_a_714_);
lean_inc_ref(v_a_713_);
lean_inc(v_a_712_);
lean_inc(v_a_711_);
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
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec(v_a_711_);
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
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec(v_a_711_);
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
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec(v_a_711_);
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
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
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
lean_inc(v_a_895_);
lean_inc_ref(v_a_894_);
lean_inc(v_a_893_);
lean_inc_ref(v_a_892_);
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
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec_ref(v_paramInfo_903_);
return v___x_904_;
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
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
lean_object* v___x_943_; lean_object* v___x_128515__overap_944_; lean_object* v___x_945_; 
v___x_943_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0);
v___x_128515__overap_944_ = lean_panic_fn(v___x_943_, v_msg_931_);
v___x_945_ = lean_apply_11(v___x_128515__overap_944_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, lean_box(0));
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___boxed(lean_object* v_msg_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v_msg_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
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
v___x_992_ = lean_apply_12(v_k_979_, v_b_986_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, lean_box(0));
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0___boxed(lean_object* v_k_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v_b_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0(v_k_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v_b_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(lean_object* v_name_1007_, uint8_t v_bi_1008_, lean_object* v_type_1009_, lean_object* v_k_1010_, uint8_t v_kind_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___f_1023_; lean_object* v___x_1024_; 
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
lean_inc(v___y_1101_);
lean_inc_ref(v___y_1100_);
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
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
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec_ref(v___x_1111_);
return v___x_1113_;
}
else
{
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
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
uint8_t v___x_136449__boxed_1131_; uint8_t v___x_136450__boxed_1132_; lean_object* v_res_1133_; 
v___x_136449__boxed_1131_ = lean_unbox(v___x_1117_);
v___x_136450__boxed_1132_ = lean_unbox(v___x_1118_);
v_res_1133_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0(v_numArgs_1114_, v_rhs_1115_, v_lhs_1116_, v___x_136449__boxed_1131_, v___x_136450__boxed_1132_, v_x_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
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
v___x_1136_ = lean_panic_fn(v___x_1135_, v_msg_1134_);
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
v___x_1244_ = lean_unsigned_to_nat(34u);
v___x_1245_ = lean_unsigned_to_nat(154u);
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
v___x_1250_ = lean_unsigned_to_nat(36u);
v___x_1251_ = lean_unsigned_to_nat(153u);
v___x_1252_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0));
v___x_1253_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1254_ = l_mkPanicMessageWithDecl(v___x_1253_, v___x_1252_, v___x_1251_, v___x_1250_, v___x_1249_);
return v___x_1254_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1263_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__5));
v___x_1264_ = lean_unsigned_to_nat(4u);
v___x_1265_ = lean_unsigned_to_nat(155u);
v___x_1266_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0));
v___x_1267_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1268_ = l_mkPanicMessageWithDecl(v___x_1267_, v___x_1266_, v___x_1265_, v___x_1264_, v___x_1263_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof(lean_object* v_lhs_1274_, lean_object* v_rhs_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v_fileName_1313_; lean_object* v_fileMap_1314_; lean_object* v_options_1315_; lean_object* v_currRecDepth_1316_; lean_object* v_maxRecDepth_1317_; lean_object* v_ref_1318_; lean_object* v_currNamespace_1319_; lean_object* v_openDecls_1320_; lean_object* v_initHeartbeats_1321_; lean_object* v_maxHeartbeats_1322_; lean_object* v_quotContext_1323_; lean_object* v_currMacroScope_1324_; uint8_t v_diag_1325_; lean_object* v_cancelTk_x3f_1326_; uint8_t v_suppressElabErrors_1327_; lean_object* v_inheritedTraceOptions_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1402_; 
v_fileName_1313_ = lean_ctor_get(v_a_1284_, 0);
v_fileMap_1314_ = lean_ctor_get(v_a_1284_, 1);
v_options_1315_ = lean_ctor_get(v_a_1284_, 2);
v_currRecDepth_1316_ = lean_ctor_get(v_a_1284_, 3);
v_maxRecDepth_1317_ = lean_ctor_get(v_a_1284_, 4);
v_ref_1318_ = lean_ctor_get(v_a_1284_, 5);
v_currNamespace_1319_ = lean_ctor_get(v_a_1284_, 6);
v_openDecls_1320_ = lean_ctor_get(v_a_1284_, 7);
v_initHeartbeats_1321_ = lean_ctor_get(v_a_1284_, 8);
v_maxHeartbeats_1322_ = lean_ctor_get(v_a_1284_, 9);
v_quotContext_1323_ = lean_ctor_get(v_a_1284_, 10);
v_currMacroScope_1324_ = lean_ctor_get(v_a_1284_, 11);
v_diag_1325_ = lean_ctor_get_uint8(v_a_1284_, sizeof(void*)*14);
v_cancelTk_x3f_1326_ = lean_ctor_get(v_a_1284_, 12);
v_suppressElabErrors_1327_ = lean_ctor_get_uint8(v_a_1284_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1328_ = lean_ctor_get(v_a_1284_, 13);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_a_1284_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1330_ = v_a_1284_;
v_isShared_1331_ = v_isSharedCheck_1402_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_inheritedTraceOptions_1328_);
lean_inc(v_cancelTk_x3f_1326_);
lean_inc(v_currMacroScope_1324_);
lean_inc(v_quotContext_1323_);
lean_inc(v_maxHeartbeats_1322_);
lean_inc(v_initHeartbeats_1321_);
lean_inc(v_openDecls_1320_);
lean_inc(v_currNamespace_1319_);
lean_inc(v_ref_1318_);
lean_inc(v_maxRecDepth_1317_);
lean_inc(v_currRecDepth_1316_);
lean_inc(v_options_1315_);
lean_inc(v_fileMap_1314_);
lean_inc(v_fileName_1313_);
lean_dec(v_a_1284_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1402_;
goto v_resetjp_1329_;
}
v___jp_1287_:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1);
v___x_1299_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1298_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
return v___x_1299_;
}
v___jp_1300_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2);
v___x_1312_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1311_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
return v___x_1312_;
}
v_resetjp_1329_:
{
uint8_t v___x_1332_; 
v___x_1332_ = lean_nat_dec_eq(v_currRecDepth_1316_, v_maxRecDepth_1317_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; uint8_t v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1333_ = l_Lean_Expr_cleanupAnnotations(v_lhs_1274_);
v___x_1334_ = l_Lean_Expr_isApp(v___x_1333_);
v___x_1335_ = lean_unsigned_to_nat(1u);
v___x_1336_ = lean_nat_add(v_currRecDepth_1316_, v___x_1335_);
lean_dec(v_currRecDepth_1316_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 3, v___x_1336_);
v___x_1338_ = v___x_1330_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_fileName_1313_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_fileMap_1314_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v_options_1315_);
lean_ctor_set(v_reuseFailAlloc_1400_, 3, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1400_, 4, v_maxRecDepth_1317_);
lean_ctor_set(v_reuseFailAlloc_1400_, 5, v_ref_1318_);
lean_ctor_set(v_reuseFailAlloc_1400_, 6, v_currNamespace_1319_);
lean_ctor_set(v_reuseFailAlloc_1400_, 7, v_openDecls_1320_);
lean_ctor_set(v_reuseFailAlloc_1400_, 8, v_initHeartbeats_1321_);
lean_ctor_set(v_reuseFailAlloc_1400_, 9, v_maxHeartbeats_1322_);
lean_ctor_set(v_reuseFailAlloc_1400_, 10, v_quotContext_1323_);
lean_ctor_set(v_reuseFailAlloc_1400_, 11, v_currMacroScope_1324_);
lean_ctor_set(v_reuseFailAlloc_1400_, 12, v_cancelTk_x3f_1326_);
lean_ctor_set(v_reuseFailAlloc_1400_, 13, v_inheritedTraceOptions_1328_);
lean_ctor_set_uint8(v_reuseFailAlloc_1400_, sizeof(void*)*14, v_diag_1325_);
lean_ctor_set_uint8(v_reuseFailAlloc_1400_, sizeof(void*)*14 + 1, v_suppressElabErrors_1327_);
v___x_1338_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
if (v___x_1334_ == 0)
{
lean_dec_ref(v___x_1333_);
lean_dec_ref(v_rhs_1275_);
v___y_1301_ = v_a_1276_;
v___y_1302_ = v_a_1277_;
v___y_1303_ = v_a_1278_;
v___y_1304_ = v_a_1279_;
v___y_1305_ = v_a_1280_;
v___y_1306_ = v_a_1281_;
v___y_1307_ = v_a_1282_;
v___y_1308_ = v_a_1283_;
v___y_1309_ = v___x_1338_;
v___y_1310_ = v_a_1285_;
goto v___jp_1300_;
}
else
{
lean_object* v_arg_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v_arg_1339_ = lean_ctor_get(v___x_1333_, 1);
lean_inc_ref(v_arg_1339_);
v___x_1340_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1333_);
v___x_1341_ = l_Lean_Expr_isApp(v___x_1340_);
if (v___x_1341_ == 0)
{
lean_dec_ref(v___x_1340_);
lean_dec_ref(v_arg_1339_);
lean_dec_ref(v_rhs_1275_);
v___y_1301_ = v_a_1276_;
v___y_1302_ = v_a_1277_;
v___y_1303_ = v_a_1278_;
v___y_1304_ = v_a_1279_;
v___y_1305_ = v_a_1280_;
v___y_1306_ = v_a_1281_;
v___y_1307_ = v_a_1282_;
v___y_1308_ = v_a_1283_;
v___y_1309_ = v___x_1338_;
v___y_1310_ = v_a_1285_;
goto v___jp_1300_;
}
else
{
lean_object* v_arg_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v_arg_1342_ = lean_ctor_get(v___x_1340_, 1);
lean_inc_ref(v_arg_1342_);
v___x_1343_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1340_);
v___x_1344_ = l_Lean_Expr_isApp(v___x_1343_);
if (v___x_1344_ == 0)
{
lean_dec_ref(v___x_1343_);
lean_dec_ref(v_arg_1342_);
lean_dec_ref(v_arg_1339_);
lean_dec_ref(v_rhs_1275_);
v___y_1301_ = v_a_1276_;
v___y_1302_ = v_a_1277_;
v___y_1303_ = v_a_1278_;
v___y_1304_ = v_a_1279_;
v___y_1305_ = v_a_1280_;
v___y_1306_ = v_a_1281_;
v___y_1307_ = v_a_1282_;
v___y_1308_ = v_a_1283_;
v___y_1309_ = v___x_1338_;
v___y_1310_ = v_a_1285_;
goto v___jp_1300_;
}
else
{
lean_object* v_arg_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v_arg_1345_ = lean_ctor_get(v___x_1343_, 1);
lean_inc_ref(v_arg_1345_);
v___x_1346_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1343_);
v___x_1347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_1348_ = l_Lean_Expr_isConstOf(v___x_1346_, v___x_1347_);
if (v___x_1348_ == 0)
{
lean_dec_ref(v___x_1346_);
lean_dec_ref(v_arg_1345_);
lean_dec_ref(v_arg_1342_);
lean_dec_ref(v_arg_1339_);
lean_dec_ref(v_rhs_1275_);
v___y_1301_ = v_a_1276_;
v___y_1302_ = v_a_1277_;
v___y_1303_ = v_a_1278_;
v___y_1304_ = v_a_1279_;
v___y_1305_ = v_a_1280_;
v___y_1306_ = v_a_1281_;
v___y_1307_ = v_a_1282_;
v___y_1308_ = v_a_1283_;
v___y_1309_ = v___x_1338_;
v___y_1310_ = v_a_1285_;
goto v___jp_1300_;
}
else
{
lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1349_ = l_Lean_Expr_cleanupAnnotations(v_rhs_1275_);
v___x_1350_ = l_Lean_Expr_isApp(v___x_1349_);
if (v___x_1350_ == 0)
{
lean_dec_ref(v___x_1349_);
lean_dec_ref(v___x_1346_);
lean_dec_ref(v_arg_1345_);
lean_dec_ref(v_arg_1342_);
lean_dec_ref(v_arg_1339_);
v___y_1288_ = v_a_1276_;
v___y_1289_ = v_a_1277_;
v___y_1290_ = v_a_1278_;
v___y_1291_ = v_a_1279_;
v___y_1292_ = v_a_1280_;
v___y_1293_ = v_a_1281_;
v___y_1294_ = v_a_1282_;
v___y_1295_ = v_a_1283_;
v___y_1296_ = v___x_1338_;
v___y_1297_ = v_a_1285_;
goto v___jp_1287_;
}
else
{
lean_object* v_arg_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v_arg_1351_ = lean_ctor_get(v___x_1349_, 1);
lean_inc_ref(v_arg_1351_);
v___x_1352_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1349_);
v___x_1353_ = l_Lean_Expr_isApp(v___x_1352_);
if (v___x_1353_ == 0)
{
lean_dec_ref(v___x_1352_);
lean_dec_ref(v_arg_1351_);
lean_dec_ref(v___x_1346_);
lean_dec_ref(v_arg_1345_);
lean_dec_ref(v_arg_1342_);
lean_dec_ref(v_arg_1339_);
v___y_1288_ = v_a_1276_;
v___y_1289_ = v_a_1277_;
v___y_1290_ = v_a_1278_;
v___y_1291_ = v_a_1279_;
v___y_1292_ = v_a_1280_;
v___y_1293_ = v_a_1281_;
v___y_1294_ = v_a_1282_;
v___y_1295_ = v_a_1283_;
v___y_1296_ = v___x_1338_;
v___y_1297_ = v_a_1285_;
goto v___jp_1287_;
}
else
{
lean_object* v_arg_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; 
v_arg_1354_ = lean_ctor_get(v___x_1352_, 1);
lean_inc_ref(v_arg_1354_);
v___x_1355_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1352_);
v___x_1356_ = l_Lean_Expr_isApp(v___x_1355_);
if (v___x_1356_ == 0)
{
lean_dec_ref(v___x_1355_);
lean_dec_ref(v_arg_1354_);
lean_dec_ref(v_arg_1351_);
lean_dec_ref(v___x_1346_);
lean_dec_ref(v_arg_1345_);
lean_dec_ref(v_arg_1342_);
lean_dec_ref(v_arg_1339_);
v___y_1288_ = v_a_1276_;
v___y_1289_ = v_a_1277_;
v___y_1290_ = v_a_1278_;
v___y_1291_ = v_a_1279_;
v___y_1292_ = v_a_1280_;
v___y_1293_ = v_a_1281_;
v___y_1294_ = v_a_1282_;
v___y_1295_ = v_a_1283_;
v___y_1296_ = v___x_1338_;
v___y_1297_ = v_a_1285_;
goto v___jp_1287_;
}
else
{
lean_object* v_arg_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v_arg_1357_ = lean_ctor_get(v___x_1355_, 1);
lean_inc_ref(v_arg_1357_);
v___x_1358_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1355_);
v___x_1359_ = l_Lean_Expr_isConstOf(v___x_1358_, v___x_1347_);
lean_dec_ref(v___x_1358_);
if (v___x_1359_ == 0)
{
lean_dec_ref(v_arg_1357_);
lean_dec_ref(v_arg_1354_);
lean_dec_ref(v_arg_1351_);
lean_dec_ref(v___x_1346_);
lean_dec_ref(v_arg_1345_);
lean_dec_ref(v_arg_1342_);
lean_dec_ref(v_arg_1339_);
v___y_1288_ = v_a_1276_;
v___y_1289_ = v_a_1277_;
v___y_1290_ = v_a_1278_;
v___y_1291_ = v_a_1279_;
v___y_1292_ = v_a_1280_;
v___y_1293_ = v_a_1281_;
v___y_1294_ = v_a_1282_;
v___y_1295_ = v_a_1283_;
v___y_1296_ = v___x_1338_;
v___y_1297_ = v_a_1285_;
goto v___jp_1287_;
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___y_1363_; uint8_t v___y_1379_; uint8_t v___x_1398_; 
v___x_1360_ = lean_st_ref_get(v_a_1276_);
v___x_1361_ = lean_st_ref_get(v_a_1276_);
v___x_1398_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1360_, v_arg_1342_, v_arg_1351_);
if (v___x_1398_ == 0)
{
lean_dec(v___x_1361_);
v___y_1379_ = v___x_1398_;
goto v___jp_1378_;
}
else
{
uint8_t v___x_1399_; 
v___x_1399_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1361_, v_arg_1339_, v_arg_1354_);
v___y_1379_ = v___x_1399_;
goto v___jp_1378_;
}
v___jp_1362_:
{
lean_object* v___x_1364_; 
lean_inc(v_a_1285_);
lean_inc_ref(v___x_1338_);
lean_inc(v_a_1283_);
lean_inc_ref(v_a_1282_);
lean_inc(v_a_1281_);
lean_inc_ref(v_a_1280_);
lean_inc(v_a_1279_);
lean_inc_ref(v_a_1278_);
lean_inc(v_a_1277_);
lean_inc(v_a_1276_);
lean_inc_ref(v_arg_1351_);
lean_inc_ref(v_arg_1342_);
v___x_1364_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1342_, v_arg_1351_, v___x_1359_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v___x_1338_, v_a_1285_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1366_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref(v___x_1364_);
lean_inc_ref(v_arg_1354_);
lean_inc_ref(v_arg_1339_);
v___x_1366_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1339_, v_arg_1354_, v___x_1359_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v___x_1338_, v_a_1285_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1377_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1369_ = v___x_1366_;
v_isShared_1370_ = v_isSharedCheck_1377_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1366_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1377_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1371_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4));
v___x_1372_ = l_Lean_mkConst(v___x_1371_, v___y_1363_);
v___x_1373_ = l_Lean_mkApp8(v___x_1372_, v_arg_1345_, v_arg_1357_, v_arg_1342_, v_arg_1339_, v_arg_1354_, v_arg_1351_, v_a_1365_, v_a_1367_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1373_);
v___x_1375_ = v___x_1369_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
else
{
lean_dec(v_a_1365_);
lean_dec(v___y_1363_);
lean_dec_ref(v_arg_1357_);
lean_dec_ref(v_arg_1354_);
lean_dec_ref(v_arg_1351_);
lean_dec_ref(v_arg_1345_);
lean_dec_ref(v_arg_1342_);
lean_dec_ref(v_arg_1339_);
return v___x_1366_;
}
}
else
{
lean_dec(v___y_1363_);
lean_dec_ref(v_arg_1357_);
lean_dec_ref(v_arg_1354_);
lean_dec_ref(v_arg_1351_);
lean_dec_ref(v_arg_1345_);
lean_dec_ref(v_arg_1342_);
lean_dec_ref(v_arg_1339_);
lean_dec_ref(v___x_1338_);
lean_dec(v_a_1285_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec(v_a_1276_);
return v___x_1364_;
}
}
v___jp_1378_:
{
if (v___y_1379_ == 0)
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
lean_dec_ref(v_arg_1357_);
lean_dec_ref(v_arg_1354_);
lean_dec_ref(v_arg_1351_);
lean_dec_ref(v___x_1346_);
lean_dec_ref(v_arg_1345_);
lean_dec_ref(v_arg_1342_);
lean_dec_ref(v_arg_1339_);
v___x_1380_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6);
v___x_1381_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1380_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v___x_1338_, v_a_1285_);
return v___x_1381_;
}
else
{
lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1382_ = l_Lean_Expr_constLevels_x21(v___x_1346_);
lean_dec_ref(v___x_1346_);
v___x_1383_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1345_, v_arg_1357_);
if (v___x_1383_ == 0)
{
v___y_1363_ = v___x_1382_;
goto v___jp_1362_;
}
else
{
if (v___x_1332_ == 0)
{
lean_object* v___x_1384_; 
lean_dec_ref(v_arg_1357_);
lean_inc(v_a_1285_);
lean_inc_ref(v___x_1338_);
lean_inc(v_a_1283_);
lean_inc_ref(v_a_1282_);
lean_inc(v_a_1281_);
lean_inc_ref(v_a_1280_);
lean_inc(v_a_1279_);
lean_inc_ref(v_a_1278_);
lean_inc(v_a_1277_);
lean_inc(v_a_1276_);
lean_inc_ref(v_arg_1351_);
lean_inc_ref(v_arg_1342_);
v___x_1384_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1342_, v_arg_1351_, v___x_1332_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v___x_1338_, v_a_1285_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref(v___x_1384_);
lean_inc_ref(v_arg_1354_);
lean_inc_ref(v_arg_1339_);
v___x_1386_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1339_, v_arg_1354_, v___x_1332_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v___x_1338_, v_a_1285_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1397_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1397_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1397_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1391_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8));
v___x_1392_ = l_Lean_mkConst(v___x_1391_, v___x_1382_);
v___x_1393_ = l_Lean_mkApp7(v___x_1392_, v_arg_1345_, v_arg_1342_, v_arg_1339_, v_arg_1354_, v_arg_1351_, v_a_1385_, v_a_1387_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1393_);
v___x_1395_ = v___x_1389_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
else
{
lean_dec(v_a_1385_);
lean_dec(v___x_1382_);
lean_dec_ref(v_arg_1354_);
lean_dec_ref(v_arg_1351_);
lean_dec_ref(v_arg_1345_);
lean_dec_ref(v_arg_1342_);
lean_dec_ref(v_arg_1339_);
return v___x_1386_;
}
}
else
{
lean_dec(v___x_1382_);
lean_dec_ref(v_arg_1354_);
lean_dec_ref(v_arg_1351_);
lean_dec_ref(v_arg_1345_);
lean_dec_ref(v_arg_1342_);
lean_dec_ref(v_arg_1339_);
lean_dec_ref(v___x_1338_);
lean_dec(v_a_1285_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec(v_a_1276_);
return v___x_1384_;
}
}
else
{
v___y_1363_ = v___x_1382_;
goto v___jp_1362_;
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
lean_object* v___x_1401_; 
lean_del_object(v___x_1330_);
lean_dec_ref(v_inheritedTraceOptions_1328_);
lean_dec(v_cancelTk_x3f_1326_);
lean_dec(v_currMacroScope_1324_);
lean_dec(v_quotContext_1323_);
lean_dec(v_maxHeartbeats_1322_);
lean_dec(v_initHeartbeats_1321_);
lean_dec(v_openDecls_1320_);
lean_dec(v_currNamespace_1319_);
lean_dec(v_maxRecDepth_1317_);
lean_dec(v_currRecDepth_1316_);
lean_dec_ref(v_options_1315_);
lean_dec_ref(v_fileMap_1314_);
lean_dec_ref(v_fileName_1313_);
lean_dec(v_a_1285_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec_ref(v_rhs_1275_);
lean_dec_ref(v_lhs_1274_);
v___x_1401_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1318_);
return v___x_1401_;
}
}
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2(void){
_start:
{
uint8_t v___x_1406_; uint64_t v___x_1407_; 
v___x_1406_ = 1;
v___x_1407_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1406_);
return v___x_1407_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4(void){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1409_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_1410_ = lean_unsigned_to_nat(38u);
v___x_1411_ = lean_unsigned_to_nat(250u);
v___x_1412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3));
v___x_1413_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1414_ = l_mkPanicMessageWithDecl(v___x_1413_, v___x_1412_, v___x_1411_, v___x_1410_, v___x_1409_);
return v___x_1414_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5));
v___x_1417_ = lean_unsigned_to_nat(6u);
v___x_1418_ = lean_unsigned_to_nat(260u);
v___x_1419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3));
v___x_1420_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1421_ = l_mkPanicMessageWithDecl(v___x_1420_, v___x_1419_, v___x_1418_, v___x_1417_, v___x_1416_);
return v___x_1421_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2(void){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1424_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__1));
v___x_1425_ = lean_unsigned_to_nat(4u);
v___x_1426_ = lean_unsigned_to_nat(219u);
v___x_1427_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__0));
v___x_1428_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1429_ = l_mkPanicMessageWithDecl(v___x_1428_, v___x_1427_, v___x_1426_, v___x_1425_, v___x_1424_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(lean_object* v_lhs_1430_, lean_object* v_rhs_1431_, uint8_t v_heq_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_numArgs_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v_numArgs_1444_ = l_Lean_Expr_getAppNumArgs(v_lhs_1430_);
v___x_1445_ = l_Lean_Expr_getAppNumArgs(v_rhs_1431_);
v___x_1446_ = lean_nat_dec_eq(v___x_1445_, v_numArgs_1444_);
lean_dec(v___x_1445_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec(v_numArgs_1444_);
lean_dec_ref(v_rhs_1431_);
lean_dec_ref(v_lhs_1430_);
v___x_1447_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2);
v___x_1448_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1447_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
return v___x_1448_;
}
else
{
lean_object* v_f_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v_f_1449_ = l_Lean_Expr_getAppFn(v_lhs_1430_);
v___x_1450_ = lean_box(0);
lean_inc(v_a_1442_);
lean_inc_ref(v_a_1441_);
lean_inc(v_a_1440_);
lean_inc_ref(v_a_1439_);
lean_inc_ref(v_f_1449_);
v___x_1451_ = l_Lean_Meta_getFunInfo(v_f_1449_, v___x_1450_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref(v___x_1451_);
v___x_1453_ = l_Lean_Meta_FunInfo_getArity(v_a_1452_);
lean_dec(v_a_1452_);
v___x_1454_ = lean_nat_dec_lt(v___x_1453_, v_numArgs_1444_);
lean_dec(v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v_g_1455_; lean_object* v___x_1456_; 
v_g_1455_ = l_Lean_Expr_getAppFn(v_rhs_1431_);
v___x_1456_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_1449_, v_g_1455_, v_numArgs_1444_, v_lhs_1430_, v_rhs_1431_, v_heq_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
return v___x_1456_;
}
else
{
lean_object* v___x_1457_; 
lean_dec_ref(v_f_1449_);
lean_dec(v_numArgs_1444_);
lean_inc_ref(v_lhs_1430_);
v___x_1457_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(v_lhs_1430_, v_rhs_1431_);
if (lean_obj_tag(v___x_1457_) == 1)
{
lean_object* v_val_1458_; lean_object* v_fst_1459_; lean_object* v_snd_1460_; lean_object* v___y_1462_; lean_object* v___x_1475_; 
v_val_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_val_1458_);
lean_dec_ref(v___x_1457_);
v_fst_1459_ = lean_ctor_get(v_val_1458_, 0);
lean_inc(v_fst_1459_);
v_snd_1460_ = lean_ctor_get(v_val_1458_, 1);
lean_inc(v_snd_1460_);
lean_dec(v_val_1458_);
lean_inc(v_a_1442_);
lean_inc_ref(v_a_1441_);
lean_inc(v_a_1440_);
lean_inc_ref(v_a_1439_);
lean_inc(v_snd_1460_);
v___x_1475_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(v_fst_1459_, v_snd_1460_, v_a_1436_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
if (lean_obj_tag(v___x_1475_) == 0)
{
v___y_1462_ = v___x_1475_;
goto v___jp_1461_;
}
else
{
lean_object* v_a_1476_; uint8_t v___y_1478_; uint8_t v___x_1480_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
v___x_1480_ = l_Lean_Exception_isInterrupt(v_a_1476_);
if (v___x_1480_ == 0)
{
uint8_t v___x_1481_; 
v___x_1481_ = l_Lean_Exception_isRuntime(v_a_1476_);
v___y_1478_ = v___x_1481_;
goto v___jp_1477_;
}
else
{
lean_dec(v_a_1476_);
v___y_1478_ = v___x_1480_;
goto v___jp_1477_;
}
v___jp_1477_:
{
if (v___y_1478_ == 0)
{
lean_object* v___x_1479_; 
lean_dec_ref(v___x_1475_);
lean_inc_ref(v_rhs_1431_);
lean_inc_ref(v_lhs_1430_);
v___x_1479_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1430_, v_rhs_1431_, lean_box(0), v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
v___y_1462_ = v___x_1479_;
goto v___jp_1461_;
}
else
{
v___y_1462_ = v___x_1475_;
goto v___jp_1461_;
}
}
}
v___jp_1461_:
{
if (lean_obj_tag(v___y_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1464_; 
v_a_1463_ = lean_ctor_get(v___y_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref(v___y_1462_);
lean_inc(v_a_1442_);
lean_inc_ref(v_a_1441_);
lean_inc(v_a_1440_);
lean_inc_ref(v_a_1439_);
v___x_1464_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_1463_, v_lhs_1430_, v_rhs_1431_, v_snd_1460_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
lean_dec(v_snd_1460_);
lean_dec_ref(v_rhs_1431_);
lean_dec_ref(v_lhs_1430_);
lean_dec(v_a_1463_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v___x_1466_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1465_);
lean_dec_ref(v___x_1464_);
v___x_1466_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_1465_, v_heq_1432_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
return v___x_1466_;
}
else
{
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
return v___x_1464_;
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec(v_snd_1460_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec(v_a_1433_);
lean_dec_ref(v_rhs_1431_);
lean_dec_ref(v_lhs_1430_);
v_a_1467_ = lean_ctor_get(v___y_1462_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___y_1462_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___y_1462_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___y_1462_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
else
{
lean_object* v___x_1482_; 
lean_dec(v___x_1457_);
v___x_1482_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1430_, v_rhs_1431_, lean_box(0), v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec(v_a_1433_);
return v___x_1482_;
}
}
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec_ref(v_f_1449_);
lean_dec(v_numArgs_1444_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec(v_a_1433_);
lean_dec_ref(v_rhs_1431_);
lean_dec_ref(v_lhs_1430_);
v_a_1483_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1451_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1451_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(lean_object* v_lhs_1491_, lean_object* v_rhs_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
uint8_t v___x_1504_; 
v___x_1504_ = l_Lean_Expr_isApp(v_lhs_1491_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec(v_a_1493_);
v___x_1505_ = lean_box(0);
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
return v___x_1506_;
}
else
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = l_Lean_Expr_appFn_x21(v_lhs_1491_);
v___x_1508_ = l_Lean_Expr_appFn_x21(v_rhs_1492_);
lean_inc(v_a_1502_);
lean_inc_ref(v_a_1501_);
lean_inc(v_a_1500_);
lean_inc_ref(v_a_1499_);
lean_inc(v_a_1498_);
lean_inc_ref(v_a_1497_);
lean_inc(v_a_1496_);
lean_inc_ref(v_a_1495_);
lean_inc(v_a_1494_);
lean_inc(v_a_1493_);
v___x_1509_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v___x_1507_, v___x_1508_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
lean_dec_ref(v___x_1508_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1605_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1512_ = v___x_1509_;
v_isShared_1513_ = v_isSharedCheck_1605_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1605_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v_a_u2081_1514_; lean_object* v_a_u2082_1515_; 
v_a_u2081_1514_ = l_Lean_Expr_appArg_x21(v_lhs_1491_);
v_a_u2082_1515_ = l_Lean_Expr_appArg_x21(v_rhs_1492_);
if (lean_obj_tag(v_a_1510_) == 1)
{
lean_object* v_val_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1571_; 
lean_del_object(v___x_1512_);
lean_dec_ref(v___x_1507_);
v_val_1516_ = lean_ctor_get(v_a_1510_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_a_1510_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1518_ = v_a_1510_;
v_isShared_1519_ = v_isSharedCheck_1571_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_val_1516_);
lean_dec(v_a_1510_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1571_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
uint8_t v___x_1520_; 
v___x_1520_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_u2081_1514_, v_a_u2082_1515_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; 
lean_inc(v_a_1502_);
lean_inc_ref(v_a_1501_);
lean_inc(v_a_1500_);
lean_inc_ref(v_a_1499_);
v___x_1521_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_1514_, v_a_u2082_1515_, v___x_1520_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1523_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref(v___x_1521_);
v___x_1523_ = l_Lean_Meta_mkCongr(v_val_1516_, v_a_1522_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1534_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1526_ = v___x_1523_;
v_isShared_1527_ = v_isSharedCheck_1534_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1523_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1534_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v_a_1524_);
v___x_1529_ = v___x_1518_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1531_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1529_);
v___x_1531_ = v___x_1526_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
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
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_del_object(v___x_1518_);
v_a_1535_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1523_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1523_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_del_object(v___x_1518_);
lean_dec(v_val_1516_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
v_a_1543_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1521_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1521_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
else
{
lean_object* v___x_1551_; 
lean_dec_ref(v_a_u2082_1515_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec(v_a_1493_);
v___x_1551_ = l_Lean_Meta_mkCongrFun(v_val_1516_, v_a_u2081_1514_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1562_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1554_ = v___x_1551_;
v_isShared_1555_ = v_isSharedCheck_1562_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1551_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1562_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v_a_1552_);
v___x_1557_ = v___x_1518_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1559_; 
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v___x_1557_);
v___x_1559_ = v___x_1554_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_del_object(v___x_1518_);
v_a_1563_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1551_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1551_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
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
}
}
else
{
uint8_t v___x_1572_; 
lean_dec(v_a_1510_);
v___x_1572_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_u2081_1514_, v_a_u2082_1515_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1573_; 
lean_del_object(v___x_1512_);
lean_inc(v_a_1502_);
lean_inc_ref(v_a_1501_);
lean_inc(v_a_1500_);
lean_inc_ref(v_a_1499_);
v___x_1573_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_1514_, v_a_u2082_1515_, v___x_1572_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1575_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref(v___x_1573_);
v___x_1575_ = l_Lean_Meta_mkCongrArg(v___x_1507_, v_a_1574_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1584_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1578_ = v___x_1575_;
v_isShared_1579_ = v_isSharedCheck_1584_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1575_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1584_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; lean_object* v___x_1582_; 
v___x_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1580_, 0, v_a_1576_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v___x_1580_);
v___x_1582_ = v___x_1578_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
v_a_1585_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1575_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1575_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec_ref(v___x_1507_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
v_a_1593_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1573_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1573_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
else
{
lean_object* v___x_1601_; lean_object* v___x_1603_; 
lean_dec_ref(v_a_u2082_1515_);
lean_dec_ref(v_a_u2081_1514_);
lean_dec_ref(v___x_1507_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec(v_a_1493_);
v___x_1601_ = lean_box(0);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v___x_1601_);
v___x_1603_ = v___x_1512_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1601_);
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
else
{
lean_dec_ref(v___x_1507_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec(v_a_1493_);
return v___x_1509_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__2));
v___x_1610_ = lean_unsigned_to_nat(14u);
v___x_1611_ = lean_unsigned_to_nat(22u);
v___x_1612_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__1));
v___x_1613_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__0));
v___x_1614_ = l_mkPanicMessageWithDecl(v___x_1613_, v___x_1612_, v___x_1611_, v___x_1610_, v___x_1609_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(lean_object* v_lhs_1615_, lean_object* v_rhs_1616_, uint8_t v_heq_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_){
_start:
{
lean_object* v___x_1629_; 
lean_inc(v_a_1627_);
lean_inc_ref(v_a_1626_);
lean_inc(v_a_1625_);
lean_inc_ref(v_a_1624_);
v___x_1629_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_1615_, v_rhs_1616_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1643_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1632_ = v___x_1629_;
v_isShared_1633_ = v_isSharedCheck_1643_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1629_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1643_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___y_1635_; 
if (lean_obj_tag(v_a_1630_) == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3);
v___x_1641_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_spec__13(v___x_1640_);
v___y_1635_ = v___x_1641_;
goto v___jp_1634_;
}
else
{
lean_object* v_val_1642_; 
v_val_1642_ = lean_ctor_get(v_a_1630_, 0);
lean_inc(v_val_1642_);
lean_dec_ref(v_a_1630_);
v___y_1635_ = v_val_1642_;
goto v___jp_1634_;
}
v___jp_1634_:
{
if (v_heq_1617_ == 0)
{
lean_object* v___x_1637_; 
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v___y_1635_);
v___x_1637_ = v___x_1632_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___y_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
else
{
lean_object* v___x_1639_; 
lean_del_object(v___x_1632_);
v___x_1639_ = l_Lean_Meta_mkHEqOfEq(v___y_1635_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_);
return v___x_1639_;
}
}
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
v_a_1644_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1629_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1629_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__1(void){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1653_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_1654_ = lean_unsigned_to_nat(34u);
v___x_1655_ = lean_unsigned_to_nat(144u);
v___x_1656_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1657_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1658_ = l_mkPanicMessageWithDecl(v___x_1657_, v___x_1656_, v___x_1655_, v___x_1654_, v___x_1653_);
return v___x_1658_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__2(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1659_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_1660_ = lean_unsigned_to_nat(36u);
v___x_1661_ = lean_unsigned_to_nat(143u);
v___x_1662_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1663_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1664_ = l_mkPanicMessageWithDecl(v___x_1663_, v___x_1662_, v___x_1661_, v___x_1660_, v___x_1659_);
return v___x_1664_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__6(void){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1671_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__5));
v___x_1672_ = lean_unsigned_to_nat(4u);
v___x_1673_ = lean_unsigned_to_nat(145u);
v___x_1674_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1675_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1676_ = l_mkPanicMessageWithDecl(v___x_1675_, v___x_1674_, v___x_1673_, v___x_1672_, v___x_1671_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrProof(lean_object* v_lhs_1682_, lean_object* v_rhs_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v_fileName_1721_; lean_object* v_fileMap_1722_; lean_object* v_options_1723_; lean_object* v_currRecDepth_1724_; lean_object* v_maxRecDepth_1725_; lean_object* v_ref_1726_; lean_object* v_currNamespace_1727_; lean_object* v_openDecls_1728_; lean_object* v_initHeartbeats_1729_; lean_object* v_maxHeartbeats_1730_; lean_object* v_quotContext_1731_; lean_object* v_currMacroScope_1732_; uint8_t v_diag_1733_; lean_object* v_cancelTk_x3f_1734_; uint8_t v_suppressElabErrors_1735_; lean_object* v_inheritedTraceOptions_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1810_; 
v_fileName_1721_ = lean_ctor_get(v_a_1692_, 0);
v_fileMap_1722_ = lean_ctor_get(v_a_1692_, 1);
v_options_1723_ = lean_ctor_get(v_a_1692_, 2);
v_currRecDepth_1724_ = lean_ctor_get(v_a_1692_, 3);
v_maxRecDepth_1725_ = lean_ctor_get(v_a_1692_, 4);
v_ref_1726_ = lean_ctor_get(v_a_1692_, 5);
v_currNamespace_1727_ = lean_ctor_get(v_a_1692_, 6);
v_openDecls_1728_ = lean_ctor_get(v_a_1692_, 7);
v_initHeartbeats_1729_ = lean_ctor_get(v_a_1692_, 8);
v_maxHeartbeats_1730_ = lean_ctor_get(v_a_1692_, 9);
v_quotContext_1731_ = lean_ctor_get(v_a_1692_, 10);
v_currMacroScope_1732_ = lean_ctor_get(v_a_1692_, 11);
v_diag_1733_ = lean_ctor_get_uint8(v_a_1692_, sizeof(void*)*14);
v_cancelTk_x3f_1734_ = lean_ctor_get(v_a_1692_, 12);
v_suppressElabErrors_1735_ = lean_ctor_get_uint8(v_a_1692_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1736_ = lean_ctor_get(v_a_1692_, 13);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_a_1692_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1738_ = v_a_1692_;
v_isShared_1739_ = v_isSharedCheck_1810_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_inheritedTraceOptions_1736_);
lean_inc(v_cancelTk_x3f_1734_);
lean_inc(v_currMacroScope_1732_);
lean_inc(v_quotContext_1731_);
lean_inc(v_maxHeartbeats_1730_);
lean_inc(v_initHeartbeats_1729_);
lean_inc(v_openDecls_1728_);
lean_inc(v_currNamespace_1727_);
lean_inc(v_ref_1726_);
lean_inc(v_maxRecDepth_1725_);
lean_inc(v_currRecDepth_1724_);
lean_inc(v_options_1723_);
lean_inc(v_fileMap_1722_);
lean_inc(v_fileName_1721_);
lean_dec(v_a_1692_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1810_;
goto v_resetjp_1737_;
}
v___jp_1695_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__1, &l_Lean_Meta_Grind_mkEqCongrProof___closed__1_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__1);
v___x_1707_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1706_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
return v___x_1707_;
}
v___jp_1708_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__2, &l_Lean_Meta_Grind_mkEqCongrProof___closed__2_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__2);
v___x_1720_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1719_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
return v___x_1720_;
}
v_resetjp_1737_:
{
uint8_t v___x_1740_; 
v___x_1740_ = lean_nat_dec_eq(v_currRecDepth_1724_, v_maxRecDepth_1725_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; uint8_t v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1746_; 
v___x_1741_ = l_Lean_Expr_cleanupAnnotations(v_lhs_1682_);
v___x_1742_ = l_Lean_Expr_isApp(v___x_1741_);
v___x_1743_ = lean_unsigned_to_nat(1u);
v___x_1744_ = lean_nat_add(v_currRecDepth_1724_, v___x_1743_);
lean_dec(v_currRecDepth_1724_);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 3, v___x_1744_);
v___x_1746_ = v___x_1738_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_fileName_1721_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_fileMap_1722_);
lean_ctor_set(v_reuseFailAlloc_1808_, 2, v_options_1723_);
lean_ctor_set(v_reuseFailAlloc_1808_, 3, v___x_1744_);
lean_ctor_set(v_reuseFailAlloc_1808_, 4, v_maxRecDepth_1725_);
lean_ctor_set(v_reuseFailAlloc_1808_, 5, v_ref_1726_);
lean_ctor_set(v_reuseFailAlloc_1808_, 6, v_currNamespace_1727_);
lean_ctor_set(v_reuseFailAlloc_1808_, 7, v_openDecls_1728_);
lean_ctor_set(v_reuseFailAlloc_1808_, 8, v_initHeartbeats_1729_);
lean_ctor_set(v_reuseFailAlloc_1808_, 9, v_maxHeartbeats_1730_);
lean_ctor_set(v_reuseFailAlloc_1808_, 10, v_quotContext_1731_);
lean_ctor_set(v_reuseFailAlloc_1808_, 11, v_currMacroScope_1732_);
lean_ctor_set(v_reuseFailAlloc_1808_, 12, v_cancelTk_x3f_1734_);
lean_ctor_set(v_reuseFailAlloc_1808_, 13, v_inheritedTraceOptions_1736_);
lean_ctor_set_uint8(v_reuseFailAlloc_1808_, sizeof(void*)*14, v_diag_1733_);
lean_ctor_set_uint8(v_reuseFailAlloc_1808_, sizeof(void*)*14 + 1, v_suppressElabErrors_1735_);
v___x_1746_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
if (v___x_1742_ == 0)
{
lean_dec_ref(v___x_1741_);
lean_dec_ref(v_rhs_1683_);
v___y_1709_ = v_a_1684_;
v___y_1710_ = v_a_1685_;
v___y_1711_ = v_a_1686_;
v___y_1712_ = v_a_1687_;
v___y_1713_ = v_a_1688_;
v___y_1714_ = v_a_1689_;
v___y_1715_ = v_a_1690_;
v___y_1716_ = v_a_1691_;
v___y_1717_ = v___x_1746_;
v___y_1718_ = v_a_1693_;
goto v___jp_1708_;
}
else
{
lean_object* v_arg_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v_arg_1747_ = lean_ctor_get(v___x_1741_, 1);
lean_inc_ref(v_arg_1747_);
v___x_1748_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1741_);
v___x_1749_ = l_Lean_Expr_isApp(v___x_1748_);
if (v___x_1749_ == 0)
{
lean_dec_ref(v___x_1748_);
lean_dec_ref(v_arg_1747_);
lean_dec_ref(v_rhs_1683_);
v___y_1709_ = v_a_1684_;
v___y_1710_ = v_a_1685_;
v___y_1711_ = v_a_1686_;
v___y_1712_ = v_a_1687_;
v___y_1713_ = v_a_1688_;
v___y_1714_ = v_a_1689_;
v___y_1715_ = v_a_1690_;
v___y_1716_ = v_a_1691_;
v___y_1717_ = v___x_1746_;
v___y_1718_ = v_a_1693_;
goto v___jp_1708_;
}
else
{
lean_object* v_arg_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; 
v_arg_1750_ = lean_ctor_get(v___x_1748_, 1);
lean_inc_ref(v_arg_1750_);
v___x_1751_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1748_);
v___x_1752_ = l_Lean_Expr_isApp(v___x_1751_);
if (v___x_1752_ == 0)
{
lean_dec_ref(v___x_1751_);
lean_dec_ref(v_arg_1750_);
lean_dec_ref(v_arg_1747_);
lean_dec_ref(v_rhs_1683_);
v___y_1709_ = v_a_1684_;
v___y_1710_ = v_a_1685_;
v___y_1711_ = v_a_1686_;
v___y_1712_ = v_a_1687_;
v___y_1713_ = v_a_1688_;
v___y_1714_ = v_a_1689_;
v___y_1715_ = v_a_1690_;
v___y_1716_ = v_a_1691_;
v___y_1717_ = v___x_1746_;
v___y_1718_ = v_a_1693_;
goto v___jp_1708_;
}
else
{
lean_object* v_arg_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v_arg_1753_ = lean_ctor_get(v___x_1751_, 1);
lean_inc_ref(v_arg_1753_);
v___x_1754_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1751_);
v___x_1755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_1756_ = l_Lean_Expr_isConstOf(v___x_1754_, v___x_1755_);
if (v___x_1756_ == 0)
{
lean_dec_ref(v___x_1754_);
lean_dec_ref(v_arg_1753_);
lean_dec_ref(v_arg_1750_);
lean_dec_ref(v_arg_1747_);
lean_dec_ref(v_rhs_1683_);
v___y_1709_ = v_a_1684_;
v___y_1710_ = v_a_1685_;
v___y_1711_ = v_a_1686_;
v___y_1712_ = v_a_1687_;
v___y_1713_ = v_a_1688_;
v___y_1714_ = v_a_1689_;
v___y_1715_ = v_a_1690_;
v___y_1716_ = v_a_1691_;
v___y_1717_ = v___x_1746_;
v___y_1718_ = v_a_1693_;
goto v___jp_1708_;
}
else
{
lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1757_ = l_Lean_Expr_cleanupAnnotations(v_rhs_1683_);
v___x_1758_ = l_Lean_Expr_isApp(v___x_1757_);
if (v___x_1758_ == 0)
{
lean_dec_ref(v___x_1757_);
lean_dec_ref(v___x_1754_);
lean_dec_ref(v_arg_1753_);
lean_dec_ref(v_arg_1750_);
lean_dec_ref(v_arg_1747_);
v___y_1696_ = v_a_1684_;
v___y_1697_ = v_a_1685_;
v___y_1698_ = v_a_1686_;
v___y_1699_ = v_a_1687_;
v___y_1700_ = v_a_1688_;
v___y_1701_ = v_a_1689_;
v___y_1702_ = v_a_1690_;
v___y_1703_ = v_a_1691_;
v___y_1704_ = v___x_1746_;
v___y_1705_ = v_a_1693_;
goto v___jp_1695_;
}
else
{
lean_object* v_arg_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
v_arg_1759_ = lean_ctor_get(v___x_1757_, 1);
lean_inc_ref(v_arg_1759_);
v___x_1760_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1757_);
v___x_1761_ = l_Lean_Expr_isApp(v___x_1760_);
if (v___x_1761_ == 0)
{
lean_dec_ref(v___x_1760_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v___x_1754_);
lean_dec_ref(v_arg_1753_);
lean_dec_ref(v_arg_1750_);
lean_dec_ref(v_arg_1747_);
v___y_1696_ = v_a_1684_;
v___y_1697_ = v_a_1685_;
v___y_1698_ = v_a_1686_;
v___y_1699_ = v_a_1687_;
v___y_1700_ = v_a_1688_;
v___y_1701_ = v_a_1689_;
v___y_1702_ = v_a_1690_;
v___y_1703_ = v_a_1691_;
v___y_1704_ = v___x_1746_;
v___y_1705_ = v_a_1693_;
goto v___jp_1695_;
}
else
{
lean_object* v_arg_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v_arg_1762_ = lean_ctor_get(v___x_1760_, 1);
lean_inc_ref(v_arg_1762_);
v___x_1763_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1760_);
v___x_1764_ = l_Lean_Expr_isApp(v___x_1763_);
if (v___x_1764_ == 0)
{
lean_dec_ref(v___x_1763_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v___x_1754_);
lean_dec_ref(v_arg_1753_);
lean_dec_ref(v_arg_1750_);
lean_dec_ref(v_arg_1747_);
v___y_1696_ = v_a_1684_;
v___y_1697_ = v_a_1685_;
v___y_1698_ = v_a_1686_;
v___y_1699_ = v_a_1687_;
v___y_1700_ = v_a_1688_;
v___y_1701_ = v_a_1689_;
v___y_1702_ = v_a_1690_;
v___y_1703_ = v_a_1691_;
v___y_1704_ = v___x_1746_;
v___y_1705_ = v_a_1693_;
goto v___jp_1695_;
}
else
{
lean_object* v_arg_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; 
v_arg_1765_ = lean_ctor_get(v___x_1763_, 1);
lean_inc_ref(v_arg_1765_);
v___x_1766_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1763_);
v___x_1767_ = l_Lean_Expr_isConstOf(v___x_1766_, v___x_1755_);
lean_dec_ref(v___x_1766_);
if (v___x_1767_ == 0)
{
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v___x_1754_);
lean_dec_ref(v_arg_1753_);
lean_dec_ref(v_arg_1750_);
lean_dec_ref(v_arg_1747_);
v___y_1696_ = v_a_1684_;
v___y_1697_ = v_a_1685_;
v___y_1698_ = v_a_1686_;
v___y_1699_ = v_a_1687_;
v___y_1700_ = v_a_1688_;
v___y_1701_ = v_a_1689_;
v___y_1702_ = v_a_1690_;
v___y_1703_ = v_a_1691_;
v___y_1704_ = v___x_1746_;
v___y_1705_ = v_a_1693_;
goto v___jp_1695_;
}
else
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___y_1771_; uint8_t v___y_1787_; uint8_t v___x_1806_; 
v___x_1768_ = lean_st_ref_get(v_a_1684_);
v___x_1769_ = lean_st_ref_get(v_a_1684_);
v___x_1806_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1768_, v_arg_1750_, v_arg_1762_);
if (v___x_1806_ == 0)
{
lean_dec(v___x_1769_);
v___y_1787_ = v___x_1806_;
goto v___jp_1786_;
}
else
{
uint8_t v___x_1807_; 
v___x_1807_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1769_, v_arg_1747_, v_arg_1759_);
v___y_1787_ = v___x_1807_;
goto v___jp_1786_;
}
v___jp_1770_:
{
lean_object* v___x_1772_; 
lean_inc(v_a_1693_);
lean_inc_ref(v___x_1746_);
lean_inc(v_a_1691_);
lean_inc_ref(v_a_1690_);
lean_inc(v_a_1689_);
lean_inc_ref(v_a_1688_);
lean_inc(v_a_1687_);
lean_inc_ref(v_a_1686_);
lean_inc(v_a_1685_);
lean_inc(v_a_1684_);
lean_inc_ref(v_arg_1762_);
lean_inc_ref(v_arg_1750_);
v___x_1772_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1750_, v_arg_1762_, v___x_1767_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v___x_1746_, v_a_1693_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1774_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref(v___x_1772_);
lean_inc_ref(v_arg_1759_);
lean_inc_ref(v_arg_1747_);
v___x_1774_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1747_, v_arg_1759_, v___x_1767_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v___x_1746_, v_a_1693_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1785_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1777_ = v___x_1774_;
v_isShared_1778_ = v_isSharedCheck_1785_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1774_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1785_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1783_; 
v___x_1779_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__4));
v___x_1780_ = l_Lean_mkConst(v___x_1779_, v___y_1771_);
v___x_1781_ = l_Lean_mkApp8(v___x_1780_, v_arg_1753_, v_arg_1765_, v_arg_1750_, v_arg_1747_, v_arg_1762_, v_arg_1759_, v_a_1773_, v_a_1775_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1781_);
v___x_1783_ = v___x_1777_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
else
{
lean_dec(v_a_1773_);
lean_dec(v___y_1771_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1753_);
lean_dec_ref(v_arg_1750_);
lean_dec_ref(v_arg_1747_);
return v___x_1774_;
}
}
else
{
lean_dec(v___y_1771_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1753_);
lean_dec_ref(v_arg_1750_);
lean_dec_ref(v_arg_1747_);
lean_dec_ref(v___x_1746_);
lean_dec(v_a_1693_);
lean_dec(v_a_1691_);
lean_dec_ref(v_a_1690_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec(v_a_1684_);
return v___x_1772_;
}
}
v___jp_1786_:
{
if (v___y_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v___x_1754_);
lean_dec_ref(v_arg_1753_);
lean_dec_ref(v_arg_1750_);
lean_dec_ref(v_arg_1747_);
v___x_1788_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__6, &l_Lean_Meta_Grind_mkEqCongrProof___closed__6_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__6);
v___x_1789_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1788_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v___x_1746_, v_a_1693_);
return v___x_1789_;
}
else
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = l_Lean_Expr_constLevels_x21(v___x_1754_);
lean_dec_ref(v___x_1754_);
v___x_1791_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1753_, v_arg_1765_);
if (v___x_1791_ == 0)
{
v___y_1771_ = v___x_1790_;
goto v___jp_1770_;
}
else
{
if (v___x_1740_ == 0)
{
lean_object* v___x_1792_; 
lean_dec_ref(v_arg_1765_);
lean_inc(v_a_1693_);
lean_inc_ref(v___x_1746_);
lean_inc(v_a_1691_);
lean_inc_ref(v_a_1690_);
lean_inc(v_a_1689_);
lean_inc_ref(v_a_1688_);
lean_inc(v_a_1687_);
lean_inc_ref(v_a_1686_);
lean_inc(v_a_1685_);
lean_inc(v_a_1684_);
lean_inc_ref(v_arg_1762_);
lean_inc_ref(v_arg_1750_);
v___x_1792_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1750_, v_arg_1762_, v___x_1740_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v___x_1746_, v_a_1693_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v___x_1794_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref(v___x_1792_);
lean_inc_ref(v_arg_1759_);
lean_inc_ref(v_arg_1747_);
v___x_1794_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1747_, v_arg_1759_, v___x_1740_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v___x_1746_, v_a_1693_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1805_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1797_ = v___x_1794_;
v_isShared_1798_ = v_isSharedCheck_1805_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1794_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1805_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1799_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__8));
v___x_1800_ = l_Lean_mkConst(v___x_1799_, v___x_1790_);
v___x_1801_ = l_Lean_mkApp7(v___x_1800_, v_arg_1753_, v_arg_1750_, v_arg_1747_, v_arg_1762_, v_arg_1759_, v_a_1793_, v_a_1795_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___x_1801_);
v___x_1803_ = v___x_1797_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
else
{
lean_dec(v_a_1793_);
lean_dec(v___x_1790_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1753_);
lean_dec_ref(v_arg_1750_);
lean_dec_ref(v_arg_1747_);
return v___x_1794_;
}
}
else
{
lean_dec(v___x_1790_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1753_);
lean_dec_ref(v_arg_1750_);
lean_dec_ref(v_arg_1747_);
lean_dec_ref(v___x_1746_);
lean_dec(v_a_1693_);
lean_dec(v_a_1691_);
lean_dec_ref(v_a_1690_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec(v_a_1684_);
return v___x_1792_;
}
}
else
{
v___y_1771_ = v___x_1790_;
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
}
}
else
{
lean_object* v___x_1809_; 
lean_del_object(v___x_1738_);
lean_dec_ref(v_inheritedTraceOptions_1736_);
lean_dec(v_cancelTk_x3f_1734_);
lean_dec(v_currMacroScope_1732_);
lean_dec(v_quotContext_1731_);
lean_dec(v_maxHeartbeats_1730_);
lean_dec(v_initHeartbeats_1729_);
lean_dec(v_openDecls_1728_);
lean_dec(v_currNamespace_1727_);
lean_dec(v_maxRecDepth_1725_);
lean_dec(v_currRecDepth_1724_);
lean_dec_ref(v_options_1723_);
lean_dec_ref(v_fileMap_1722_);
lean_dec_ref(v_fileName_1721_);
lean_dec(v_a_1693_);
lean_dec(v_a_1691_);
lean_dec_ref(v_a_1690_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec(v_a_1684_);
lean_dec_ref(v_rhs_1683_);
lean_dec_ref(v_lhs_1682_);
v___x_1809_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1726_);
return v___x_1809_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = lean_box(0);
v___x_1822_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3));
v___x_1823_ = l_Lean_mkConst(v___x_1822_, v___x_1821_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(lean_object* v_lhs_1824_, lean_object* v_rhs_1825_, uint8_t v_heq_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v___x_1838_; lean_object* v_p_1839_; lean_object* v___x_1840_; lean_object* v_q_1841_; uint8_t v___x_1842_; lean_object* v___x_1843_; 
v___x_1838_ = l_Lean_Expr_appFn_x21(v_lhs_1824_);
v_p_1839_ = l_Lean_Expr_appArg_x21(v___x_1838_);
lean_dec_ref(v___x_1838_);
v___x_1840_ = l_Lean_Expr_appFn_x21(v_rhs_1825_);
v_q_1841_ = l_Lean_Expr_appArg_x21(v___x_1840_);
lean_dec_ref(v___x_1840_);
v___x_1842_ = 0;
lean_inc(v_a_1836_);
lean_inc_ref(v_a_1835_);
lean_inc(v_a_1834_);
lean_inc_ref(v_a_1833_);
lean_inc_ref(v_q_1841_);
lean_inc_ref(v_p_1839_);
v___x_1843_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_p_1839_, v_q_1841_, v___x_1842_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v_hp_1845_; lean_object* v_hq_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref(v___x_1843_);
v_hp_1845_ = l_Lean_Expr_appArg_x21(v_lhs_1824_);
v_hq_1846_ = l_Lean_Expr_appArg_x21(v_rhs_1825_);
v___x_1847_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4);
v___x_1848_ = l_Lean_mkApp5(v___x_1847_, v_p_1839_, v_q_1841_, v_a_1844_, v_hp_1845_, v_hq_1846_);
v___x_1849_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v___x_1848_, v_heq_1826_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
return v___x_1849_;
}
else
{
lean_dec_ref(v_q_1841_);
lean_dec_ref(v_p_1839_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
return v___x_1843_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2(void){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1860_ = lean_box(0);
v___x_1861_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1));
v___x_1862_ = l_Lean_mkConst(v___x_1861_, v___x_1860_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(lean_object* v_lhs_1863_, lean_object* v_rhs_1864_, uint8_t v_heq_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v___x_1877_; lean_object* v_p_1878_; lean_object* v___x_1879_; lean_object* v_q_1880_; uint8_t v___x_1881_; lean_object* v___x_1882_; 
v___x_1877_ = l_Lean_Expr_appFn_x21(v_lhs_1863_);
v_p_1878_ = l_Lean_Expr_appArg_x21(v___x_1877_);
lean_dec_ref(v___x_1877_);
v___x_1879_ = l_Lean_Expr_appFn_x21(v_rhs_1864_);
v_q_1880_ = l_Lean_Expr_appArg_x21(v___x_1879_);
lean_dec_ref(v___x_1879_);
v___x_1881_ = 0;
lean_inc(v_a_1875_);
lean_inc_ref(v_a_1874_);
lean_inc(v_a_1873_);
lean_inc_ref(v_a_1872_);
lean_inc_ref(v_q_1880_);
lean_inc_ref(v_p_1878_);
v___x_1882_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_p_1878_, v_q_1880_, v___x_1881_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v_hp_1884_; lean_object* v_hq_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref(v___x_1882_);
v_hp_1884_ = l_Lean_Expr_appArg_x21(v_lhs_1863_);
v_hq_1885_ = l_Lean_Expr_appArg_x21(v_rhs_1864_);
v___x_1886_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2);
v___x_1887_ = l_Lean_mkApp5(v___x_1886_, v_p_1878_, v_q_1880_, v_a_1883_, v_hp_1884_, v_hq_1885_);
v___x_1888_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v___x_1887_, v_heq_1865_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
return v___x_1888_;
}
else
{
lean_dec_ref(v_q_1880_);
lean_dec_ref(v_p_1878_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
return v___x_1882_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(lean_object* v_lhs_1889_, lean_object* v_rhs_1890_, uint8_t v_heq_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
if (lean_obj_tag(v_lhs_1889_) == 7)
{
if (lean_obj_tag(v_rhs_1890_) == 7)
{
lean_object* v_binderType_1903_; lean_object* v_body_1904_; lean_object* v_binderType_1905_; lean_object* v_body_1906_; lean_object* v___y_1908_; lean_object* v_a_1909_; lean_object* v___x_1928_; uint8_t v_foApprox_1929_; uint8_t v_ctxApprox_1930_; uint8_t v_quasiPatternApprox_1931_; uint8_t v_constApprox_1932_; uint8_t v_isDefEqStuckEx_1933_; uint8_t v_unificationHints_1934_; uint8_t v_proofIrrelevance_1935_; uint8_t v_assignSyntheticOpaque_1936_; uint8_t v_offsetCnstrs_1937_; uint8_t v_etaStruct_1938_; uint8_t v_univApprox_1939_; uint8_t v_iota_1940_; uint8_t v_beta_1941_; uint8_t v_proj_1942_; uint8_t v_zeta_1943_; uint8_t v_zetaDelta_1944_; uint8_t v_zetaUnused_1945_; uint8_t v_zetaHave_1946_; uint8_t v_trackZetaDelta_1947_; lean_object* v_zetaDeltaSet_1948_; lean_object* v_lctx_1949_; lean_object* v_localInstances_1950_; lean_object* v_defEqCtx_x3f_1951_; lean_object* v_synthPendingDepth_1952_; lean_object* v_canUnfold_x3f_1953_; uint8_t v_univApprox_1954_; uint8_t v_inTypeClassResolution_1955_; uint8_t v_cacheInferType_1956_; lean_object* v_a_1958_; uint8_t v___x_2004_; lean_object* v_config_2005_; uint64_t v___x_2006_; uint64_t v___x_2007_; uint64_t v___x_2008_; uint64_t v___x_2009_; uint64_t v___x_2010_; uint64_t v_key_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v_binderType_1903_ = lean_ctor_get(v_lhs_1889_, 1);
lean_inc_ref(v_binderType_1903_);
v_body_1904_ = lean_ctor_get(v_lhs_1889_, 2);
lean_inc_ref(v_body_1904_);
lean_dec_ref(v_lhs_1889_);
v_binderType_1905_ = lean_ctor_get(v_rhs_1890_, 1);
lean_inc_ref(v_binderType_1905_);
v_body_1906_ = lean_ctor_get(v_rhs_1890_, 2);
lean_inc_ref(v_body_1906_);
lean_dec_ref(v_rhs_1890_);
v___x_1928_ = l_Lean_Meta_Context_config(v_a_1898_);
v_foApprox_1929_ = lean_ctor_get_uint8(v___x_1928_, 0);
v_ctxApprox_1930_ = lean_ctor_get_uint8(v___x_1928_, 1);
v_quasiPatternApprox_1931_ = lean_ctor_get_uint8(v___x_1928_, 2);
v_constApprox_1932_ = lean_ctor_get_uint8(v___x_1928_, 3);
v_isDefEqStuckEx_1933_ = lean_ctor_get_uint8(v___x_1928_, 4);
v_unificationHints_1934_ = lean_ctor_get_uint8(v___x_1928_, 5);
v_proofIrrelevance_1935_ = lean_ctor_get_uint8(v___x_1928_, 6);
v_assignSyntheticOpaque_1936_ = lean_ctor_get_uint8(v___x_1928_, 7);
v_offsetCnstrs_1937_ = lean_ctor_get_uint8(v___x_1928_, 8);
v_etaStruct_1938_ = lean_ctor_get_uint8(v___x_1928_, 10);
v_univApprox_1939_ = lean_ctor_get_uint8(v___x_1928_, 11);
v_iota_1940_ = lean_ctor_get_uint8(v___x_1928_, 12);
v_beta_1941_ = lean_ctor_get_uint8(v___x_1928_, 13);
v_proj_1942_ = lean_ctor_get_uint8(v___x_1928_, 14);
v_zeta_1943_ = lean_ctor_get_uint8(v___x_1928_, 15);
v_zetaDelta_1944_ = lean_ctor_get_uint8(v___x_1928_, 16);
v_zetaUnused_1945_ = lean_ctor_get_uint8(v___x_1928_, 17);
v_zetaHave_1946_ = lean_ctor_get_uint8(v___x_1928_, 18);
v_trackZetaDelta_1947_ = lean_ctor_get_uint8(v_a_1898_, sizeof(void*)*7);
v_zetaDeltaSet_1948_ = lean_ctor_get(v_a_1898_, 1);
v_lctx_1949_ = lean_ctor_get(v_a_1898_, 2);
v_localInstances_1950_ = lean_ctor_get(v_a_1898_, 3);
v_defEqCtx_x3f_1951_ = lean_ctor_get(v_a_1898_, 4);
v_synthPendingDepth_1952_ = lean_ctor_get(v_a_1898_, 5);
v_canUnfold_x3f_1953_ = lean_ctor_get(v_a_1898_, 6);
v_univApprox_1954_ = lean_ctor_get_uint8(v_a_1898_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1955_ = lean_ctor_get_uint8(v_a_1898_, sizeof(void*)*7 + 2);
v_cacheInferType_1956_ = lean_ctor_get_uint8(v_a_1898_, sizeof(void*)*7 + 3);
v___x_2004_ = 1;
v_config_2005_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_config_2005_, 0, v_foApprox_1929_);
lean_ctor_set_uint8(v_config_2005_, 1, v_ctxApprox_1930_);
lean_ctor_set_uint8(v_config_2005_, 2, v_quasiPatternApprox_1931_);
lean_ctor_set_uint8(v_config_2005_, 3, v_constApprox_1932_);
lean_ctor_set_uint8(v_config_2005_, 4, v_isDefEqStuckEx_1933_);
lean_ctor_set_uint8(v_config_2005_, 5, v_unificationHints_1934_);
lean_ctor_set_uint8(v_config_2005_, 6, v_proofIrrelevance_1935_);
lean_ctor_set_uint8(v_config_2005_, 7, v_assignSyntheticOpaque_1936_);
lean_ctor_set_uint8(v_config_2005_, 8, v_offsetCnstrs_1937_);
lean_ctor_set_uint8(v_config_2005_, 9, v___x_2004_);
lean_ctor_set_uint8(v_config_2005_, 10, v_etaStruct_1938_);
lean_ctor_set_uint8(v_config_2005_, 11, v_univApprox_1939_);
lean_ctor_set_uint8(v_config_2005_, 12, v_iota_1940_);
lean_ctor_set_uint8(v_config_2005_, 13, v_beta_1941_);
lean_ctor_set_uint8(v_config_2005_, 14, v_proj_1942_);
lean_ctor_set_uint8(v_config_2005_, 15, v_zeta_1943_);
lean_ctor_set_uint8(v_config_2005_, 16, v_zetaDelta_1944_);
lean_ctor_set_uint8(v_config_2005_, 17, v_zetaUnused_1945_);
lean_ctor_set_uint8(v_config_2005_, 18, v_zetaHave_1946_);
v___x_2006_ = l_Lean_Meta_Context_configKey(v_a_1898_);
v___x_2007_ = 2ULL;
v___x_2008_ = lean_uint64_shift_right(v___x_2006_, v___x_2007_);
v___x_2009_ = lean_uint64_shift_left(v___x_2008_, v___x_2007_);
v___x_2010_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2);
v_key_2011_ = lean_uint64_lor(v___x_2009_, v___x_2010_);
v___x_2012_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2012_, 0, v_config_2005_);
lean_ctor_set_uint64(v___x_2012_, sizeof(void*)*1, v_key_2011_);
lean_inc(v_canUnfold_x3f_1953_);
lean_inc(v_synthPendingDepth_1952_);
lean_inc(v_defEqCtx_x3f_1951_);
lean_inc_ref(v_localInstances_1950_);
lean_inc_ref(v_lctx_1949_);
lean_inc(v_zetaDeltaSet_1948_);
v___x_2013_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
lean_ctor_set(v___x_2013_, 1, v_zetaDeltaSet_1948_);
lean_ctor_set(v___x_2013_, 2, v_lctx_1949_);
lean_ctor_set(v___x_2013_, 3, v_localInstances_1950_);
lean_ctor_set(v___x_2013_, 4, v_defEqCtx_x3f_1951_);
lean_ctor_set(v___x_2013_, 5, v_synthPendingDepth_1952_);
lean_ctor_set(v___x_2013_, 6, v_canUnfold_x3f_1953_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*7, v_trackZetaDelta_1947_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*7 + 1, v_univApprox_1954_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1955_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*7 + 3, v_cacheInferType_1956_);
lean_inc(v_a_1901_);
lean_inc_ref(v_a_1900_);
lean_inc(v_a_1899_);
lean_inc_ref(v_binderType_1903_);
v___x_2014_ = l_Lean_Meta_getLevel(v_binderType_1903_, v___x_2013_, v_a_1899_, v_a_1900_, v_a_1901_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref(v___x_2014_);
v_a_1958_ = v_a_2015_;
goto v___jp_1957_;
}
else
{
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2016_; 
v_a_2016_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2016_);
lean_dec_ref(v___x_2014_);
v_a_1958_ = v_a_2016_;
goto v___jp_1957_;
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec_ref(v___x_1928_);
lean_dec_ref(v_body_1906_);
lean_dec_ref(v_binderType_1905_);
lean_dec_ref(v_body_1904_);
lean_dec_ref(v_binderType_1903_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec(v_a_1892_);
v_a_2017_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2014_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2014_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
v___jp_1907_:
{
uint8_t v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = 0;
lean_inc(v_a_1901_);
lean_inc_ref(v_a_1900_);
lean_inc(v_a_1899_);
lean_inc_ref(v_a_1898_);
lean_inc(v_a_1897_);
lean_inc_ref(v_a_1896_);
lean_inc(v_a_1895_);
lean_inc_ref(v_a_1894_);
lean_inc(v_a_1893_);
lean_inc(v_a_1892_);
lean_inc_ref(v_binderType_1905_);
lean_inc_ref(v_binderType_1903_);
v___x_1911_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_binderType_1903_, v_binderType_1905_, v___x_1910_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1913_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref(v___x_1911_);
lean_inc_ref(v_body_1906_);
lean_inc_ref(v_body_1904_);
v___x_1913_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_body_1904_, v_body_1906_, v___x_1910_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1927_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1916_ = v___x_1913_;
v_isShared_1917_ = v_isSharedCheck_1927_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1913_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1927_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1918_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__1));
v___x_1919_ = lean_box(0);
v___x_1920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1920_, 0, v_a_1909_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___y_1908_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = l_Lean_mkConst(v___x_1918_, v___x_1921_);
v___x_1923_ = l_Lean_mkApp6(v___x_1922_, v_binderType_1903_, v_binderType_1905_, v_body_1904_, v_body_1906_, v_a_1912_, v_a_1914_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 0, v___x_1923_);
v___x_1925_ = v___x_1916_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
else
{
lean_dec(v_a_1912_);
lean_dec(v_a_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v_body_1906_);
lean_dec_ref(v_binderType_1905_);
lean_dec_ref(v_body_1904_);
lean_dec_ref(v_binderType_1903_);
return v___x_1913_;
}
}
else
{
lean_dec(v_a_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v_body_1906_);
lean_dec_ref(v_binderType_1905_);
lean_dec_ref(v_body_1904_);
lean_dec_ref(v_binderType_1903_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec(v_a_1892_);
return v___x_1911_;
}
}
v___jp_1957_:
{
uint8_t v_foApprox_1959_; uint8_t v_ctxApprox_1960_; uint8_t v_quasiPatternApprox_1961_; uint8_t v_constApprox_1962_; uint8_t v_isDefEqStuckEx_1963_; uint8_t v_unificationHints_1964_; uint8_t v_proofIrrelevance_1965_; uint8_t v_assignSyntheticOpaque_1966_; uint8_t v_offsetCnstrs_1967_; uint8_t v_etaStruct_1968_; uint8_t v_univApprox_1969_; uint8_t v_iota_1970_; uint8_t v_beta_1971_; uint8_t v_proj_1972_; uint8_t v_zeta_1973_; uint8_t v_zetaDelta_1974_; uint8_t v_zetaUnused_1975_; uint8_t v_zetaHave_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_2003_; 
v_foApprox_1959_ = lean_ctor_get_uint8(v___x_1928_, 0);
v_ctxApprox_1960_ = lean_ctor_get_uint8(v___x_1928_, 1);
v_quasiPatternApprox_1961_ = lean_ctor_get_uint8(v___x_1928_, 2);
v_constApprox_1962_ = lean_ctor_get_uint8(v___x_1928_, 3);
v_isDefEqStuckEx_1963_ = lean_ctor_get_uint8(v___x_1928_, 4);
v_unificationHints_1964_ = lean_ctor_get_uint8(v___x_1928_, 5);
v_proofIrrelevance_1965_ = lean_ctor_get_uint8(v___x_1928_, 6);
v_assignSyntheticOpaque_1966_ = lean_ctor_get_uint8(v___x_1928_, 7);
v_offsetCnstrs_1967_ = lean_ctor_get_uint8(v___x_1928_, 8);
v_etaStruct_1968_ = lean_ctor_get_uint8(v___x_1928_, 10);
v_univApprox_1969_ = lean_ctor_get_uint8(v___x_1928_, 11);
v_iota_1970_ = lean_ctor_get_uint8(v___x_1928_, 12);
v_beta_1971_ = lean_ctor_get_uint8(v___x_1928_, 13);
v_proj_1972_ = lean_ctor_get_uint8(v___x_1928_, 14);
v_zeta_1973_ = lean_ctor_get_uint8(v___x_1928_, 15);
v_zetaDelta_1974_ = lean_ctor_get_uint8(v___x_1928_, 16);
v_zetaUnused_1975_ = lean_ctor_get_uint8(v___x_1928_, 17);
v_zetaHave_1976_ = lean_ctor_get_uint8(v___x_1928_, 18);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1978_ = v___x_1928_;
v_isShared_1979_ = v_isSharedCheck_2003_;
goto v_resetjp_1977_;
}
else
{
lean_dec(v___x_1928_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_2003_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
uint8_t v___x_1980_; lean_object* v_config_1982_; 
v___x_1980_ = 1;
if (v_isShared_1979_ == 0)
{
v_config_1982_ = v___x_1978_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, 0, v_foApprox_1959_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, 1, v_ctxApprox_1960_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, 2, v_quasiPatternApprox_1961_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, 3, v_constApprox_1962_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, 4, v_isDefEqStuckEx_1963_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, 5, v_unificationHints_1964_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, 6, v_proofIrrelevance_1965_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, 7, v_assignSyntheticOpaque_1966_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, 8, v_offsetCnstrs_1967_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, 10, v_etaStruct_1968_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, 11, v_univApprox_1969_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, 12, v_iota_1970_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, 13, v_beta_1971_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, 14, v_proj_1972_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, 15, v_zeta_1973_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, 16, v_zetaDelta_1974_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, 17, v_zetaUnused_1975_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, 18, v_zetaHave_1976_);
v_config_1982_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
uint64_t v___x_1983_; uint64_t v___x_1984_; uint64_t v___x_1985_; uint64_t v___x_1986_; uint64_t v___x_1987_; uint64_t v_key_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
lean_ctor_set_uint8(v_config_1982_, 9, v___x_1980_);
v___x_1983_ = l_Lean_Meta_Context_configKey(v_a_1898_);
v___x_1984_ = 2ULL;
v___x_1985_ = lean_uint64_shift_right(v___x_1983_, v___x_1984_);
v___x_1986_ = lean_uint64_shift_left(v___x_1985_, v___x_1984_);
v___x_1987_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2);
v_key_1988_ = lean_uint64_lor(v___x_1986_, v___x_1987_);
v___x_1989_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1989_, 0, v_config_1982_);
lean_ctor_set_uint64(v___x_1989_, sizeof(void*)*1, v_key_1988_);
lean_inc(v_canUnfold_x3f_1953_);
lean_inc(v_synthPendingDepth_1952_);
lean_inc(v_defEqCtx_x3f_1951_);
lean_inc_ref(v_localInstances_1950_);
lean_inc_ref(v_lctx_1949_);
lean_inc(v_zetaDeltaSet_1948_);
v___x_1990_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
lean_ctor_set(v___x_1990_, 1, v_zetaDeltaSet_1948_);
lean_ctor_set(v___x_1990_, 2, v_lctx_1949_);
lean_ctor_set(v___x_1990_, 3, v_localInstances_1950_);
lean_ctor_set(v___x_1990_, 4, v_defEqCtx_x3f_1951_);
lean_ctor_set(v___x_1990_, 5, v_synthPendingDepth_1952_);
lean_ctor_set(v___x_1990_, 6, v_canUnfold_x3f_1953_);
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*7, v_trackZetaDelta_1947_);
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*7 + 1, v_univApprox_1954_);
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1955_);
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*7 + 3, v_cacheInferType_1956_);
lean_inc(v_a_1901_);
lean_inc_ref(v_a_1900_);
lean_inc(v_a_1899_);
lean_inc_ref(v_body_1904_);
v___x_1991_ = l_Lean_Meta_getLevel(v_body_1904_, v___x_1990_, v_a_1899_, v_a_1900_, v_a_1901_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref(v___x_1991_);
v___y_1908_ = v_a_1958_;
v_a_1909_ = v_a_1992_;
goto v___jp_1907_;
}
else
{
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1993_; 
v_a_1993_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1993_);
lean_dec_ref(v___x_1991_);
v___y_1908_ = v_a_1958_;
v_a_1909_ = v_a_1993_;
goto v___jp_1907_;
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec(v_a_1958_);
lean_dec_ref(v_body_1906_);
lean_dec_ref(v_binderType_1905_);
lean_dec_ref(v_body_1904_);
lean_dec_ref(v_binderType_1903_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec(v_a_1892_);
v_a_1994_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1991_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1991_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
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
lean_object* v___x_2025_; lean_object* v___x_2026_; 
lean_dec_ref(v_lhs_1889_);
lean_dec_ref(v_rhs_1890_);
v___x_2025_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4);
v___x_2026_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2025_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
return v___x_2026_;
}
}
else
{
lean_object* v___x_2027_; 
lean_inc_ref(v_lhs_1889_);
v___x_2027_ = l_Lean_Meta_Grind_useFunCC___redArg(v_lhs_1889_, v_a_1892_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; uint8_t v___x_2029_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref(v___x_2027_);
v___x_2029_ = lean_unbox(v_a_2028_);
lean_dec(v_a_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; 
v___x_2030_ = l_Lean_Expr_getAppNumArgs(v_lhs_1889_);
v___x_2031_ = l_Lean_Expr_getAppNumArgs(v_rhs_1890_);
v___x_2032_ = lean_nat_dec_eq(v___x_2031_, v___x_2030_);
lean_dec(v___x_2031_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
lean_dec(v___x_2030_);
lean_dec_ref(v_rhs_1890_);
lean_dec_ref(v_lhs_1889_);
v___x_2033_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6);
v___x_2034_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2033_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
return v___x_2034_;
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; uint8_t v___y_2052_; uint8_t v___y_2064_; lean_object* v___x_2068_; uint8_t v___x_2069_; uint8_t v___y_2074_; 
v___x_2035_ = l_Lean_Expr_getAppFn(v_lhs_1889_);
v___x_2036_ = l_Lean_Expr_getAppFn(v_rhs_1890_);
v___x_2068_ = lean_unsigned_to_nat(2u);
v___x_2069_ = lean_nat_dec_eq(v___x_2030_, v___x_2068_);
if (v___x_2069_ == 0)
{
v___y_2074_ = v___x_2069_;
goto v___jp_2073_;
}
else
{
lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2078_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10));
v___x_2079_ = l_Lean_Expr_isConstOf(v___x_2035_, v___x_2078_);
v___y_2074_ = v___x_2079_;
goto v___jp_2073_;
}
v___jp_2037_:
{
lean_object* v___x_2038_; 
lean_inc(v_a_1901_);
lean_inc_ref(v_a_1900_);
lean_inc(v_a_1899_);
lean_inc_ref(v_a_1898_);
lean_inc_ref(v_rhs_1890_);
lean_inc_ref(v_lhs_1889_);
v___x_2038_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(v_lhs_1889_, v_rhs_1890_, v___x_2035_, v___x_2036_, v___x_2030_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
lean_dec_ref(v___x_2036_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; uint8_t v___x_2040_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref(v___x_2038_);
v___x_2040_ = lean_unbox(v_a_2039_);
lean_dec(v_a_2039_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2041_; 
v___x_2041_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_1889_, v_rhs_1890_, v_heq_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
return v___x_2041_;
}
else
{
lean_object* v___x_2042_; 
v___x_2042_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_1889_, v_rhs_1890_, v_heq_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
lean_dec_ref(v_rhs_1890_);
lean_dec_ref(v_lhs_1889_);
return v___x_2042_;
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_rhs_1890_);
lean_dec_ref(v_lhs_1889_);
v_a_2043_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2038_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2038_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
v___jp_2051_:
{
if (v___y_2052_ == 0)
{
goto v___jp_2037_;
}
else
{
lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2053_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_2054_ = l_Lean_Expr_isConstOf(v___x_2036_, v___x_2053_);
if (v___x_2054_ == 0)
{
goto v___jp_2037_;
}
else
{
lean_object* v___x_2055_; 
lean_dec_ref(v___x_2036_);
lean_dec_ref(v___x_2035_);
lean_dec(v___x_2030_);
lean_inc(v_a_1901_);
lean_inc_ref(v_a_1900_);
lean_inc(v_a_1899_);
lean_inc_ref(v_a_1898_);
v___x_2055_ = l_Lean_Meta_Grind_mkEqCongrProof(v_lhs_1889_, v_rhs_1890_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
if (lean_obj_tag(v___x_2055_) == 0)
{
if (v_heq_1891_ == 0)
{
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
return v___x_2055_;
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2057_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref(v___x_2055_);
v___x_2057_ = l_Lean_Meta_mkHEqOfEq(v_a_2056_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
return v___x_2057_;
}
}
else
{
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
return v___x_2055_;
}
}
}
}
v___jp_2058_:
{
lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2059_ = lean_unsigned_to_nat(3u);
v___x_2060_ = lean_nat_dec_eq(v___x_2030_, v___x_2059_);
if (v___x_2060_ == 0)
{
v___y_2052_ = v___x_2060_;
goto v___jp_2051_;
}
else
{
lean_object* v___x_2061_; uint8_t v___x_2062_; 
v___x_2061_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_2062_ = l_Lean_Expr_isConstOf(v___x_2035_, v___x_2061_);
v___y_2052_ = v___x_2062_;
goto v___jp_2051_;
}
}
v___jp_2063_:
{
if (v___y_2064_ == 0)
{
goto v___jp_2058_;
}
else
{
lean_object* v___x_2065_; uint8_t v___x_2066_; 
v___x_2065_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8));
v___x_2066_ = l_Lean_Expr_isConstOf(v___x_2036_, v___x_2065_);
if (v___x_2066_ == 0)
{
goto v___jp_2058_;
}
else
{
lean_object* v___x_2067_; 
lean_dec_ref(v___x_2036_);
lean_dec_ref(v___x_2035_);
lean_dec(v___x_2030_);
v___x_2067_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_1889_, v_rhs_1890_, v_heq_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
lean_dec_ref(v_rhs_1890_);
lean_dec_ref(v_lhs_1889_);
return v___x_2067_;
}
}
}
v___jp_2070_:
{
if (v___x_2069_ == 0)
{
v___y_2064_ = v___x_2069_;
goto v___jp_2063_;
}
else
{
lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2071_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8));
v___x_2072_ = l_Lean_Expr_isConstOf(v___x_2035_, v___x_2071_);
v___y_2064_ = v___x_2072_;
goto v___jp_2063_;
}
}
v___jp_2073_:
{
if (v___y_2074_ == 0)
{
goto v___jp_2070_;
}
else
{
lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2075_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10));
v___x_2076_ = l_Lean_Expr_isConstOf(v___x_2036_, v___x_2075_);
if (v___x_2076_ == 0)
{
goto v___jp_2070_;
}
else
{
lean_object* v___x_2077_; 
lean_dec_ref(v___x_2036_);
lean_dec_ref(v___x_2035_);
lean_dec(v___x_2030_);
v___x_2077_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_1889_, v_rhs_1890_, v_heq_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
lean_dec_ref(v_rhs_1890_);
lean_dec_ref(v_lhs_1889_);
return v___x_2077_;
}
}
}
}
}
else
{
lean_object* v___x_2080_; 
v___x_2080_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_1889_, v_rhs_1890_, v_heq_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
return v___x_2080_;
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_rhs_1890_);
lean_dec_ref(v_lhs_1889_);
v_a_2081_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2027_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2027_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(lean_object* v_lhs_2089_, lean_object* v_rhs_2090_, lean_object* v_h_2091_, uint8_t v_flipped_2092_, uint8_t v_heq_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2105_ = l_Lean_Meta_Grind_congrPlaceholderProof;
v___x_2106_ = lean_expr_eqv(v_h_2091_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; uint8_t v___x_2108_; 
v___x_2107_ = l_Lean_Meta_Grind_eqCongrSymmPlaceholderProof;
v___x_2108_ = lean_expr_eqv(v_h_2091_, v___x_2107_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; 
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
lean_dec(v_a_2095_);
lean_dec(v_a_2094_);
lean_dec_ref(v_rhs_2090_);
lean_dec_ref(v_lhs_2089_);
v___x_2109_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(v_h_2091_, v_flipped_2092_, v_heq_2093_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
return v___x_2109_;
}
else
{
lean_object* v___x_2110_; 
lean_dec_ref(v_h_2091_);
lean_inc(v_a_2103_);
lean_inc_ref(v_a_2102_);
lean_inc(v_a_2101_);
lean_inc_ref(v_a_2100_);
v___x_2110_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(v_lhs_2089_, v_rhs_2090_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
if (lean_obj_tag(v___x_2110_) == 0)
{
if (v_heq_2093_ == 0)
{
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
return v___x_2110_;
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2112_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref(v___x_2110_);
v___x_2112_ = l_Lean_Meta_mkHEqOfEq(v_a_2111_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
return v___x_2112_;
}
}
else
{
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
return v___x_2110_;
}
}
}
else
{
lean_object* v___x_2113_; 
lean_dec_ref(v_h_2091_);
v___x_2113_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(v_lhs_2089_, v_rhs_2090_, v_heq_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
return v___x_2113_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2115_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2116_ = lean_unsigned_to_nat(29u);
v___x_2117_ = lean_unsigned_to_nat(288u);
v___x_2118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0));
v___x_2119_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2120_ = l_mkPanicMessageWithDecl(v___x_2119_, v___x_2118_, v___x_2117_, v___x_2116_, v___x_2115_);
return v___x_2120_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2121_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2122_ = lean_unsigned_to_nat(35u);
v___x_2123_ = lean_unsigned_to_nat(287u);
v___x_2124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0));
v___x_2125_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2126_ = l_mkPanicMessageWithDecl(v___x_2125_, v___x_2124_, v___x_2123_, v___x_2122_, v___x_2121_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(lean_object* v_lhs_2127_, lean_object* v_common_2128_, lean_object* v_acc_2129_, uint8_t v_heq_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_){
_start:
{
uint8_t v___x_2142_; 
v___x_2142_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_lhs_2127_, v_common_2128_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = lean_st_ref_get(v_a_2131_);
lean_inc_ref(v_lhs_2127_);
v___x_2144_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2143_, v_lhs_2127_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v_target_x3f_2146_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref(v___x_2144_);
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
v_flipped_2148_ = lean_ctor_get_uint8(v_a_2145_, sizeof(void*)*11);
lean_dec(v_a_2145_);
v_val_2149_ = lean_ctor_get(v_target_x3f_2146_, 0);
lean_inc(v_val_2149_);
lean_dec_ref(v_target_x3f_2146_);
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
lean_inc(v_a_2140_);
lean_inc_ref(v_a_2139_);
lean_inc(v_a_2138_);
lean_inc_ref(v_a_2137_);
lean_inc(v_a_2136_);
lean_inc_ref(v_a_2135_);
lean_inc(v_a_2134_);
lean_inc_ref(v_a_2133_);
lean_inc(v_a_2132_);
lean_inc(v_a_2131_);
lean_inc(v_val_2149_);
v___x_2154_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_lhs_2127_, v_val_2149_, v_val_2150_, v_flipped_2148_, v_heq_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2156_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref(v___x_2154_);
lean_inc(v_a_2140_);
lean_inc_ref(v_a_2139_);
lean_inc(v_a_2138_);
lean_inc_ref(v_a_2137_);
v___x_2156_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_acc_2129_, v_a_2155_, v_heq_2130_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2159_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref(v___x_2156_);
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
v_lhs_2127_ = v_val_2149_;
v_acc_2129_ = v___x_2159_;
goto _start;
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_del_object(v___x_2152_);
lean_dec(v_val_2149_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec(v_a_2131_);
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
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec(v_a_2131_);
lean_dec(v_acc_2129_);
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
lean_dec_ref(v_target_x3f_2146_);
lean_dec(v_proof_x3f_2147_);
lean_dec(v_a_2145_);
lean_dec(v_acc_2129_);
lean_dec_ref(v_lhs_2127_);
v___x_2179_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1);
v___x_2180_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2179_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
return v___x_2180_;
}
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
lean_dec(v_target_x3f_2146_);
lean_dec(v_a_2145_);
lean_dec(v_acc_2129_);
lean_dec_ref(v_lhs_2127_);
v___x_2181_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2);
v___x_2182_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2181_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
return v___x_2182_;
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec(v_a_2131_);
lean_dec(v_acc_2129_);
lean_dec_ref(v_lhs_2127_);
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
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec(v_a_2131_);
lean_dec_ref(v_lhs_2127_);
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v_acc_2129_);
return v___x_2191_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2193_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2194_ = lean_unsigned_to_nat(29u);
v___x_2195_ = lean_unsigned_to_nat(300u);
v___x_2196_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0));
v___x_2197_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2198_ = l_mkPanicMessageWithDecl(v___x_2197_, v___x_2196_, v___x_2195_, v___x_2194_, v___x_2193_);
return v___x_2198_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2(void){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2199_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2200_ = lean_unsigned_to_nat(35u);
v___x_2201_ = lean_unsigned_to_nat(299u);
v___x_2202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0));
v___x_2203_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2204_ = l_mkPanicMessageWithDecl(v___x_2203_, v___x_2202_, v___x_2201_, v___x_2200_, v___x_2199_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(lean_object* v_rhs_2205_, lean_object* v_common_2206_, lean_object* v_lhsEqCommon_x3f_2207_, uint8_t v_heq_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
uint8_t v___x_2220_; 
v___x_2220_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_rhs_2205_, v_common_2206_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = lean_st_ref_get(v_a_2209_);
lean_inc_ref(v_rhs_2205_);
v___x_2222_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2221_, v_rhs_2205_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v_target_x3f_2224_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_a_2223_);
lean_dec_ref(v___x_2222_);
v_target_x3f_2224_ = lean_ctor_get(v_a_2223_, 4);
lean_inc(v_target_x3f_2224_);
if (lean_obj_tag(v_target_x3f_2224_) == 1)
{
lean_object* v_proof_x3f_2225_; 
v_proof_x3f_2225_ = lean_ctor_get(v_a_2223_, 5);
lean_inc(v_proof_x3f_2225_);
if (lean_obj_tag(v_proof_x3f_2225_) == 1)
{
uint8_t v_flipped_2226_; lean_object* v_val_2227_; lean_object* v_val_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2267_; 
v_flipped_2226_ = lean_ctor_get_uint8(v_a_2223_, sizeof(void*)*11);
lean_dec(v_a_2223_);
v_val_2227_ = lean_ctor_get(v_target_x3f_2224_, 0);
lean_inc(v_val_2227_);
lean_dec_ref(v_target_x3f_2224_);
v_val_2228_ = lean_ctor_get(v_proof_x3f_2225_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_proof_x3f_2225_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2230_ = v_proof_x3f_2225_;
v_isShared_2231_ = v_isSharedCheck_2267_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_val_2228_);
lean_dec(v_proof_x3f_2225_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2267_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
uint8_t v___y_2233_; 
if (v_flipped_2226_ == 0)
{
uint8_t v___x_2266_; 
v___x_2266_ = 1;
v___y_2233_ = v___x_2266_;
goto v___jp_2232_;
}
else
{
v___y_2233_ = v___x_2220_;
goto v___jp_2232_;
}
v___jp_2232_:
{
lean_object* v___x_2234_; 
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc(v_a_2216_);
lean_inc_ref(v_a_2215_);
lean_inc(v_a_2214_);
lean_inc_ref(v_a_2213_);
lean_inc(v_a_2212_);
lean_inc_ref(v_a_2211_);
lean_inc(v_a_2210_);
lean_inc(v_a_2209_);
lean_inc(v_val_2227_);
v___x_2234_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_val_2227_, v_rhs_2205_, v_val_2228_, v___y_2233_, v_heq_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2236_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref(v___x_2234_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc(v_a_2216_);
lean_inc_ref(v_a_2215_);
v___x_2236_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_val_2227_, v_common_2206_, v_lhsEqCommon_x3f_2207_, v_heq_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2238_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2237_);
lean_dec_ref(v___x_2236_);
v___x_2238_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_a_2237_, v_a_2235_, v_heq_2208_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2249_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2241_ = v___x_2238_;
v_isShared_2242_ = v_isSharedCheck_2249_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2238_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2249_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 0, v_a_2239_);
v___x_2244_ = v___x_2230_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
lean_object* v___x_2246_; 
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v___x_2244_);
v___x_2246_ = v___x_2241_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2244_);
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
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_del_object(v___x_2230_);
v_a_2250_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2238_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2238_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
else
{
lean_dec(v_a_2235_);
lean_del_object(v___x_2230_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
return v___x_2236_;
}
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
lean_del_object(v___x_2230_);
lean_dec(v_val_2227_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
lean_dec(v_a_2210_);
lean_dec(v_a_2209_);
lean_dec(v_lhsEqCommon_x3f_2207_);
v_a_2258_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2234_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2234_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
}
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
lean_dec_ref(v_target_x3f_2224_);
lean_dec(v_proof_x3f_2225_);
lean_dec(v_a_2223_);
lean_dec(v_lhsEqCommon_x3f_2207_);
lean_dec_ref(v_rhs_2205_);
v___x_2268_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1);
v___x_2269_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2268_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
return v___x_2269_;
}
}
else
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
lean_dec(v_target_x3f_2224_);
lean_dec(v_a_2223_);
lean_dec(v_lhsEqCommon_x3f_2207_);
lean_dec_ref(v_rhs_2205_);
v___x_2270_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2);
v___x_2271_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2270_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
return v___x_2271_;
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
lean_dec(v_a_2210_);
lean_dec(v_a_2209_);
lean_dec(v_lhsEqCommon_x3f_2207_);
lean_dec_ref(v_rhs_2205_);
v_a_2272_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2222_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2222_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
else
{
lean_object* v___x_2280_; 
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
lean_dec(v_a_2210_);
lean_dec(v_a_2209_);
lean_dec_ref(v_rhs_2205_);
v___x_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2280_, 0, v_lhsEqCommon_x3f_2207_);
return v___x_2280_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3(void){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2281_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2282_ = lean_unsigned_to_nat(72u);
v___x_2283_ = lean_unsigned_to_nat(321u);
v___x_2284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0));
v___x_2285_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2286_ = l_mkPanicMessageWithDecl(v___x_2285_, v___x_2284_, v___x_2283_, v___x_2282_, v___x_2281_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(lean_object* v_lhs_2287_, lean_object* v_rhs_2288_, uint8_t v_heq_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
uint8_t v___x_2301_; 
v___x_2301_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_lhs_2287_, v_rhs_2288_);
if (v___x_2301_ == 0)
{
lean_object* v___x_2302_; 
lean_inc_ref(v_lhs_2287_);
v___x_2302_ = l_Lean_Meta_Grind_getRootENode___redArg(v_lhs_2287_, v_a_2290_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref(v___x_2302_);
v___x_2304_ = lean_st_ref_get(v_a_2290_);
lean_inc_ref(v_lhs_2287_);
v___x_2305_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2304_, v_lhs_2287_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref(v___x_2305_);
v___x_2307_ = lean_st_ref_get(v_a_2290_);
lean_inc_ref(v_rhs_2288_);
v___x_2308_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2307_, v_rhs_2288_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v_root_2310_; lean_object* v_root_2311_; uint8_t v___x_2312_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref(v___x_2308_);
v_root_2310_ = lean_ctor_get(v_a_2306_, 2);
lean_inc_ref(v_root_2310_);
lean_dec(v_a_2306_);
v_root_2311_ = lean_ctor_get(v_a_2309_, 2);
lean_inc_ref(v_root_2311_);
lean_dec(v_a_2309_);
v___x_2312_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_root_2310_, v_root_2311_);
lean_dec_ref(v_root_2311_);
lean_dec_ref(v_root_2310_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
lean_dec(v_a_2303_);
lean_dec_ref(v_rhs_2288_);
lean_dec_ref(v_lhs_2287_);
v___x_2313_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2);
v___x_2314_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2313_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_2314_;
}
else
{
lean_object* v___x_2315_; 
lean_inc(v_a_2299_);
lean_inc_ref(v_a_2298_);
lean_inc(v_a_2297_);
lean_inc_ref(v_a_2296_);
lean_inc(v_a_2295_);
lean_inc_ref(v_a_2294_);
lean_inc(v_a_2293_);
lean_inc_ref(v_a_2292_);
lean_inc(v_a_2291_);
lean_inc(v_a_2290_);
lean_inc_ref(v_rhs_2288_);
lean_inc_ref(v_lhs_2287_);
v___x_2315_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(v_lhs_2287_, v_rhs_2288_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; uint8_t v_heqProofs_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref(v___x_2315_);
v_heqProofs_2317_ = lean_ctor_get_uint8(v_a_2303_, sizeof(void*)*11 + 4);
lean_dec(v_a_2303_);
v___x_2318_ = lean_box(0);
lean_inc(v_a_2299_);
lean_inc_ref(v_a_2298_);
lean_inc(v_a_2297_);
lean_inc_ref(v_a_2296_);
lean_inc(v_a_2295_);
lean_inc_ref(v_a_2294_);
lean_inc(v_a_2293_);
lean_inc_ref(v_a_2292_);
lean_inc(v_a_2291_);
lean_inc(v_a_2290_);
v___x_2319_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_2287_, v_a_2316_, v___x_2318_, v_heqProofs_2317_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2321_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref(v___x_2319_);
lean_inc(v_a_2299_);
lean_inc_ref(v_a_2298_);
lean_inc(v_a_2297_);
lean_inc_ref(v_a_2296_);
lean_inc(v_a_2295_);
lean_inc_ref(v_a_2294_);
lean_inc(v_a_2293_);
lean_inc_ref(v_a_2292_);
lean_inc(v_a_2291_);
lean_inc(v_a_2290_);
v___x_2321_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_2288_, v_a_2316_, v_a_2320_, v_heqProofs_2317_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
lean_dec(v_a_2316_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2337_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2324_ = v___x_2321_;
v_isShared_2325_ = v_isSharedCheck_2337_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2321_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2337_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
if (lean_obj_tag(v_a_2322_) == 1)
{
lean_object* v_val_2326_; uint8_t v___y_2331_; 
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec(v_a_2290_);
v_val_2326_ = lean_ctor_get(v_a_2322_, 0);
lean_inc(v_val_2326_);
lean_dec_ref(v_a_2322_);
if (v_heq_2289_ == 0)
{
if (v_heqProofs_2317_ == 0)
{
v___y_2331_ = v___x_2312_;
goto v___jp_2330_;
}
else
{
lean_del_object(v___x_2324_);
goto v___jp_2327_;
}
}
else
{
v___y_2331_ = v_heqProofs_2317_;
goto v___jp_2330_;
}
v___jp_2327_:
{
if (v_heq_2289_ == 0)
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Lean_Meta_mkEqOfHEq(v_val_2326_, v_heq_2289_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_2328_;
}
else
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_Meta_mkHEqOfEq(v_val_2326_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_2329_;
}
}
v___jp_2330_:
{
if (v___y_2331_ == 0)
{
lean_del_object(v___x_2324_);
goto v___jp_2327_;
}
else
{
lean_object* v___x_2333_; 
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v_val_2326_);
v___x_2333_ = v___x_2324_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_val_2326_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
else
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
lean_del_object(v___x_2324_);
lean_dec(v_a_2322_);
v___x_2335_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3);
v___x_2336_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2335_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_2336_;
}
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec(v_a_2290_);
v_a_2338_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2321_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2321_);
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
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec(v_a_2316_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_rhs_2288_);
v_a_2346_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2319_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2319_);
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
lean_dec(v_a_2303_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_rhs_2288_);
lean_dec_ref(v_lhs_2287_);
return v___x_2315_;
}
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec(v_a_2306_);
lean_dec(v_a_2303_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_rhs_2288_);
lean_dec_ref(v_lhs_2287_);
v_a_2354_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2308_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2308_);
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
lean_dec(v_a_2303_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_rhs_2288_);
lean_dec_ref(v_lhs_2287_);
v_a_2362_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2305_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2305_);
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
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_rhs_2288_);
lean_dec_ref(v_lhs_2287_);
v_a_2370_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2302_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2302_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
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
lean_object* v___x_2378_; 
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_rhs_2288_);
v___x_2378_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(v_lhs_2287_, v_heq_2289_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_2378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(lean_object* v_thm_2379_, lean_object* v_lhs_2380_, lean_object* v_rhs_2381_, lean_object* v_i_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v___x_2394_; uint8_t v___x_2395_; 
v___x_2394_ = lean_unsigned_to_nat(0u);
v___x_2395_ = lean_nat_dec_lt(v___x_2394_, v_i_2382_);
if (v___x_2395_ == 0)
{
lean_object* v_proof_2396_; lean_object* v___x_2397_; 
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec(v_a_2383_);
v_proof_2396_ = lean_ctor_get(v_thm_2379_, 1);
lean_inc_ref(v_proof_2396_);
v___x_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2397_, 0, v_proof_2396_);
return v___x_2397_;
}
else
{
lean_object* v___x_2398_; lean_object* v_i_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2398_ = lean_unsigned_to_nat(1u);
v_i_2399_ = lean_nat_sub(v_i_2382_, v___x_2398_);
v___x_2400_ = l_Lean_Expr_appFn_x21(v_lhs_2380_);
v___x_2401_ = l_Lean_Expr_appFn_x21(v_rhs_2381_);
lean_inc(v_a_2392_);
lean_inc_ref(v_a_2391_);
lean_inc(v_a_2390_);
lean_inc_ref(v_a_2389_);
lean_inc(v_a_2388_);
lean_inc_ref(v_a_2387_);
lean_inc(v_a_2386_);
lean_inc_ref(v_a_2385_);
lean_inc(v_a_2384_);
lean_inc(v_a_2383_);
v___x_2402_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_2379_, v___x_2400_, v___x_2401_, v_i_2399_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
lean_dec_ref(v___x_2401_);
lean_dec_ref(v___x_2400_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v_argKinds_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; uint8_t v___y_2408_; uint8_t v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; uint8_t v___x_2422_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref(v___x_2402_);
v_argKinds_2404_ = lean_ctor_get(v_thm_2379_, 2);
v___x_2405_ = l_Lean_Expr_appArg_x21(v_lhs_2380_);
v___x_2406_ = l_Lean_Expr_appArg_x21(v_rhs_2381_);
v___x_2419_ = 0;
v___x_2420_ = lean_box(v___x_2419_);
v___x_2421_ = lean_array_get_borrowed(v___x_2420_, v_argKinds_2404_, v_i_2399_);
lean_dec(v_i_2399_);
v___x_2422_ = lean_unbox(v___x_2421_);
if (v___x_2422_ == 4)
{
v___y_2408_ = v___x_2395_;
goto v___jp_2407_;
}
else
{
uint8_t v___x_2423_; 
v___x_2423_ = 0;
v___y_2408_ = v___x_2423_;
goto v___jp_2407_;
}
v___jp_2407_:
{
lean_object* v___x_2409_; 
lean_inc_ref(v___x_2406_);
lean_inc_ref(v___x_2405_);
v___x_2409_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___x_2405_, v___x_2406_, v___y_2408_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2418_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2412_ = v___x_2409_;
v_isShared_2413_ = v_isSharedCheck_2418_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2409_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2418_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v___x_2416_; 
v___x_2414_ = l_Lean_mkApp3(v_a_2403_, v___x_2405_, v___x_2406_, v_a_2410_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2414_);
v___x_2416_ = v___x_2412_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
else
{
lean_dec_ref(v___x_2406_);
lean_dec_ref(v___x_2405_);
lean_dec(v_a_2403_);
return v___x_2409_;
}
}
}
else
{
lean_dec(v_i_2399_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec(v_a_2383_);
return v___x_2402_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(lean_object* v_f_2427_, lean_object* v_g_2428_, lean_object* v_numArgs_2429_, lean_object* v_lhs_2430_, lean_object* v_rhs_2431_, uint8_t v_heq_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v___x_2444_; 
lean_inc(v_a_2442_);
lean_inc_ref(v_a_2441_);
lean_inc(v_a_2440_);
lean_inc_ref(v_a_2439_);
lean_inc(v_numArgs_2429_);
lean_inc_ref(v_f_2427_);
v___x_2444_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(v_f_2427_, v_numArgs_2429_, v_a_2436_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v_argKinds_2446_; lean_object* v___x_2447_; uint8_t v___x_2448_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
lean_inc(v_a_2445_);
lean_dec_ref(v___x_2444_);
v_argKinds_2446_ = lean_ctor_get(v_a_2445_, 2);
v___x_2447_ = lean_array_get_size(v_argKinds_2446_);
v___x_2448_ = lean_nat_dec_eq(v___x_2447_, v_numArgs_2429_);
if (v___x_2448_ == 0)
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
lean_dec(v_a_2445_);
lean_dec_ref(v_rhs_2431_);
lean_dec_ref(v_lhs_2430_);
lean_dec(v_numArgs_2429_);
lean_dec_ref(v_g_2428_);
lean_dec_ref(v_f_2427_);
v___x_2449_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2);
v___x_2450_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2449_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
return v___x_2450_;
}
else
{
lean_object* v___x_2451_; 
lean_inc(v_a_2442_);
lean_inc_ref(v_a_2441_);
lean_inc(v_a_2440_);
lean_inc_ref(v_a_2439_);
lean_inc(v_a_2438_);
lean_inc_ref(v_a_2437_);
lean_inc(v_a_2436_);
lean_inc_ref(v_a_2435_);
lean_inc(v_a_2434_);
lean_inc(v_a_2433_);
v___x_2451_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_2445_, v_lhs_2430_, v_rhs_2431_, v_numArgs_2429_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
lean_dec(v_a_2445_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; uint8_t v___x_2453_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2452_);
lean_dec_ref(v___x_2451_);
v___x_2453_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_f_2427_, v_g_2428_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__4));
lean_inc(v_a_2442_);
lean_inc_ref(v_a_2441_);
v___x_2455_ = l_Lean_Core_mkFreshUserName(v___x_2454_, v_a_2441_, v_a_2442_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2457_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref(v___x_2455_);
lean_inc(v_a_2442_);
lean_inc_ref(v_a_2441_);
lean_inc(v_a_2440_);
lean_inc_ref(v_a_2439_);
lean_inc_ref(v_f_2427_);
v___x_2457_ = lean_infer_type(v_f_2427_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___f_2461_; lean_object* v___x_2462_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref(v___x_2457_);
v___x_2459_ = lean_box(v___x_2453_);
v___x_2460_ = lean_box(v___x_2448_);
v___f_2461_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___boxed), 17, 5);
lean_closure_set(v___f_2461_, 0, v_numArgs_2429_);
lean_closure_set(v___f_2461_, 1, v_rhs_2431_);
lean_closure_set(v___f_2461_, 2, v_lhs_2430_);
lean_closure_set(v___f_2461_, 3, v___x_2459_);
lean_closure_set(v___f_2461_, 4, v___x_2460_);
lean_inc(v_a_2442_);
lean_inc_ref(v_a_2441_);
lean_inc(v_a_2440_);
lean_inc_ref(v_a_2439_);
lean_inc(v_a_2438_);
lean_inc_ref(v_a_2437_);
lean_inc(v_a_2436_);
lean_inc_ref(v_a_2435_);
lean_inc(v_a_2434_);
lean_inc(v_a_2433_);
v___x_2462_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_a_2456_, v_a_2458_, v___f_2461_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2464_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_a_2463_);
lean_dec_ref(v___x_2462_);
lean_inc(v_a_2442_);
lean_inc_ref(v_a_2441_);
lean_inc(v_a_2440_);
lean_inc_ref(v_a_2439_);
v___x_2464_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_f_2427_, v_g_2428_, v___x_2453_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2466_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2465_);
lean_dec_ref(v___x_2464_);
lean_inc(v_a_2442_);
lean_inc_ref(v_a_2441_);
lean_inc(v_a_2440_);
lean_inc_ref(v_a_2439_);
v___x_2466_ = l_Lean_Meta_mkEqNDRec(v_a_2463_, v_a_2452_, v_a_2465_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2468_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
lean_dec_ref(v___x_2466_);
v___x_2468_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_2467_, v_heq_2432_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
return v___x_2468_;
}
else
{
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
return v___x_2466_;
}
}
else
{
lean_dec(v_a_2463_);
lean_dec(v_a_2452_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
return v___x_2464_;
}
}
else
{
lean_dec(v_a_2452_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_g_2428_);
lean_dec_ref(v_f_2427_);
return v___x_2462_;
}
}
else
{
lean_dec(v_a_2456_);
lean_dec(v_a_2452_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_rhs_2431_);
lean_dec_ref(v_lhs_2430_);
lean_dec(v_numArgs_2429_);
lean_dec_ref(v_g_2428_);
lean_dec_ref(v_f_2427_);
return v___x_2457_;
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec(v_a_2452_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_rhs_2431_);
lean_dec_ref(v_lhs_2430_);
lean_dec(v_numArgs_2429_);
lean_dec_ref(v_g_2428_);
lean_dec_ref(v_f_2427_);
v_a_2469_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2455_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2455_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
else
{
lean_object* v___x_2477_; 
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_rhs_2431_);
lean_dec_ref(v_lhs_2430_);
lean_dec(v_numArgs_2429_);
lean_dec_ref(v_g_2428_);
lean_dec_ref(v_f_2427_);
v___x_2477_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_2452_, v_heq_2432_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
return v___x_2477_;
}
}
else
{
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_rhs_2431_);
lean_dec_ref(v_lhs_2430_);
lean_dec(v_numArgs_2429_);
lean_dec_ref(v_g_2428_);
lean_dec_ref(v_f_2427_);
return v___x_2451_;
}
}
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_rhs_2431_);
lean_dec_ref(v_lhs_2430_);
lean_dec(v_numArgs_2429_);
lean_dec_ref(v_g_2428_);
lean_dec_ref(v_f_2427_);
v_a_2478_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2444_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2444_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1(void){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2487_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2488_ = lean_unsigned_to_nat(27u);
v___x_2489_ = lean_unsigned_to_nat(237u);
v___x_2490_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0));
v___x_2491_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2492_ = l_mkPanicMessageWithDecl(v___x_2491_, v___x_2490_, v___x_2489_, v___x_2488_, v___x_2487_);
return v___x_2492_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2493_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2494_ = lean_unsigned_to_nat(27u);
v___x_2495_ = lean_unsigned_to_nat(236u);
v___x_2496_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0));
v___x_2497_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2498_ = l_mkPanicMessageWithDecl(v___x_2497_, v___x_2496_, v___x_2495_, v___x_2494_, v___x_2493_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(lean_object* v_lhs_2499_, lean_object* v_rhs_2500_, uint8_t v_heq_2501_, lean_object* v_e_u2081_2502_, lean_object* v_e_u2082_2503_, lean_object* v_numArgs_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_){
_start:
{
if (lean_obj_tag(v_e_u2081_2502_) == 5)
{
if (lean_obj_tag(v_e_u2082_2503_) == 5)
{
lean_object* v_fn_2516_; lean_object* v_fn_2517_; lean_object* v___x_2518_; lean_object* v_numArgs_2519_; uint8_t v___x_2520_; 
v_fn_2516_ = lean_ctor_get(v_e_u2081_2502_, 0);
lean_inc_ref(v_fn_2516_);
lean_dec_ref(v_e_u2081_2502_);
v_fn_2517_ = lean_ctor_get(v_e_u2082_2503_, 0);
lean_inc_ref(v_fn_2517_);
lean_dec_ref(v_e_u2082_2503_);
v___x_2518_ = lean_unsigned_to_nat(1u);
v_numArgs_2519_ = lean_nat_add(v_numArgs_2504_, v___x_2518_);
lean_dec(v_numArgs_2504_);
v___x_2520_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_2516_, v_fn_2517_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2521_; 
lean_inc(v_a_2514_);
lean_inc_ref(v_a_2513_);
lean_inc(v_a_2512_);
lean_inc_ref(v_a_2511_);
lean_inc_ref(v_fn_2517_);
lean_inc_ref(v_fn_2516_);
v___x_2521_ = l_Lean_Meta_Grind_hasSameType(v_fn_2516_, v_fn_2517_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; uint8_t v___x_2523_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_a_2522_);
lean_dec_ref(v___x_2521_);
v___x_2523_ = lean_unbox(v_a_2522_);
lean_dec(v_a_2522_);
if (v___x_2523_ == 0)
{
v_e_u2081_2502_ = v_fn_2516_;
v_e_u2082_2503_ = v_fn_2517_;
v_numArgs_2504_ = v_numArgs_2519_;
goto _start;
}
else
{
lean_object* v___x_2525_; 
v___x_2525_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_2516_, v_fn_2517_, v_numArgs_2519_, v_lhs_2499_, v_rhs_2500_, v_heq_2501_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_);
return v___x_2525_;
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec(v_numArgs_2519_);
lean_dec_ref(v_fn_2517_);
lean_dec_ref(v_fn_2516_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec(v_a_2506_);
lean_dec(v_a_2505_);
lean_dec_ref(v_rhs_2500_);
lean_dec_ref(v_lhs_2499_);
v_a_2526_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2521_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2521_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
else
{
lean_object* v___x_2534_; 
v___x_2534_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_2516_, v_fn_2517_, v_numArgs_2519_, v_lhs_2499_, v_rhs_2500_, v_heq_2501_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_);
return v___x_2534_;
}
}
else
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
lean_dec_ref(v_e_u2081_2502_);
lean_dec(v_numArgs_2504_);
lean_dec_ref(v_e_u2082_2503_);
lean_dec_ref(v_rhs_2500_);
lean_dec_ref(v_lhs_2499_);
v___x_2535_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1);
v___x_2536_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2535_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_);
return v___x_2536_;
}
}
else
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
lean_dec(v_numArgs_2504_);
lean_dec_ref(v_e_u2082_2503_);
lean_dec_ref(v_e_u2081_2502_);
lean_dec_ref(v_rhs_2500_);
lean_dec_ref(v_lhs_2499_);
v___x_2537_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2);
v___x_2538_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2537_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_);
return v___x_2538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(lean_object* v_lhs_2539_, lean_object* v_rhs_2540_, uint8_t v_heq_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_rhs_2540_);
lean_inc_ref(v_lhs_2539_);
v___x_2554_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(v_lhs_2539_, v_rhs_2540_, v_heq_2541_, v_lhs_2539_, v_rhs_2540_, v___x_2553_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC___boxed(lean_object* v_lhs_2555_, lean_object* v_rhs_2556_, lean_object* v_heq_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
uint8_t v_heq_boxed_2569_; lean_object* v_res_2570_; 
v_heq_boxed_2569_ = lean_unbox(v_heq_2557_);
v_res_2570_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_2555_, v_rhs_2556_, v_heq_boxed_2569_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___boxed(lean_object* v_lhs_2571_, lean_object* v_rhs_2572_, lean_object* v_heq_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_){
_start:
{
uint8_t v_heq_boxed_2585_; lean_object* v_res_2586_; 
v_heq_boxed_2585_ = lean_unbox(v_heq_2573_);
v_res_2586_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_2571_, v_rhs_2572_, v_heq_boxed_2585_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_);
lean_dec_ref(v_rhs_2572_);
lean_dec_ref(v_lhs_2571_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___boxed(lean_object* v_lhs_2587_, lean_object* v_rhs_2588_, lean_object* v_heq_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_){
_start:
{
uint8_t v_heq_boxed_2601_; lean_object* v_res_2602_; 
v_heq_boxed_2601_ = lean_unbox(v_heq_2589_);
v_res_2602_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_2587_, v_rhs_2588_, v_heq_boxed_2601_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_);
lean_dec_ref(v_rhs_2588_);
lean_dec_ref(v_lhs_2587_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof___boxed(lean_object* v_lhs_2603_, lean_object* v_rhs_2604_, lean_object* v_h_2605_, lean_object* v_flipped_2606_, lean_object* v_heq_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
uint8_t v_flipped_boxed_2619_; uint8_t v_heq_boxed_2620_; lean_object* v_res_2621_; 
v_flipped_boxed_2619_ = lean_unbox(v_flipped_2606_);
v_heq_boxed_2620_ = lean_unbox(v_heq_2607_);
v_res_2621_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_lhs_2603_, v_rhs_2604_, v_h_2605_, v_flipped_boxed_2619_, v_heq_boxed_2620_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___boxed(lean_object* v_lhs_2622_, lean_object* v_rhs_2623_, lean_object* v_heq_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_){
_start:
{
uint8_t v_heq_boxed_2636_; lean_object* v_res_2637_; 
v_heq_boxed_2636_ = lean_unbox(v_heq_2624_);
v_res_2637_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_2622_, v_rhs_2623_, v_heq_boxed_2636_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_);
lean_dec_ref(v_rhs_2623_);
lean_dec_ref(v_lhs_2622_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper___boxed(lean_object* v_thm_2638_, lean_object* v_lhs_2639_, lean_object* v_rhs_2640_, lean_object* v_i_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_2638_, v_lhs_2639_, v_rhs_2640_, v_i_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
lean_dec(v_i_2641_);
lean_dec_ref(v_rhs_2640_);
lean_dec_ref(v_lhs_2639_);
lean_dec_ref(v_thm_2638_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___boxed(lean_object** _args){
lean_object* v_lhs_2654_ = _args[0];
lean_object* v_rhs_2655_ = _args[1];
lean_object* v_heq_2656_ = _args[2];
lean_object* v_e_u2081_2657_ = _args[3];
lean_object* v_e_u2082_2658_ = _args[4];
lean_object* v_numArgs_2659_ = _args[5];
lean_object* v_a_2660_ = _args[6];
lean_object* v_a_2661_ = _args[7];
lean_object* v_a_2662_ = _args[8];
lean_object* v_a_2663_ = _args[9];
lean_object* v_a_2664_ = _args[10];
lean_object* v_a_2665_ = _args[11];
lean_object* v_a_2666_ = _args[12];
lean_object* v_a_2667_ = _args[13];
lean_object* v_a_2668_ = _args[14];
lean_object* v_a_2669_ = _args[15];
lean_object* v_a_2670_ = _args[16];
_start:
{
uint8_t v_heq_boxed_2671_; lean_object* v_res_2672_; 
v_heq_boxed_2671_ = lean_unbox(v_heq_2656_);
v_res_2672_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(v_lhs_2654_, v_rhs_2655_, v_heq_boxed_2671_, v_e_u2081_2657_, v_e_u2082_2658_, v_numArgs_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___boxed(lean_object* v_lhs_2673_, lean_object* v_common_2674_, lean_object* v_acc_2675_, lean_object* v_heq_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_){
_start:
{
uint8_t v_heq_boxed_2688_; lean_object* v_res_2689_; 
v_heq_boxed_2688_ = lean_unbox(v_heq_2676_);
v_res_2689_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_2673_, v_common_2674_, v_acc_2675_, v_heq_boxed_2688_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
lean_dec_ref(v_common_2674_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___boxed(lean_object** _args){
lean_object* v_f_2690_ = _args[0];
lean_object* v_g_2691_ = _args[1];
lean_object* v_numArgs_2692_ = _args[2];
lean_object* v_lhs_2693_ = _args[3];
lean_object* v_rhs_2694_ = _args[4];
lean_object* v_heq_2695_ = _args[5];
lean_object* v_a_2696_ = _args[6];
lean_object* v_a_2697_ = _args[7];
lean_object* v_a_2698_ = _args[8];
lean_object* v_a_2699_ = _args[9];
lean_object* v_a_2700_ = _args[10];
lean_object* v_a_2701_ = _args[11];
lean_object* v_a_2702_ = _args[12];
lean_object* v_a_2703_ = _args[13];
lean_object* v_a_2704_ = _args[14];
lean_object* v_a_2705_ = _args[15];
lean_object* v_a_2706_ = _args[16];
_start:
{
uint8_t v_heq_boxed_2707_; lean_object* v_res_2708_; 
v_heq_boxed_2707_ = lean_unbox(v_heq_2695_);
v_res_2708_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_2690_, v_g_2691_, v_numArgs_2692_, v_lhs_2693_, v_rhs_2694_, v_heq_boxed_2707_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___boxed(lean_object* v_rhs_2709_, lean_object* v_common_2710_, lean_object* v_lhsEqCommon_x3f_2711_, lean_object* v_heq_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_){
_start:
{
uint8_t v_heq_boxed_2724_; lean_object* v_res_2725_; 
v_heq_boxed_2724_ = lean_unbox(v_heq_2712_);
v_res_2725_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_2709_, v_common_2710_, v_lhsEqCommon_x3f_2711_, v_heq_boxed_2724_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_);
lean_dec_ref(v_common_2710_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop___boxed(lean_object* v_lhs_2726_, lean_object* v_rhs_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_2726_, v_rhs_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
lean_dec_ref(v_rhs_2727_);
lean_dec_ref(v_lhs_2726_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___boxed(lean_object* v_lhs_2740_, lean_object* v_rhs_2741_, lean_object* v_heq_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
uint8_t v_heq_boxed_2754_; lean_object* v_res_2755_; 
v_heq_boxed_2754_ = lean_unbox(v_heq_2742_);
v_res_2755_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_2740_, v_rhs_2741_, v_heq_boxed_2754_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___boxed(lean_object* v_lhs_2756_, lean_object* v_rhs_2757_, lean_object* v_heq_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_){
_start:
{
uint8_t v_heq_boxed_2770_; lean_object* v_res_2771_; 
v_heq_boxed_2770_ = lean_unbox(v_heq_2758_);
v_res_2771_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_lhs_2756_, v_rhs_2757_, v_heq_boxed_2770_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrProof___boxed(lean_object* v_lhs_2772_, lean_object* v_rhs_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Lean_Meta_Grind_mkEqCongrProof(v_lhs_2772_, v_rhs_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___boxed(lean_object* v_lhs_2786_, lean_object* v_rhs_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(v_lhs_2786_, v_rhs_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___boxed(lean_object* v_lhs_2800_, lean_object* v_rhs_2801_, lean_object* v_heq_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_){
_start:
{
uint8_t v_heq_boxed_2814_; lean_object* v_res_2815_; 
v_heq_boxed_2814_ = lean_unbox(v_heq_2802_);
v_res_2815_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(v_lhs_2800_, v_rhs_2801_, v_heq_boxed_2814_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(lean_object* v_00_u03b1_2816_, lean_object* v_ref_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_2817_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___boxed(lean_object* v_00_u03b1_2830_, lean_object* v_ref_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(v_00_u03b1_2830_, v_ref_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec(v___y_2832_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(lean_object* v_00_u03b1_2844_, lean_object* v_name_2845_, uint8_t v_bi_2846_, lean_object* v_type_2847_, lean_object* v_k_2848_, uint8_t v_kind_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_2845_, v_bi_2846_, v_type_2847_, v_k_2848_, v_kind_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___boxed(lean_object** _args){
lean_object* v_00_u03b1_2862_ = _args[0];
lean_object* v_name_2863_ = _args[1];
lean_object* v_bi_2864_ = _args[2];
lean_object* v_type_2865_ = _args[3];
lean_object* v_k_2866_ = _args[4];
lean_object* v_kind_2867_ = _args[5];
lean_object* v___y_2868_ = _args[6];
lean_object* v___y_2869_ = _args[7];
lean_object* v___y_2870_ = _args[8];
lean_object* v___y_2871_ = _args[9];
lean_object* v___y_2872_ = _args[10];
lean_object* v___y_2873_ = _args[11];
lean_object* v___y_2874_ = _args[12];
lean_object* v___y_2875_ = _args[13];
lean_object* v___y_2876_ = _args[14];
lean_object* v___y_2877_ = _args[15];
lean_object* v___y_2878_ = _args[16];
_start:
{
uint8_t v_bi_boxed_2879_; uint8_t v_kind_boxed_2880_; lean_object* v_res_2881_; 
v_bi_boxed_2879_ = lean_unbox(v_bi_2864_);
v_kind_boxed_2880_ = lean_unbox(v_kind_2867_);
v_res_2881_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(v_00_u03b1_2862_, v_name_2863_, v_bi_boxed_2879_, v_type_2865_, v_k_2866_, v_kind_boxed_2880_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(lean_object* v_00_u03b1_2882_, lean_object* v_name_2883_, lean_object* v_type_2884_, lean_object* v_k_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_name_2883_, v_type_2884_, v_k_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___boxed(lean_object* v_00_u03b1_2898_, lean_object* v_name_2899_, lean_object* v_type_2900_, lean_object* v_k_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(v_00_u03b1_2898_, v_name_2899_, v_type_2900_, v_k_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(lean_object* v_00_u03b1_2914_, lean_object* v_msg_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v___x_2927_; 
v___x_2927_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v_msg_2915_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___boxed(lean_object* v_00_u03b1_2928_, lean_object* v_msg_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(v_00_u03b1_2928_, v_msg_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec(v___y_2930_);
return v_res_2941_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__1(void){
_start:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2943_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__0));
v___x_2944_ = l_Lean_stringToMessageData(v___x_2943_);
return v___x_2944_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__3(void){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2946_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__2));
v___x_2947_ = l_Lean_stringToMessageData(v___x_2946_);
return v___x_2947_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__5(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__4));
v___x_2950_ = l_Lean_stringToMessageData(v___x_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* lean_grind_mk_eq_proof(lean_object* v_a_2951_, lean_object* v_b_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_){
_start:
{
lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___x_2977_; 
lean_inc(v_a_2962_);
lean_inc_ref(v_a_2961_);
lean_inc(v_a_2960_);
lean_inc_ref(v_a_2959_);
lean_inc_ref(v_b_2952_);
lean_inc_ref(v_a_2951_);
v___x_2977_ = l_Lean_Meta_Grind_hasSameType(v_a_2951_, v_b_2952_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; uint8_t v___x_2979_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref(v___x_2977_);
v___x_2979_ = lean_unbox(v_a_2978_);
lean_dec(v_a_2978_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; 
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec(v_a_2954_);
lean_dec(v_a_2953_);
lean_inc(v_a_2962_);
lean_inc_ref(v_a_2961_);
lean_inc(v_a_2960_);
lean_inc_ref(v_a_2959_);
lean_inc_ref(v_a_2951_);
v___x_2980_ = lean_infer_type(v_a_2951_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2982_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref(v___x_2980_);
lean_inc(v_a_2962_);
lean_inc_ref(v_a_2961_);
lean_inc(v_a_2960_);
lean_inc_ref(v_a_2959_);
lean_inc_ref(v_b_2952_);
v___x_2982_ = lean_infer_type(v_b_2952_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref(v___x_2982_);
v___x_2984_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__1, &l_Lean_Meta_Grind_mkEqProofImpl___closed__1_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__1);
v___x_2985_ = l_Lean_indentExpr(v_a_2951_);
v___x_2986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2984_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
v___x_2987_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__3, &l_Lean_Meta_Grind_mkEqProofImpl___closed__3_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__3);
v___x_2988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2986_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
v___x_2989_ = l_Lean_indentExpr(v_a_2981_);
v___x_2990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2988_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
v___x_2991_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__5, &l_Lean_Meta_Grind_mkEqProofImpl___closed__5_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__5);
v___x_2992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2990_);
lean_ctor_set(v___x_2992_, 1, v___x_2991_);
v___x_2993_ = l_Lean_indentExpr(v_b_2952_);
v___x_2994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2992_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
v___x_2995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2994_);
lean_ctor_set(v___x_2995_, 1, v___x_2987_);
v___x_2996_ = l_Lean_indentExpr(v_a_2983_);
v___x_2997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2995_);
lean_ctor_set(v___x_2997_, 1, v___x_2996_);
v___x_2998_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v___x_2997_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_);
lean_dec(v_a_2962_);
lean_dec_ref(v_a_2961_);
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2998_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2998_);
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
else
{
lean_dec(v_a_2981_);
lean_dec(v_a_2962_);
lean_dec_ref(v_a_2961_);
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
lean_dec_ref(v_b_2952_);
lean_dec_ref(v_a_2951_);
return v___x_2982_;
}
}
else
{
lean_dec(v_a_2962_);
lean_dec_ref(v_a_2961_);
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
lean_dec_ref(v_b_2952_);
lean_dec_ref(v_a_2951_);
return v___x_2980_;
}
}
else
{
v___y_2965_ = v_a_2953_;
v___y_2966_ = v_a_2954_;
v___y_2967_ = v_a_2955_;
v___y_2968_ = v_a_2956_;
v___y_2969_ = v_a_2957_;
v___y_2970_ = v_a_2958_;
v___y_2971_ = v_a_2959_;
v___y_2972_ = v_a_2960_;
v___y_2973_ = v_a_2961_;
v___y_2974_ = v_a_2962_;
goto v___jp_2964_;
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_dec(v_a_2962_);
lean_dec_ref(v_a_2961_);
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec(v_a_2954_);
lean_dec(v_a_2953_);
lean_dec_ref(v_b_2952_);
lean_dec_ref(v_a_2951_);
v_a_3007_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2977_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2977_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
v___jp_2964_:
{
uint8_t v___x_2975_; lean_object* v___x_2976_; 
v___x_2975_ = 0;
v___x_2976_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_2951_, v_b_2952_, v___x_2975_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
return v___x_2976_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqProofImpl___boxed(lean_object* v_a_3015_, lean_object* v_b_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = lean_grind_mk_eq_proof(v_a_3015_, v_b_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* lean_grind_mk_heq_proof(lean_object* v_a_3029_, lean_object* v_b_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_){
_start:
{
uint8_t v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = 1;
v___x_3043_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_3029_, v_b_3030_, v___x_3042_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHEqProofImpl___boxed(lean_object* v_a_3044_, lean_object* v_b_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = lean_grind_mk_heq_proof(v_a_3044_, v_b_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
return v_res_3057_;
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
