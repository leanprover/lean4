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
v___x_8578__overap_216_ = lean_panic_fn(v___x_215_, v_msg_203_);
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
v___x_9377__overap_245_ = lean_panic_fn(v___x_244_, v_msg_232_);
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
lean_object* v___x_943_; lean_object* v___x_124900__overap_944_; lean_object* v___x_945_; 
v___x_943_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0);
v___x_124900__overap_944_ = lean_panic_fn(v___x_943_, v_msg_931_);
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
v___x_945_ = lean_apply_11(v___x_124900__overap_944_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, lean_box(0));
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
uint8_t v___x_132762__boxed_1131_; uint8_t v___x_132763__boxed_1132_; lean_object* v_res_1133_; 
v___x_132762__boxed_1131_ = lean_unbox(v___x_1117_);
v___x_132763__boxed_1132_ = lean_unbox(v___x_1118_);
v_res_1133_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0(v_numArgs_1114_, v_rhs_1115_, v_lhs_1116_, v___x_132762__boxed_1131_, v___x_132763__boxed_1132_, v_x_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
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
lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v_fileName_1313_; lean_object* v_fileMap_1314_; lean_object* v_options_1315_; lean_object* v_currRecDepth_1316_; lean_object* v_maxRecDepth_1317_; lean_object* v_ref_1318_; lean_object* v_currNamespace_1319_; lean_object* v_openDecls_1320_; lean_object* v_initHeartbeats_1321_; lean_object* v_maxHeartbeats_1322_; lean_object* v_quotContext_1323_; lean_object* v_currMacroScope_1324_; uint8_t v_diag_1325_; lean_object* v_cancelTk_x3f_1326_; uint8_t v_suppressElabErrors_1327_; lean_object* v_inheritedTraceOptions_1328_; uint8_t v___x_1329_; 
v_fileName_1313_ = lean_ctor_get(v_a_1284_, 0);
lean_inc_ref(v_fileName_1313_);
v_fileMap_1314_ = lean_ctor_get(v_a_1284_, 1);
lean_inc_ref(v_fileMap_1314_);
v_options_1315_ = lean_ctor_get(v_a_1284_, 2);
lean_inc_ref(v_options_1315_);
v_currRecDepth_1316_ = lean_ctor_get(v_a_1284_, 3);
lean_inc(v_currRecDepth_1316_);
v_maxRecDepth_1317_ = lean_ctor_get(v_a_1284_, 4);
lean_inc(v_maxRecDepth_1317_);
v_ref_1318_ = lean_ctor_get(v_a_1284_, 5);
lean_inc(v_ref_1318_);
v_currNamespace_1319_ = lean_ctor_get(v_a_1284_, 6);
lean_inc(v_currNamespace_1319_);
v_openDecls_1320_ = lean_ctor_get(v_a_1284_, 7);
lean_inc(v_openDecls_1320_);
v_initHeartbeats_1321_ = lean_ctor_get(v_a_1284_, 8);
lean_inc(v_initHeartbeats_1321_);
v_maxHeartbeats_1322_ = lean_ctor_get(v_a_1284_, 9);
lean_inc(v_maxHeartbeats_1322_);
v_quotContext_1323_ = lean_ctor_get(v_a_1284_, 10);
lean_inc(v_quotContext_1323_);
v_currMacroScope_1324_ = lean_ctor_get(v_a_1284_, 11);
lean_inc(v_currMacroScope_1324_);
v_diag_1325_ = lean_ctor_get_uint8(v_a_1284_, sizeof(void*)*14);
v_cancelTk_x3f_1326_ = lean_ctor_get(v_a_1284_, 12);
lean_inc(v_cancelTk_x3f_1326_);
v_suppressElabErrors_1327_ = lean_ctor_get_uint8(v_a_1284_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1328_ = lean_ctor_get(v_a_1284_, 13);
lean_inc_ref(v_inheritedTraceOptions_1328_);
lean_dec_ref(v_a_1284_);
v___x_1329_ = lean_nat_dec_eq(v_currRecDepth_1316_, v_maxRecDepth_1317_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; uint8_t v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1330_ = l_Lean_Expr_cleanupAnnotations(v_lhs_1274_);
v___x_1331_ = l_Lean_Expr_isApp(v___x_1330_);
v___x_1332_ = lean_unsigned_to_nat(1u);
v___x_1333_ = lean_nat_add(v_currRecDepth_1316_, v___x_1332_);
lean_dec(v_currRecDepth_1316_);
v___x_1334_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1334_, 0, v_fileName_1313_);
lean_ctor_set(v___x_1334_, 1, v_fileMap_1314_);
lean_ctor_set(v___x_1334_, 2, v_options_1315_);
lean_ctor_set(v___x_1334_, 3, v___x_1333_);
lean_ctor_set(v___x_1334_, 4, v_maxRecDepth_1317_);
lean_ctor_set(v___x_1334_, 5, v_ref_1318_);
lean_ctor_set(v___x_1334_, 6, v_currNamespace_1319_);
lean_ctor_set(v___x_1334_, 7, v_openDecls_1320_);
lean_ctor_set(v___x_1334_, 8, v_initHeartbeats_1321_);
lean_ctor_set(v___x_1334_, 9, v_maxHeartbeats_1322_);
lean_ctor_set(v___x_1334_, 10, v_quotContext_1323_);
lean_ctor_set(v___x_1334_, 11, v_currMacroScope_1324_);
lean_ctor_set(v___x_1334_, 12, v_cancelTk_x3f_1326_);
lean_ctor_set(v___x_1334_, 13, v_inheritedTraceOptions_1328_);
lean_ctor_set_uint8(v___x_1334_, sizeof(void*)*14, v_diag_1325_);
lean_ctor_set_uint8(v___x_1334_, sizeof(void*)*14 + 1, v_suppressElabErrors_1327_);
if (v___x_1331_ == 0)
{
lean_dec_ref(v___x_1330_);
lean_dec_ref(v_rhs_1275_);
v___y_1301_ = v_a_1276_;
v___y_1302_ = v_a_1277_;
v___y_1303_ = v_a_1278_;
v___y_1304_ = v_a_1279_;
v___y_1305_ = v_a_1280_;
v___y_1306_ = v_a_1281_;
v___y_1307_ = v_a_1282_;
v___y_1308_ = v_a_1283_;
v___y_1309_ = v___x_1334_;
v___y_1310_ = v_a_1285_;
goto v___jp_1300_;
}
else
{
lean_object* v_arg_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v_arg_1335_ = lean_ctor_get(v___x_1330_, 1);
lean_inc_ref(v_arg_1335_);
v___x_1336_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1330_);
v___x_1337_ = l_Lean_Expr_isApp(v___x_1336_);
if (v___x_1337_ == 0)
{
lean_dec_ref(v___x_1336_);
lean_dec_ref(v_arg_1335_);
lean_dec_ref(v_rhs_1275_);
v___y_1301_ = v_a_1276_;
v___y_1302_ = v_a_1277_;
v___y_1303_ = v_a_1278_;
v___y_1304_ = v_a_1279_;
v___y_1305_ = v_a_1280_;
v___y_1306_ = v_a_1281_;
v___y_1307_ = v_a_1282_;
v___y_1308_ = v_a_1283_;
v___y_1309_ = v___x_1334_;
v___y_1310_ = v_a_1285_;
goto v___jp_1300_;
}
else
{
lean_object* v_arg_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
v_arg_1338_ = lean_ctor_get(v___x_1336_, 1);
lean_inc_ref(v_arg_1338_);
v___x_1339_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1336_);
v___x_1340_ = l_Lean_Expr_isApp(v___x_1339_);
if (v___x_1340_ == 0)
{
lean_dec_ref(v___x_1339_);
lean_dec_ref(v_arg_1338_);
lean_dec_ref(v_arg_1335_);
lean_dec_ref(v_rhs_1275_);
v___y_1301_ = v_a_1276_;
v___y_1302_ = v_a_1277_;
v___y_1303_ = v_a_1278_;
v___y_1304_ = v_a_1279_;
v___y_1305_ = v_a_1280_;
v___y_1306_ = v_a_1281_;
v___y_1307_ = v_a_1282_;
v___y_1308_ = v_a_1283_;
v___y_1309_ = v___x_1334_;
v___y_1310_ = v_a_1285_;
goto v___jp_1300_;
}
else
{
lean_object* v_arg_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v_arg_1341_ = lean_ctor_get(v___x_1339_, 1);
lean_inc_ref(v_arg_1341_);
v___x_1342_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1339_);
v___x_1343_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_1344_ = l_Lean_Expr_isConstOf(v___x_1342_, v___x_1343_);
if (v___x_1344_ == 0)
{
lean_dec_ref(v___x_1342_);
lean_dec_ref(v_arg_1341_);
lean_dec_ref(v_arg_1338_);
lean_dec_ref(v_arg_1335_);
lean_dec_ref(v_rhs_1275_);
v___y_1301_ = v_a_1276_;
v___y_1302_ = v_a_1277_;
v___y_1303_ = v_a_1278_;
v___y_1304_ = v_a_1279_;
v___y_1305_ = v_a_1280_;
v___y_1306_ = v_a_1281_;
v___y_1307_ = v_a_1282_;
v___y_1308_ = v_a_1283_;
v___y_1309_ = v___x_1334_;
v___y_1310_ = v_a_1285_;
goto v___jp_1300_;
}
else
{
lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1345_ = l_Lean_Expr_cleanupAnnotations(v_rhs_1275_);
v___x_1346_ = l_Lean_Expr_isApp(v___x_1345_);
if (v___x_1346_ == 0)
{
lean_dec_ref(v___x_1345_);
lean_dec_ref(v___x_1342_);
lean_dec_ref(v_arg_1341_);
lean_dec_ref(v_arg_1338_);
lean_dec_ref(v_arg_1335_);
v___y_1288_ = v_a_1276_;
v___y_1289_ = v_a_1277_;
v___y_1290_ = v_a_1278_;
v___y_1291_ = v_a_1279_;
v___y_1292_ = v_a_1280_;
v___y_1293_ = v_a_1281_;
v___y_1294_ = v_a_1282_;
v___y_1295_ = v_a_1283_;
v___y_1296_ = v___x_1334_;
v___y_1297_ = v_a_1285_;
goto v___jp_1287_;
}
else
{
lean_object* v_arg_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v_arg_1347_ = lean_ctor_get(v___x_1345_, 1);
lean_inc_ref(v_arg_1347_);
v___x_1348_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1345_);
v___x_1349_ = l_Lean_Expr_isApp(v___x_1348_);
if (v___x_1349_ == 0)
{
lean_dec_ref(v___x_1348_);
lean_dec_ref(v_arg_1347_);
lean_dec_ref(v___x_1342_);
lean_dec_ref(v_arg_1341_);
lean_dec_ref(v_arg_1338_);
lean_dec_ref(v_arg_1335_);
v___y_1288_ = v_a_1276_;
v___y_1289_ = v_a_1277_;
v___y_1290_ = v_a_1278_;
v___y_1291_ = v_a_1279_;
v___y_1292_ = v_a_1280_;
v___y_1293_ = v_a_1281_;
v___y_1294_ = v_a_1282_;
v___y_1295_ = v_a_1283_;
v___y_1296_ = v___x_1334_;
v___y_1297_ = v_a_1285_;
goto v___jp_1287_;
}
else
{
lean_object* v_arg_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v_arg_1350_ = lean_ctor_get(v___x_1348_, 1);
lean_inc_ref(v_arg_1350_);
v___x_1351_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1348_);
v___x_1352_ = l_Lean_Expr_isApp(v___x_1351_);
if (v___x_1352_ == 0)
{
lean_dec_ref(v___x_1351_);
lean_dec_ref(v_arg_1350_);
lean_dec_ref(v_arg_1347_);
lean_dec_ref(v___x_1342_);
lean_dec_ref(v_arg_1341_);
lean_dec_ref(v_arg_1338_);
lean_dec_ref(v_arg_1335_);
v___y_1288_ = v_a_1276_;
v___y_1289_ = v_a_1277_;
v___y_1290_ = v_a_1278_;
v___y_1291_ = v_a_1279_;
v___y_1292_ = v_a_1280_;
v___y_1293_ = v_a_1281_;
v___y_1294_ = v_a_1282_;
v___y_1295_ = v_a_1283_;
v___y_1296_ = v___x_1334_;
v___y_1297_ = v_a_1285_;
goto v___jp_1287_;
}
else
{
lean_object* v_arg_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v_arg_1353_ = lean_ctor_get(v___x_1351_, 1);
lean_inc_ref(v_arg_1353_);
v___x_1354_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1351_);
v___x_1355_ = l_Lean_Expr_isConstOf(v___x_1354_, v___x_1343_);
lean_dec_ref(v___x_1354_);
if (v___x_1355_ == 0)
{
lean_dec_ref(v_arg_1353_);
lean_dec_ref(v_arg_1350_);
lean_dec_ref(v_arg_1347_);
lean_dec_ref(v___x_1342_);
lean_dec_ref(v_arg_1341_);
lean_dec_ref(v_arg_1338_);
lean_dec_ref(v_arg_1335_);
v___y_1288_ = v_a_1276_;
v___y_1289_ = v_a_1277_;
v___y_1290_ = v_a_1278_;
v___y_1291_ = v_a_1279_;
v___y_1292_ = v_a_1280_;
v___y_1293_ = v_a_1281_;
v___y_1294_ = v_a_1282_;
v___y_1295_ = v_a_1283_;
v___y_1296_ = v___x_1334_;
v___y_1297_ = v_a_1285_;
goto v___jp_1287_;
}
else
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___y_1359_; uint8_t v___y_1375_; uint8_t v___x_1394_; 
v___x_1356_ = lean_st_ref_get(v_a_1276_);
v___x_1357_ = lean_st_ref_get(v_a_1276_);
v___x_1394_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1356_, v_arg_1338_, v_arg_1347_);
if (v___x_1394_ == 0)
{
lean_dec(v___x_1357_);
v___y_1375_ = v___x_1394_;
goto v___jp_1374_;
}
else
{
uint8_t v___x_1395_; 
v___x_1395_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1357_, v_arg_1335_, v_arg_1350_);
v___y_1375_ = v___x_1395_;
goto v___jp_1374_;
}
v___jp_1358_:
{
lean_object* v___x_1360_; 
lean_inc_ref(v_arg_1347_);
lean_inc_ref(v_arg_1338_);
v___x_1360_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1338_, v_arg_1347_, v___x_1355_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v___x_1334_, v_a_1285_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1362_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref(v___x_1360_);
lean_inc_ref(v_arg_1350_);
lean_inc_ref(v_arg_1335_);
v___x_1362_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1335_, v_arg_1350_, v___x_1355_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v___x_1334_, v_a_1285_);
lean_dec_ref(v___x_1334_);
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
v___x_1367_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4));
v___x_1368_ = l_Lean_mkConst(v___x_1367_, v___y_1359_);
v___x_1369_ = l_Lean_mkApp8(v___x_1368_, v_arg_1341_, v_arg_1353_, v_arg_1338_, v_arg_1335_, v_arg_1350_, v_arg_1347_, v_a_1361_, v_a_1363_);
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
lean_dec(v___y_1359_);
lean_dec_ref(v_arg_1353_);
lean_dec_ref(v_arg_1350_);
lean_dec_ref(v_arg_1347_);
lean_dec_ref(v_arg_1341_);
lean_dec_ref(v_arg_1338_);
lean_dec_ref(v_arg_1335_);
return v___x_1362_;
}
}
else
{
lean_dec(v___y_1359_);
lean_dec_ref(v_arg_1353_);
lean_dec_ref(v_arg_1350_);
lean_dec_ref(v_arg_1347_);
lean_dec_ref(v_arg_1341_);
lean_dec_ref(v_arg_1338_);
lean_dec_ref(v_arg_1335_);
lean_dec_ref(v___x_1334_);
return v___x_1360_;
}
}
v___jp_1374_:
{
if (v___y_1375_ == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec_ref(v_arg_1353_);
lean_dec_ref(v_arg_1350_);
lean_dec_ref(v_arg_1347_);
lean_dec_ref(v___x_1342_);
lean_dec_ref(v_arg_1341_);
lean_dec_ref(v_arg_1338_);
lean_dec_ref(v_arg_1335_);
v___x_1376_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6, &l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6_once, _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6);
v___x_1377_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1376_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v___x_1334_, v_a_1285_);
lean_dec_ref(v___x_1334_);
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1378_ = l_Lean_Expr_constLevels_x21(v___x_1342_);
lean_dec_ref(v___x_1342_);
v___x_1379_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1341_, v_arg_1353_);
if (v___x_1379_ == 0)
{
v___y_1359_ = v___x_1378_;
goto v___jp_1358_;
}
else
{
if (v___x_1329_ == 0)
{
lean_object* v___x_1380_; 
lean_dec_ref(v_arg_1353_);
lean_inc_ref(v_arg_1347_);
lean_inc_ref(v_arg_1338_);
v___x_1380_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1338_, v_arg_1347_, v___x_1329_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v___x_1334_, v_a_1285_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1382_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
lean_dec_ref(v___x_1380_);
lean_inc_ref(v_arg_1350_);
lean_inc_ref(v_arg_1335_);
v___x_1382_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1335_, v_arg_1350_, v___x_1329_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v___x_1334_, v_a_1285_);
lean_dec_ref(v___x_1334_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1393_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1393_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1393_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1387_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8));
v___x_1388_ = l_Lean_mkConst(v___x_1387_, v___x_1378_);
v___x_1389_ = l_Lean_mkApp7(v___x_1388_, v_arg_1341_, v_arg_1338_, v_arg_1335_, v_arg_1350_, v_arg_1347_, v_a_1381_, v_a_1383_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1389_);
v___x_1391_ = v___x_1385_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
else
{
lean_dec(v_a_1381_);
lean_dec(v___x_1378_);
lean_dec_ref(v_arg_1350_);
lean_dec_ref(v_arg_1347_);
lean_dec_ref(v_arg_1341_);
lean_dec_ref(v_arg_1338_);
lean_dec_ref(v_arg_1335_);
return v___x_1382_;
}
}
else
{
lean_dec(v___x_1378_);
lean_dec_ref(v_arg_1350_);
lean_dec_ref(v_arg_1347_);
lean_dec_ref(v_arg_1341_);
lean_dec_ref(v_arg_1338_);
lean_dec_ref(v_arg_1335_);
lean_dec_ref(v___x_1334_);
return v___x_1380_;
}
}
else
{
v___y_1359_ = v___x_1378_;
goto v___jp_1358_;
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
lean_object* v___x_1396_; 
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
lean_dec_ref(v_rhs_1275_);
lean_dec_ref(v_lhs_1274_);
v___x_1396_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1318_);
return v___x_1396_;
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
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2(void){
_start:
{
uint8_t v___x_1400_; uint64_t v___x_1401_; 
v___x_1400_ = 1;
v___x_1401_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1400_);
return v___x_1401_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1403_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_1404_ = lean_unsigned_to_nat(38u);
v___x_1405_ = lean_unsigned_to_nat(250u);
v___x_1406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3));
v___x_1407_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1408_ = l_mkPanicMessageWithDecl(v___x_1407_, v___x_1406_, v___x_1405_, v___x_1404_, v___x_1403_);
return v___x_1408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6(void){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5));
v___x_1411_ = lean_unsigned_to_nat(6u);
v___x_1412_ = lean_unsigned_to_nat(260u);
v___x_1413_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3));
v___x_1414_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1415_ = l_mkPanicMessageWithDecl(v___x_1414_, v___x_1413_, v___x_1412_, v___x_1411_, v___x_1410_);
return v___x_1415_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__1));
v___x_1419_ = lean_unsigned_to_nat(4u);
v___x_1420_ = lean_unsigned_to_nat(219u);
v___x_1421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__0));
v___x_1422_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1423_ = l_mkPanicMessageWithDecl(v___x_1422_, v___x_1421_, v___x_1420_, v___x_1419_, v___x_1418_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(lean_object* v_lhs_1424_, lean_object* v_rhs_1425_, uint8_t v_heq_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v_numArgs_1438_; lean_object* v___x_1439_; uint8_t v___x_1440_; 
v_numArgs_1438_ = l_Lean_Expr_getAppNumArgs(v_lhs_1424_);
v___x_1439_ = l_Lean_Expr_getAppNumArgs(v_rhs_1425_);
v___x_1440_ = lean_nat_dec_eq(v___x_1439_, v_numArgs_1438_);
lean_dec(v___x_1439_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_dec(v_numArgs_1438_);
lean_dec_ref(v_rhs_1425_);
lean_dec_ref(v_lhs_1424_);
v___x_1441_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2);
v___x_1442_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1441_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
return v___x_1442_;
}
else
{
lean_object* v_f_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v_f_1443_ = l_Lean_Expr_getAppFn(v_lhs_1424_);
v___x_1444_ = lean_box(0);
lean_inc_ref(v_f_1443_);
v___x_1445_ = l_Lean_Meta_getFunInfo(v_f_1443_, v___x_1444_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
lean_dec_ref(v___x_1445_);
v___x_1447_ = l_Lean_Meta_FunInfo_getArity(v_a_1446_);
lean_dec(v_a_1446_);
v___x_1448_ = lean_nat_dec_lt(v___x_1447_, v_numArgs_1438_);
lean_dec(v___x_1447_);
if (v___x_1448_ == 0)
{
lean_object* v_g_1449_; lean_object* v___x_1450_; 
v_g_1449_ = l_Lean_Expr_getAppFn(v_rhs_1425_);
v___x_1450_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_1443_, v_g_1449_, v_numArgs_1438_, v_lhs_1424_, v_rhs_1425_, v_heq_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
return v___x_1450_;
}
else
{
lean_object* v___x_1451_; 
lean_dec_ref(v_f_1443_);
lean_dec(v_numArgs_1438_);
lean_inc_ref(v_lhs_1424_);
v___x_1451_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(v_lhs_1424_, v_rhs_1425_);
if (lean_obj_tag(v___x_1451_) == 1)
{
lean_object* v_val_1452_; lean_object* v_fst_1453_; lean_object* v_snd_1454_; lean_object* v___y_1456_; lean_object* v___x_1469_; 
v_val_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_val_1452_);
lean_dec_ref(v___x_1451_);
v_fst_1453_ = lean_ctor_get(v_val_1452_, 0);
lean_inc(v_fst_1453_);
v_snd_1454_ = lean_ctor_get(v_val_1452_, 1);
lean_inc(v_snd_1454_);
lean_dec(v_val_1452_);
lean_inc(v_snd_1454_);
v___x_1469_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(v_fst_1453_, v_snd_1454_, v_a_1430_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
if (lean_obj_tag(v___x_1469_) == 0)
{
v___y_1456_ = v___x_1469_;
goto v___jp_1455_;
}
else
{
lean_object* v_a_1470_; uint8_t v___y_1472_; uint8_t v___x_1474_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
v___x_1474_ = l_Lean_Exception_isInterrupt(v_a_1470_);
if (v___x_1474_ == 0)
{
uint8_t v___x_1475_; 
v___x_1475_ = l_Lean_Exception_isRuntime(v_a_1470_);
v___y_1472_ = v___x_1475_;
goto v___jp_1471_;
}
else
{
lean_dec(v_a_1470_);
v___y_1472_ = v___x_1474_;
goto v___jp_1471_;
}
v___jp_1471_:
{
if (v___y_1472_ == 0)
{
lean_object* v___x_1473_; 
lean_dec_ref(v___x_1469_);
lean_inc_ref(v_rhs_1425_);
lean_inc_ref(v_lhs_1424_);
v___x_1473_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1424_, v_rhs_1425_, lean_box(0), v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
v___y_1456_ = v___x_1473_;
goto v___jp_1455_;
}
else
{
v___y_1456_ = v___x_1469_;
goto v___jp_1455_;
}
}
}
v___jp_1455_:
{
if (lean_obj_tag(v___y_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; 
v_a_1457_ = lean_ctor_get(v___y_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref(v___y_1456_);
v___x_1458_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_1457_, v_lhs_1424_, v_rhs_1425_, v_snd_1454_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
lean_dec(v_snd_1454_);
lean_dec_ref(v_rhs_1425_);
lean_dec_ref(v_lhs_1424_);
lean_dec(v_a_1457_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1460_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref(v___x_1458_);
v___x_1460_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_1459_, v_heq_1426_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
return v___x_1460_;
}
else
{
return v___x_1458_;
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec(v_snd_1454_);
lean_dec_ref(v_rhs_1425_);
lean_dec_ref(v_lhs_1424_);
v_a_1461_ = lean_ctor_get(v___y_1456_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___y_1456_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___y_1456_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___y_1456_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
else
{
lean_object* v___x_1476_; 
lean_dec(v___x_1451_);
v___x_1476_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_1424_, v_rhs_1425_, lean_box(0), v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
return v___x_1476_;
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec_ref(v_f_1443_);
lean_dec(v_numArgs_1438_);
lean_dec_ref(v_rhs_1425_);
lean_dec_ref(v_lhs_1424_);
v_a_1477_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1445_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1445_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(lean_object* v_lhs_1485_, lean_object* v_rhs_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
uint8_t v___x_1498_; 
v___x_1498_ = l_Lean_Expr_isApp(v_lhs_1485_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = lean_box(0);
v___x_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
return v___x_1500_;
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1501_ = l_Lean_Expr_appFn_x21(v_lhs_1485_);
v___x_1502_ = l_Lean_Expr_appFn_x21(v_rhs_1486_);
v___x_1503_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v___x_1501_, v___x_1502_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
lean_dec_ref(v___x_1502_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1599_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1599_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1599_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v_a_u2081_1508_; lean_object* v_a_u2082_1509_; 
v_a_u2081_1508_ = l_Lean_Expr_appArg_x21(v_lhs_1485_);
v_a_u2082_1509_ = l_Lean_Expr_appArg_x21(v_rhs_1486_);
if (lean_obj_tag(v_a_1504_) == 1)
{
lean_object* v_val_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1565_; 
lean_del_object(v___x_1506_);
lean_dec_ref(v___x_1501_);
v_val_1510_ = lean_ctor_get(v_a_1504_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_a_1504_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1512_ = v_a_1504_;
v_isShared_1513_ = v_isSharedCheck_1565_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_val_1510_);
lean_dec(v_a_1504_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1565_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
uint8_t v___x_1514_; 
v___x_1514_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_u2081_1508_, v_a_u2082_1509_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; 
v___x_1515_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_1508_, v_a_u2082_1509_, v___x_1514_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1517_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref(v___x_1515_);
v___x_1517_ = l_Lean_Meta_mkCongr(v_val_1510_, v_a_1516_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1528_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1520_ = v___x_1517_;
v_isShared_1521_ = v_isSharedCheck_1528_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1528_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v_a_1518_);
v___x_1523_ = v___x_1512_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1525_; 
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1523_);
v___x_1525_ = v___x_1520_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
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
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
lean_del_object(v___x_1512_);
v_a_1529_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1517_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1517_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_del_object(v___x_1512_);
lean_dec(v_val_1510_);
v_a_1537_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1515_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1515_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
else
{
lean_object* v___x_1545_; 
lean_dec_ref(v_a_u2082_1509_);
v___x_1545_ = l_Lean_Meta_mkCongrFun(v_val_1510_, v_a_u2081_1508_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1556_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1556_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1556_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v_a_1546_);
v___x_1551_ = v___x_1512_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1553_; 
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v___x_1551_);
v___x_1553_ = v___x_1548_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
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
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_del_object(v___x_1512_);
v_a_1557_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1545_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1545_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
}
else
{
uint8_t v___x_1566_; 
lean_dec(v_a_1504_);
v___x_1566_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_u2081_1508_, v_a_u2082_1509_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; 
lean_del_object(v___x_1506_);
v___x_1567_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_1508_, v_a_u2082_1509_, v___x_1566_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1569_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref(v___x_1567_);
v___x_1569_ = l_Lean_Meta_mkCongrArg(v___x_1501_, v_a_1568_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1578_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1572_ = v___x_1569_;
v_isShared_1573_ = v_isSharedCheck_1578_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1578_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1574_, 0, v_a_1570_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v___x_1574_);
v___x_1576_ = v___x_1572_;
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
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
v_a_1579_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1569_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1569_);
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
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec_ref(v___x_1501_);
v_a_1587_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1567_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1567_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
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
lean_object* v___x_1595_; lean_object* v___x_1597_; 
lean_dec_ref(v_a_u2082_1509_);
lean_dec_ref(v_a_u2081_1508_);
lean_dec_ref(v___x_1501_);
v___x_1595_ = lean_box(0);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1595_);
v___x_1597_ = v___x_1506_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1501_);
return v___x_1503_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3(void){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1603_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__2));
v___x_1604_ = lean_unsigned_to_nat(14u);
v___x_1605_ = lean_unsigned_to_nat(22u);
v___x_1606_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__1));
v___x_1607_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__0));
v___x_1608_ = l_mkPanicMessageWithDecl(v___x_1607_, v___x_1606_, v___x_1605_, v___x_1604_, v___x_1603_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(lean_object* v_lhs_1609_, lean_object* v_rhs_1610_, uint8_t v_heq_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_1609_, v_rhs_1610_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1637_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1637_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1637_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___y_1629_; 
if (lean_obj_tag(v_a_1624_) == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3);
v___x_1635_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_spec__13(v___x_1634_);
v___y_1629_ = v___x_1635_;
goto v___jp_1628_;
}
else
{
lean_object* v_val_1636_; 
v_val_1636_ = lean_ctor_get(v_a_1624_, 0);
lean_inc(v_val_1636_);
lean_dec_ref(v_a_1624_);
v___y_1629_ = v_val_1636_;
goto v___jp_1628_;
}
v___jp_1628_:
{
if (v_heq_1611_ == 0)
{
lean_object* v___x_1631_; 
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v___y_1629_);
v___x_1631_ = v___x_1626_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___y_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
else
{
lean_object* v___x_1633_; 
lean_del_object(v___x_1626_);
v___x_1633_ = l_Lean_Meta_mkHEqOfEq(v___y_1629_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
return v___x_1633_;
}
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
v_a_1638_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1623_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1623_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__1(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1647_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_1648_ = lean_unsigned_to_nat(34u);
v___x_1649_ = lean_unsigned_to_nat(144u);
v___x_1650_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1651_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1652_ = l_mkPanicMessageWithDecl(v___x_1651_, v___x_1650_, v___x_1649_, v___x_1648_, v___x_1647_);
return v___x_1652_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__2(void){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1653_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_1654_ = lean_unsigned_to_nat(36u);
v___x_1655_ = lean_unsigned_to_nat(143u);
v___x_1656_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1657_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1658_ = l_mkPanicMessageWithDecl(v___x_1657_, v___x_1656_, v___x_1655_, v___x_1654_, v___x_1653_);
return v___x_1658_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__6(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1665_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__5));
v___x_1666_ = lean_unsigned_to_nat(4u);
v___x_1667_ = lean_unsigned_to_nat(145u);
v___x_1668_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__0));
v___x_1669_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_1670_ = l_mkPanicMessageWithDecl(v___x_1669_, v___x_1668_, v___x_1667_, v___x_1666_, v___x_1665_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrProof(lean_object* v_lhs_1676_, lean_object* v_rhs_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v_fileName_1715_; lean_object* v_fileMap_1716_; lean_object* v_options_1717_; lean_object* v_currRecDepth_1718_; lean_object* v_maxRecDepth_1719_; lean_object* v_ref_1720_; lean_object* v_currNamespace_1721_; lean_object* v_openDecls_1722_; lean_object* v_initHeartbeats_1723_; lean_object* v_maxHeartbeats_1724_; lean_object* v_quotContext_1725_; lean_object* v_currMacroScope_1726_; uint8_t v_diag_1727_; lean_object* v_cancelTk_x3f_1728_; uint8_t v_suppressElabErrors_1729_; lean_object* v_inheritedTraceOptions_1730_; uint8_t v___x_1731_; 
v_fileName_1715_ = lean_ctor_get(v_a_1686_, 0);
lean_inc_ref(v_fileName_1715_);
v_fileMap_1716_ = lean_ctor_get(v_a_1686_, 1);
lean_inc_ref(v_fileMap_1716_);
v_options_1717_ = lean_ctor_get(v_a_1686_, 2);
lean_inc_ref(v_options_1717_);
v_currRecDepth_1718_ = lean_ctor_get(v_a_1686_, 3);
lean_inc(v_currRecDepth_1718_);
v_maxRecDepth_1719_ = lean_ctor_get(v_a_1686_, 4);
lean_inc(v_maxRecDepth_1719_);
v_ref_1720_ = lean_ctor_get(v_a_1686_, 5);
lean_inc(v_ref_1720_);
v_currNamespace_1721_ = lean_ctor_get(v_a_1686_, 6);
lean_inc(v_currNamespace_1721_);
v_openDecls_1722_ = lean_ctor_get(v_a_1686_, 7);
lean_inc(v_openDecls_1722_);
v_initHeartbeats_1723_ = lean_ctor_get(v_a_1686_, 8);
lean_inc(v_initHeartbeats_1723_);
v_maxHeartbeats_1724_ = lean_ctor_get(v_a_1686_, 9);
lean_inc(v_maxHeartbeats_1724_);
v_quotContext_1725_ = lean_ctor_get(v_a_1686_, 10);
lean_inc(v_quotContext_1725_);
v_currMacroScope_1726_ = lean_ctor_get(v_a_1686_, 11);
lean_inc(v_currMacroScope_1726_);
v_diag_1727_ = lean_ctor_get_uint8(v_a_1686_, sizeof(void*)*14);
v_cancelTk_x3f_1728_ = lean_ctor_get(v_a_1686_, 12);
lean_inc(v_cancelTk_x3f_1728_);
v_suppressElabErrors_1729_ = lean_ctor_get_uint8(v_a_1686_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1730_ = lean_ctor_get(v_a_1686_, 13);
lean_inc_ref(v_inheritedTraceOptions_1730_);
lean_dec_ref(v_a_1686_);
v___x_1731_ = lean_nat_dec_eq(v_currRecDepth_1718_, v_maxRecDepth_1719_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; uint8_t v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1732_ = l_Lean_Expr_cleanupAnnotations(v_lhs_1676_);
v___x_1733_ = l_Lean_Expr_isApp(v___x_1732_);
v___x_1734_ = lean_unsigned_to_nat(1u);
v___x_1735_ = lean_nat_add(v_currRecDepth_1718_, v___x_1734_);
lean_dec(v_currRecDepth_1718_);
v___x_1736_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1736_, 0, v_fileName_1715_);
lean_ctor_set(v___x_1736_, 1, v_fileMap_1716_);
lean_ctor_set(v___x_1736_, 2, v_options_1717_);
lean_ctor_set(v___x_1736_, 3, v___x_1735_);
lean_ctor_set(v___x_1736_, 4, v_maxRecDepth_1719_);
lean_ctor_set(v___x_1736_, 5, v_ref_1720_);
lean_ctor_set(v___x_1736_, 6, v_currNamespace_1721_);
lean_ctor_set(v___x_1736_, 7, v_openDecls_1722_);
lean_ctor_set(v___x_1736_, 8, v_initHeartbeats_1723_);
lean_ctor_set(v___x_1736_, 9, v_maxHeartbeats_1724_);
lean_ctor_set(v___x_1736_, 10, v_quotContext_1725_);
lean_ctor_set(v___x_1736_, 11, v_currMacroScope_1726_);
lean_ctor_set(v___x_1736_, 12, v_cancelTk_x3f_1728_);
lean_ctor_set(v___x_1736_, 13, v_inheritedTraceOptions_1730_);
lean_ctor_set_uint8(v___x_1736_, sizeof(void*)*14, v_diag_1727_);
lean_ctor_set_uint8(v___x_1736_, sizeof(void*)*14 + 1, v_suppressElabErrors_1729_);
if (v___x_1733_ == 0)
{
lean_dec_ref(v___x_1732_);
lean_dec_ref(v_rhs_1677_);
v___y_1703_ = v_a_1678_;
v___y_1704_ = v_a_1679_;
v___y_1705_ = v_a_1680_;
v___y_1706_ = v_a_1681_;
v___y_1707_ = v_a_1682_;
v___y_1708_ = v_a_1683_;
v___y_1709_ = v_a_1684_;
v___y_1710_ = v_a_1685_;
v___y_1711_ = v___x_1736_;
v___y_1712_ = v_a_1687_;
goto v___jp_1702_;
}
else
{
lean_object* v_arg_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; 
v_arg_1737_ = lean_ctor_get(v___x_1732_, 1);
lean_inc_ref(v_arg_1737_);
v___x_1738_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1732_);
v___x_1739_ = l_Lean_Expr_isApp(v___x_1738_);
if (v___x_1739_ == 0)
{
lean_dec_ref(v___x_1738_);
lean_dec_ref(v_arg_1737_);
lean_dec_ref(v_rhs_1677_);
v___y_1703_ = v_a_1678_;
v___y_1704_ = v_a_1679_;
v___y_1705_ = v_a_1680_;
v___y_1706_ = v_a_1681_;
v___y_1707_ = v_a_1682_;
v___y_1708_ = v_a_1683_;
v___y_1709_ = v_a_1684_;
v___y_1710_ = v_a_1685_;
v___y_1711_ = v___x_1736_;
v___y_1712_ = v_a_1687_;
goto v___jp_1702_;
}
else
{
lean_object* v_arg_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; 
v_arg_1740_ = lean_ctor_get(v___x_1738_, 1);
lean_inc_ref(v_arg_1740_);
v___x_1741_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1738_);
v___x_1742_ = l_Lean_Expr_isApp(v___x_1741_);
if (v___x_1742_ == 0)
{
lean_dec_ref(v___x_1741_);
lean_dec_ref(v_arg_1740_);
lean_dec_ref(v_arg_1737_);
lean_dec_ref(v_rhs_1677_);
v___y_1703_ = v_a_1678_;
v___y_1704_ = v_a_1679_;
v___y_1705_ = v_a_1680_;
v___y_1706_ = v_a_1681_;
v___y_1707_ = v_a_1682_;
v___y_1708_ = v_a_1683_;
v___y_1709_ = v_a_1684_;
v___y_1710_ = v_a_1685_;
v___y_1711_ = v___x_1736_;
v___y_1712_ = v_a_1687_;
goto v___jp_1702_;
}
else
{
lean_object* v_arg_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
v_arg_1743_ = lean_ctor_get(v___x_1741_, 1);
lean_inc_ref(v_arg_1743_);
v___x_1744_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1741_);
v___x_1745_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_1746_ = l_Lean_Expr_isConstOf(v___x_1744_, v___x_1745_);
if (v___x_1746_ == 0)
{
lean_dec_ref(v___x_1744_);
lean_dec_ref(v_arg_1743_);
lean_dec_ref(v_arg_1740_);
lean_dec_ref(v_arg_1737_);
lean_dec_ref(v_rhs_1677_);
v___y_1703_ = v_a_1678_;
v___y_1704_ = v_a_1679_;
v___y_1705_ = v_a_1680_;
v___y_1706_ = v_a_1681_;
v___y_1707_ = v_a_1682_;
v___y_1708_ = v_a_1683_;
v___y_1709_ = v_a_1684_;
v___y_1710_ = v_a_1685_;
v___y_1711_ = v___x_1736_;
v___y_1712_ = v_a_1687_;
goto v___jp_1702_;
}
else
{
lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1747_ = l_Lean_Expr_cleanupAnnotations(v_rhs_1677_);
v___x_1748_ = l_Lean_Expr_isApp(v___x_1747_);
if (v___x_1748_ == 0)
{
lean_dec_ref(v___x_1747_);
lean_dec_ref(v___x_1744_);
lean_dec_ref(v_arg_1743_);
lean_dec_ref(v_arg_1740_);
lean_dec_ref(v_arg_1737_);
v___y_1690_ = v_a_1678_;
v___y_1691_ = v_a_1679_;
v___y_1692_ = v_a_1680_;
v___y_1693_ = v_a_1681_;
v___y_1694_ = v_a_1682_;
v___y_1695_ = v_a_1683_;
v___y_1696_ = v_a_1684_;
v___y_1697_ = v_a_1685_;
v___y_1698_ = v___x_1736_;
v___y_1699_ = v_a_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v_arg_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
v_arg_1749_ = lean_ctor_get(v___x_1747_, 1);
lean_inc_ref(v_arg_1749_);
v___x_1750_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1747_);
v___x_1751_ = l_Lean_Expr_isApp(v___x_1750_);
if (v___x_1751_ == 0)
{
lean_dec_ref(v___x_1750_);
lean_dec_ref(v_arg_1749_);
lean_dec_ref(v___x_1744_);
lean_dec_ref(v_arg_1743_);
lean_dec_ref(v_arg_1740_);
lean_dec_ref(v_arg_1737_);
v___y_1690_ = v_a_1678_;
v___y_1691_ = v_a_1679_;
v___y_1692_ = v_a_1680_;
v___y_1693_ = v_a_1681_;
v___y_1694_ = v_a_1682_;
v___y_1695_ = v_a_1683_;
v___y_1696_ = v_a_1684_;
v___y_1697_ = v_a_1685_;
v___y_1698_ = v___x_1736_;
v___y_1699_ = v_a_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v_arg_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v_arg_1752_ = lean_ctor_get(v___x_1750_, 1);
lean_inc_ref(v_arg_1752_);
v___x_1753_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1750_);
v___x_1754_ = l_Lean_Expr_isApp(v___x_1753_);
if (v___x_1754_ == 0)
{
lean_dec_ref(v___x_1753_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_arg_1749_);
lean_dec_ref(v___x_1744_);
lean_dec_ref(v_arg_1743_);
lean_dec_ref(v_arg_1740_);
lean_dec_ref(v_arg_1737_);
v___y_1690_ = v_a_1678_;
v___y_1691_ = v_a_1679_;
v___y_1692_ = v_a_1680_;
v___y_1693_ = v_a_1681_;
v___y_1694_ = v_a_1682_;
v___y_1695_ = v_a_1683_;
v___y_1696_ = v_a_1684_;
v___y_1697_ = v_a_1685_;
v___y_1698_ = v___x_1736_;
v___y_1699_ = v_a_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v_arg_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v_arg_1755_ = lean_ctor_get(v___x_1753_, 1);
lean_inc_ref(v_arg_1755_);
v___x_1756_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1753_);
v___x_1757_ = l_Lean_Expr_isConstOf(v___x_1756_, v___x_1745_);
lean_dec_ref(v___x_1756_);
if (v___x_1757_ == 0)
{
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_arg_1749_);
lean_dec_ref(v___x_1744_);
lean_dec_ref(v_arg_1743_);
lean_dec_ref(v_arg_1740_);
lean_dec_ref(v_arg_1737_);
v___y_1690_ = v_a_1678_;
v___y_1691_ = v_a_1679_;
v___y_1692_ = v_a_1680_;
v___y_1693_ = v_a_1681_;
v___y_1694_ = v_a_1682_;
v___y_1695_ = v_a_1683_;
v___y_1696_ = v_a_1684_;
v___y_1697_ = v_a_1685_;
v___y_1698_ = v___x_1736_;
v___y_1699_ = v_a_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___y_1761_; uint8_t v___y_1777_; uint8_t v___x_1796_; 
v___x_1758_ = lean_st_ref_get(v_a_1678_);
v___x_1759_ = lean_st_ref_get(v_a_1678_);
v___x_1796_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1758_, v_arg_1740_, v_arg_1752_);
if (v___x_1796_ == 0)
{
lean_dec(v___x_1759_);
v___y_1777_ = v___x_1796_;
goto v___jp_1776_;
}
else
{
uint8_t v___x_1797_; 
v___x_1797_ = l_Lean_Meta_Grind_Goal_hasSameRoot(v___x_1759_, v_arg_1737_, v_arg_1749_);
v___y_1777_ = v___x_1797_;
goto v___jp_1776_;
}
v___jp_1760_:
{
lean_object* v___x_1762_; 
lean_inc_ref(v_arg_1752_);
lean_inc_ref(v_arg_1740_);
v___x_1762_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1740_, v_arg_1752_, v___x_1757_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v___x_1736_, v_a_1687_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1764_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref(v___x_1762_);
lean_inc_ref(v_arg_1749_);
lean_inc_ref(v_arg_1737_);
v___x_1764_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1737_, v_arg_1749_, v___x_1757_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v___x_1736_, v_a_1687_);
lean_dec_ref(v___x_1736_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1775_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1767_ = v___x_1764_;
v_isShared_1768_ = v_isSharedCheck_1775_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1775_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1769_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__4));
v___x_1770_ = l_Lean_mkConst(v___x_1769_, v___y_1761_);
v___x_1771_ = l_Lean_mkApp8(v___x_1770_, v_arg_1743_, v_arg_1755_, v_arg_1740_, v_arg_1737_, v_arg_1752_, v_arg_1749_, v_a_1763_, v_a_1765_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___x_1771_);
v___x_1773_ = v___x_1767_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
else
{
lean_dec(v_a_1763_);
lean_dec(v___y_1761_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_arg_1749_);
lean_dec_ref(v_arg_1743_);
lean_dec_ref(v_arg_1740_);
lean_dec_ref(v_arg_1737_);
return v___x_1764_;
}
}
else
{
lean_dec(v___y_1761_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_arg_1749_);
lean_dec_ref(v_arg_1743_);
lean_dec_ref(v_arg_1740_);
lean_dec_ref(v_arg_1737_);
lean_dec_ref(v___x_1736_);
return v___x_1762_;
}
}
v___jp_1776_:
{
if (v___y_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_arg_1749_);
lean_dec_ref(v___x_1744_);
lean_dec_ref(v_arg_1743_);
lean_dec_ref(v_arg_1740_);
lean_dec_ref(v_arg_1737_);
v___x_1778_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__6, &l_Lean_Meta_Grind_mkEqCongrProof___closed__6_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__6);
v___x_1779_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1778_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v___x_1736_, v_a_1687_);
lean_dec_ref(v___x_1736_);
return v___x_1779_;
}
else
{
lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1780_ = l_Lean_Expr_constLevels_x21(v___x_1744_);
lean_dec_ref(v___x_1744_);
v___x_1781_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1743_, v_arg_1755_);
if (v___x_1781_ == 0)
{
v___y_1761_ = v___x_1780_;
goto v___jp_1760_;
}
else
{
if (v___x_1731_ == 0)
{
lean_object* v___x_1782_; 
lean_dec_ref(v_arg_1755_);
lean_inc_ref(v_arg_1752_);
lean_inc_ref(v_arg_1740_);
v___x_1782_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1740_, v_arg_1752_, v___x_1731_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v___x_1736_, v_a_1687_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1784_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref(v___x_1782_);
lean_inc_ref(v_arg_1749_);
lean_inc_ref(v_arg_1737_);
v___x_1784_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_arg_1737_, v_arg_1749_, v___x_1731_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v___x_1736_, v_a_1687_);
lean_dec_ref(v___x_1736_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1795_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1795_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1795_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1789_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqCongrProof___closed__8));
v___x_1790_ = l_Lean_mkConst(v___x_1789_, v___x_1780_);
v___x_1791_ = l_Lean_mkApp7(v___x_1790_, v_arg_1743_, v_arg_1740_, v_arg_1737_, v_arg_1752_, v_arg_1749_, v_a_1783_, v_a_1785_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v___x_1791_);
v___x_1793_ = v___x_1787_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
else
{
lean_dec(v_a_1783_);
lean_dec(v___x_1780_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_arg_1749_);
lean_dec_ref(v_arg_1743_);
lean_dec_ref(v_arg_1740_);
lean_dec_ref(v_arg_1737_);
return v___x_1784_;
}
}
else
{
lean_dec(v___x_1780_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_arg_1749_);
lean_dec_ref(v_arg_1743_);
lean_dec_ref(v_arg_1740_);
lean_dec_ref(v_arg_1737_);
lean_dec_ref(v___x_1736_);
return v___x_1782_;
}
}
else
{
v___y_1761_ = v___x_1780_;
goto v___jp_1760_;
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
lean_object* v___x_1798_; 
lean_dec_ref(v_inheritedTraceOptions_1730_);
lean_dec(v_cancelTk_x3f_1728_);
lean_dec(v_currMacroScope_1726_);
lean_dec(v_quotContext_1725_);
lean_dec(v_maxHeartbeats_1724_);
lean_dec(v_initHeartbeats_1723_);
lean_dec(v_openDecls_1722_);
lean_dec(v_currNamespace_1721_);
lean_dec(v_maxRecDepth_1719_);
lean_dec(v_currRecDepth_1718_);
lean_dec_ref(v_options_1717_);
lean_dec_ref(v_fileMap_1716_);
lean_dec_ref(v_fileName_1715_);
lean_dec_ref(v_rhs_1677_);
lean_dec_ref(v_lhs_1676_);
v___x_1798_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_1720_);
return v___x_1798_;
}
v___jp_1689_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__1, &l_Lean_Meta_Grind_mkEqCongrProof___closed__1_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__1);
v___x_1701_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1700_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
lean_dec_ref(v___y_1698_);
return v___x_1701_;
}
v___jp_1702_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqCongrProof___closed__2, &l_Lean_Meta_Grind_mkEqCongrProof___closed__2_once, _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__2);
v___x_1714_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_1713_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec_ref(v___y_1711_);
return v___x_1714_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = lean_box(0);
v___x_1810_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3));
v___x_1811_ = l_Lean_mkConst(v___x_1810_, v___x_1809_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(lean_object* v_lhs_1812_, lean_object* v_rhs_1813_, uint8_t v_heq_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_){
_start:
{
lean_object* v___x_1826_; lean_object* v_p_1827_; lean_object* v___x_1828_; lean_object* v_q_1829_; uint8_t v___x_1830_; lean_object* v___x_1831_; 
v___x_1826_ = l_Lean_Expr_appFn_x21(v_lhs_1812_);
v_p_1827_ = l_Lean_Expr_appArg_x21(v___x_1826_);
lean_dec_ref(v___x_1826_);
v___x_1828_ = l_Lean_Expr_appFn_x21(v_rhs_1813_);
v_q_1829_ = l_Lean_Expr_appArg_x21(v___x_1828_);
lean_dec_ref(v___x_1828_);
v___x_1830_ = 0;
lean_inc_ref(v_q_1829_);
lean_inc_ref(v_p_1827_);
v___x_1831_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_p_1827_, v_q_1829_, v___x_1830_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v_hp_1833_; lean_object* v_hq_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref(v___x_1831_);
v_hp_1833_ = l_Lean_Expr_appArg_x21(v_lhs_1812_);
v_hq_1834_ = l_Lean_Expr_appArg_x21(v_rhs_1813_);
v___x_1835_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4);
v___x_1836_ = l_Lean_mkApp5(v___x_1835_, v_p_1827_, v_q_1829_, v_a_1832_, v_hp_1833_, v_hq_1834_);
v___x_1837_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v___x_1836_, v_heq_1814_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_);
return v___x_1837_;
}
else
{
lean_dec_ref(v_q_1829_);
lean_dec_ref(v_p_1827_);
return v___x_1831_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = lean_box(0);
v___x_1849_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1));
v___x_1850_ = l_Lean_mkConst(v___x_1849_, v___x_1848_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(lean_object* v_lhs_1851_, lean_object* v_rhs_1852_, uint8_t v_heq_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v___x_1865_; lean_object* v_p_1866_; lean_object* v___x_1867_; lean_object* v_q_1868_; uint8_t v___x_1869_; lean_object* v___x_1870_; 
v___x_1865_ = l_Lean_Expr_appFn_x21(v_lhs_1851_);
v_p_1866_ = l_Lean_Expr_appArg_x21(v___x_1865_);
lean_dec_ref(v___x_1865_);
v___x_1867_ = l_Lean_Expr_appFn_x21(v_rhs_1852_);
v_q_1868_ = l_Lean_Expr_appArg_x21(v___x_1867_);
lean_dec_ref(v___x_1867_);
v___x_1869_ = 0;
lean_inc_ref(v_q_1868_);
lean_inc_ref(v_p_1866_);
v___x_1870_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_p_1866_, v_q_1868_, v___x_1869_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v_hp_1872_; lean_object* v_hq_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref(v___x_1870_);
v_hp_1872_ = l_Lean_Expr_appArg_x21(v_lhs_1851_);
v_hq_1873_ = l_Lean_Expr_appArg_x21(v_rhs_1852_);
v___x_1874_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2);
v___x_1875_ = l_Lean_mkApp5(v___x_1874_, v_p_1866_, v_q_1868_, v_a_1871_, v_hp_1872_, v_hq_1873_);
v___x_1876_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v___x_1875_, v_heq_1853_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
return v___x_1876_;
}
else
{
lean_dec_ref(v_q_1868_);
lean_dec_ref(v_p_1866_);
return v___x_1870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(lean_object* v_lhs_1877_, lean_object* v_rhs_1878_, uint8_t v_heq_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
if (lean_obj_tag(v_lhs_1877_) == 7)
{
if (lean_obj_tag(v_rhs_1878_) == 7)
{
lean_object* v_binderType_1891_; lean_object* v_body_1892_; lean_object* v_binderType_1893_; lean_object* v_body_1894_; lean_object* v___y_1896_; lean_object* v_a_1897_; lean_object* v___x_1916_; uint8_t v_foApprox_1917_; uint8_t v_ctxApprox_1918_; uint8_t v_quasiPatternApprox_1919_; uint8_t v_constApprox_1920_; uint8_t v_isDefEqStuckEx_1921_; uint8_t v_unificationHints_1922_; uint8_t v_proofIrrelevance_1923_; uint8_t v_assignSyntheticOpaque_1924_; uint8_t v_offsetCnstrs_1925_; uint8_t v_etaStruct_1926_; uint8_t v_univApprox_1927_; uint8_t v_iota_1928_; uint8_t v_beta_1929_; uint8_t v_proj_1930_; uint8_t v_zeta_1931_; uint8_t v_zetaDelta_1932_; uint8_t v_zetaUnused_1933_; uint8_t v_zetaHave_1934_; uint8_t v_trackZetaDelta_1935_; lean_object* v_zetaDeltaSet_1936_; lean_object* v_lctx_1937_; lean_object* v_localInstances_1938_; lean_object* v_defEqCtx_x3f_1939_; lean_object* v_synthPendingDepth_1940_; lean_object* v_canUnfold_x3f_1941_; uint8_t v_univApprox_1942_; uint8_t v_inTypeClassResolution_1943_; uint8_t v_cacheInferType_1944_; lean_object* v_a_1946_; uint8_t v___x_1992_; lean_object* v_config_1993_; uint64_t v___x_1994_; uint64_t v___x_1995_; uint64_t v___x_1996_; uint64_t v___x_1997_; uint64_t v___x_1998_; uint64_t v_key_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v_binderType_1891_ = lean_ctor_get(v_lhs_1877_, 1);
lean_inc_ref(v_binderType_1891_);
v_body_1892_ = lean_ctor_get(v_lhs_1877_, 2);
lean_inc_ref(v_body_1892_);
lean_dec_ref(v_lhs_1877_);
v_binderType_1893_ = lean_ctor_get(v_rhs_1878_, 1);
lean_inc_ref(v_binderType_1893_);
v_body_1894_ = lean_ctor_get(v_rhs_1878_, 2);
lean_inc_ref(v_body_1894_);
lean_dec_ref(v_rhs_1878_);
v___x_1916_ = l_Lean_Meta_Context_config(v_a_1886_);
v_foApprox_1917_ = lean_ctor_get_uint8(v___x_1916_, 0);
v_ctxApprox_1918_ = lean_ctor_get_uint8(v___x_1916_, 1);
v_quasiPatternApprox_1919_ = lean_ctor_get_uint8(v___x_1916_, 2);
v_constApprox_1920_ = lean_ctor_get_uint8(v___x_1916_, 3);
v_isDefEqStuckEx_1921_ = lean_ctor_get_uint8(v___x_1916_, 4);
v_unificationHints_1922_ = lean_ctor_get_uint8(v___x_1916_, 5);
v_proofIrrelevance_1923_ = lean_ctor_get_uint8(v___x_1916_, 6);
v_assignSyntheticOpaque_1924_ = lean_ctor_get_uint8(v___x_1916_, 7);
v_offsetCnstrs_1925_ = lean_ctor_get_uint8(v___x_1916_, 8);
v_etaStruct_1926_ = lean_ctor_get_uint8(v___x_1916_, 10);
v_univApprox_1927_ = lean_ctor_get_uint8(v___x_1916_, 11);
v_iota_1928_ = lean_ctor_get_uint8(v___x_1916_, 12);
v_beta_1929_ = lean_ctor_get_uint8(v___x_1916_, 13);
v_proj_1930_ = lean_ctor_get_uint8(v___x_1916_, 14);
v_zeta_1931_ = lean_ctor_get_uint8(v___x_1916_, 15);
v_zetaDelta_1932_ = lean_ctor_get_uint8(v___x_1916_, 16);
v_zetaUnused_1933_ = lean_ctor_get_uint8(v___x_1916_, 17);
v_zetaHave_1934_ = lean_ctor_get_uint8(v___x_1916_, 18);
v_trackZetaDelta_1935_ = lean_ctor_get_uint8(v_a_1886_, sizeof(void*)*7);
v_zetaDeltaSet_1936_ = lean_ctor_get(v_a_1886_, 1);
v_lctx_1937_ = lean_ctor_get(v_a_1886_, 2);
v_localInstances_1938_ = lean_ctor_get(v_a_1886_, 3);
v_defEqCtx_x3f_1939_ = lean_ctor_get(v_a_1886_, 4);
v_synthPendingDepth_1940_ = lean_ctor_get(v_a_1886_, 5);
v_canUnfold_x3f_1941_ = lean_ctor_get(v_a_1886_, 6);
v_univApprox_1942_ = lean_ctor_get_uint8(v_a_1886_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1943_ = lean_ctor_get_uint8(v_a_1886_, sizeof(void*)*7 + 2);
v_cacheInferType_1944_ = lean_ctor_get_uint8(v_a_1886_, sizeof(void*)*7 + 3);
v___x_1992_ = 1;
v_config_1993_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_config_1993_, 0, v_foApprox_1917_);
lean_ctor_set_uint8(v_config_1993_, 1, v_ctxApprox_1918_);
lean_ctor_set_uint8(v_config_1993_, 2, v_quasiPatternApprox_1919_);
lean_ctor_set_uint8(v_config_1993_, 3, v_constApprox_1920_);
lean_ctor_set_uint8(v_config_1993_, 4, v_isDefEqStuckEx_1921_);
lean_ctor_set_uint8(v_config_1993_, 5, v_unificationHints_1922_);
lean_ctor_set_uint8(v_config_1993_, 6, v_proofIrrelevance_1923_);
lean_ctor_set_uint8(v_config_1993_, 7, v_assignSyntheticOpaque_1924_);
lean_ctor_set_uint8(v_config_1993_, 8, v_offsetCnstrs_1925_);
lean_ctor_set_uint8(v_config_1993_, 9, v___x_1992_);
lean_ctor_set_uint8(v_config_1993_, 10, v_etaStruct_1926_);
lean_ctor_set_uint8(v_config_1993_, 11, v_univApprox_1927_);
lean_ctor_set_uint8(v_config_1993_, 12, v_iota_1928_);
lean_ctor_set_uint8(v_config_1993_, 13, v_beta_1929_);
lean_ctor_set_uint8(v_config_1993_, 14, v_proj_1930_);
lean_ctor_set_uint8(v_config_1993_, 15, v_zeta_1931_);
lean_ctor_set_uint8(v_config_1993_, 16, v_zetaDelta_1932_);
lean_ctor_set_uint8(v_config_1993_, 17, v_zetaUnused_1933_);
lean_ctor_set_uint8(v_config_1993_, 18, v_zetaHave_1934_);
v___x_1994_ = l_Lean_Meta_Context_configKey(v_a_1886_);
v___x_1995_ = 2ULL;
v___x_1996_ = lean_uint64_shift_right(v___x_1994_, v___x_1995_);
v___x_1997_ = lean_uint64_shift_left(v___x_1996_, v___x_1995_);
v___x_1998_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2);
v_key_1999_ = lean_uint64_lor(v___x_1997_, v___x_1998_);
v___x_2000_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2000_, 0, v_config_1993_);
lean_ctor_set_uint64(v___x_2000_, sizeof(void*)*1, v_key_1999_);
lean_inc(v_canUnfold_x3f_1941_);
lean_inc(v_synthPendingDepth_1940_);
lean_inc(v_defEqCtx_x3f_1939_);
lean_inc_ref(v_localInstances_1938_);
lean_inc_ref(v_lctx_1937_);
lean_inc(v_zetaDeltaSet_1936_);
v___x_2001_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
lean_ctor_set(v___x_2001_, 1, v_zetaDeltaSet_1936_);
lean_ctor_set(v___x_2001_, 2, v_lctx_1937_);
lean_ctor_set(v___x_2001_, 3, v_localInstances_1938_);
lean_ctor_set(v___x_2001_, 4, v_defEqCtx_x3f_1939_);
lean_ctor_set(v___x_2001_, 5, v_synthPendingDepth_1940_);
lean_ctor_set(v___x_2001_, 6, v_canUnfold_x3f_1941_);
lean_ctor_set_uint8(v___x_2001_, sizeof(void*)*7, v_trackZetaDelta_1935_);
lean_ctor_set_uint8(v___x_2001_, sizeof(void*)*7 + 1, v_univApprox_1942_);
lean_ctor_set_uint8(v___x_2001_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1943_);
lean_ctor_set_uint8(v___x_2001_, sizeof(void*)*7 + 3, v_cacheInferType_1944_);
lean_inc_ref(v_binderType_1891_);
v___x_2002_ = l_Lean_Meta_getLevel(v_binderType_1891_, v___x_2001_, v_a_1887_, v_a_1888_, v_a_1889_);
lean_dec_ref(v___x_2001_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref(v___x_2002_);
v_a_1946_ = v_a_2003_;
goto v___jp_1945_;
}
else
{
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2004_; 
v_a_2004_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2004_);
lean_dec_ref(v___x_2002_);
v_a_1946_ = v_a_2004_;
goto v___jp_1945_;
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec_ref(v___x_1916_);
lean_dec_ref(v_body_1894_);
lean_dec_ref(v_binderType_1893_);
lean_dec_ref(v_body_1892_);
lean_dec_ref(v_binderType_1891_);
v_a_2005_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_2002_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2002_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
v___jp_1895_:
{
uint8_t v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = 0;
lean_inc_ref(v_binderType_1893_);
lean_inc_ref(v_binderType_1891_);
v___x_1899_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_binderType_1891_, v_binderType_1893_, v___x_1898_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1901_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref(v___x_1899_);
lean_inc_ref(v_body_1894_);
lean_inc_ref(v_body_1892_);
v___x_1901_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_body_1892_, v_body_1894_, v___x_1898_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1915_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1915_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1915_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1906_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__1));
v___x_1907_ = lean_box(0);
v___x_1908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1908_, 0, v_a_1897_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___y_1896_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = l_Lean_mkConst(v___x_1906_, v___x_1909_);
v___x_1911_ = l_Lean_mkApp6(v___x_1910_, v_binderType_1891_, v_binderType_1893_, v_body_1892_, v_body_1894_, v_a_1900_, v_a_1902_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1911_);
v___x_1913_ = v___x_1904_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
else
{
lean_dec(v_a_1900_);
lean_dec(v_a_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v_body_1894_);
lean_dec_ref(v_binderType_1893_);
lean_dec_ref(v_body_1892_);
lean_dec_ref(v_binderType_1891_);
return v___x_1901_;
}
}
else
{
lean_dec(v_a_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v_body_1894_);
lean_dec_ref(v_binderType_1893_);
lean_dec_ref(v_body_1892_);
lean_dec_ref(v_binderType_1891_);
return v___x_1899_;
}
}
v___jp_1945_:
{
uint8_t v_foApprox_1947_; uint8_t v_ctxApprox_1948_; uint8_t v_quasiPatternApprox_1949_; uint8_t v_constApprox_1950_; uint8_t v_isDefEqStuckEx_1951_; uint8_t v_unificationHints_1952_; uint8_t v_proofIrrelevance_1953_; uint8_t v_assignSyntheticOpaque_1954_; uint8_t v_offsetCnstrs_1955_; uint8_t v_etaStruct_1956_; uint8_t v_univApprox_1957_; uint8_t v_iota_1958_; uint8_t v_beta_1959_; uint8_t v_proj_1960_; uint8_t v_zeta_1961_; uint8_t v_zetaDelta_1962_; uint8_t v_zetaUnused_1963_; uint8_t v_zetaHave_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1991_; 
v_foApprox_1947_ = lean_ctor_get_uint8(v___x_1916_, 0);
v_ctxApprox_1948_ = lean_ctor_get_uint8(v___x_1916_, 1);
v_quasiPatternApprox_1949_ = lean_ctor_get_uint8(v___x_1916_, 2);
v_constApprox_1950_ = lean_ctor_get_uint8(v___x_1916_, 3);
v_isDefEqStuckEx_1951_ = lean_ctor_get_uint8(v___x_1916_, 4);
v_unificationHints_1952_ = lean_ctor_get_uint8(v___x_1916_, 5);
v_proofIrrelevance_1953_ = lean_ctor_get_uint8(v___x_1916_, 6);
v_assignSyntheticOpaque_1954_ = lean_ctor_get_uint8(v___x_1916_, 7);
v_offsetCnstrs_1955_ = lean_ctor_get_uint8(v___x_1916_, 8);
v_etaStruct_1956_ = lean_ctor_get_uint8(v___x_1916_, 10);
v_univApprox_1957_ = lean_ctor_get_uint8(v___x_1916_, 11);
v_iota_1958_ = lean_ctor_get_uint8(v___x_1916_, 12);
v_beta_1959_ = lean_ctor_get_uint8(v___x_1916_, 13);
v_proj_1960_ = lean_ctor_get_uint8(v___x_1916_, 14);
v_zeta_1961_ = lean_ctor_get_uint8(v___x_1916_, 15);
v_zetaDelta_1962_ = lean_ctor_get_uint8(v___x_1916_, 16);
v_zetaUnused_1963_ = lean_ctor_get_uint8(v___x_1916_, 17);
v_zetaHave_1964_ = lean_ctor_get_uint8(v___x_1916_, 18);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1966_ = v___x_1916_;
v_isShared_1967_ = v_isSharedCheck_1991_;
goto v_resetjp_1965_;
}
else
{
lean_dec(v___x_1916_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1991_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
uint8_t v___x_1968_; lean_object* v_config_1970_; 
v___x_1968_ = 1;
if (v_isShared_1967_ == 0)
{
v_config_1970_ = v___x_1966_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, 0, v_foApprox_1947_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, 1, v_ctxApprox_1948_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, 2, v_quasiPatternApprox_1949_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, 3, v_constApprox_1950_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, 4, v_isDefEqStuckEx_1951_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, 5, v_unificationHints_1952_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, 6, v_proofIrrelevance_1953_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, 7, v_assignSyntheticOpaque_1954_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, 8, v_offsetCnstrs_1955_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, 10, v_etaStruct_1956_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, 11, v_univApprox_1957_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, 12, v_iota_1958_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, 13, v_beta_1959_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, 14, v_proj_1960_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, 15, v_zeta_1961_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, 16, v_zetaDelta_1962_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, 17, v_zetaUnused_1963_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, 18, v_zetaHave_1964_);
v_config_1970_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
uint64_t v___x_1971_; uint64_t v___x_1972_; uint64_t v___x_1973_; uint64_t v___x_1974_; uint64_t v___x_1975_; uint64_t v_key_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
lean_ctor_set_uint8(v_config_1970_, 9, v___x_1968_);
v___x_1971_ = l_Lean_Meta_Context_configKey(v_a_1886_);
v___x_1972_ = 2ULL;
v___x_1973_ = lean_uint64_shift_right(v___x_1971_, v___x_1972_);
v___x_1974_ = lean_uint64_shift_left(v___x_1973_, v___x_1972_);
v___x_1975_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2);
v_key_1976_ = lean_uint64_lor(v___x_1974_, v___x_1975_);
v___x_1977_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1977_, 0, v_config_1970_);
lean_ctor_set_uint64(v___x_1977_, sizeof(void*)*1, v_key_1976_);
lean_inc(v_canUnfold_x3f_1941_);
lean_inc(v_synthPendingDepth_1940_);
lean_inc(v_defEqCtx_x3f_1939_);
lean_inc_ref(v_localInstances_1938_);
lean_inc_ref(v_lctx_1937_);
lean_inc(v_zetaDeltaSet_1936_);
v___x_1978_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
lean_ctor_set(v___x_1978_, 1, v_zetaDeltaSet_1936_);
lean_ctor_set(v___x_1978_, 2, v_lctx_1937_);
lean_ctor_set(v___x_1978_, 3, v_localInstances_1938_);
lean_ctor_set(v___x_1978_, 4, v_defEqCtx_x3f_1939_);
lean_ctor_set(v___x_1978_, 5, v_synthPendingDepth_1940_);
lean_ctor_set(v___x_1978_, 6, v_canUnfold_x3f_1941_);
lean_ctor_set_uint8(v___x_1978_, sizeof(void*)*7, v_trackZetaDelta_1935_);
lean_ctor_set_uint8(v___x_1978_, sizeof(void*)*7 + 1, v_univApprox_1942_);
lean_ctor_set_uint8(v___x_1978_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1943_);
lean_ctor_set_uint8(v___x_1978_, sizeof(void*)*7 + 3, v_cacheInferType_1944_);
lean_inc_ref(v_body_1892_);
v___x_1979_ = l_Lean_Meta_getLevel(v_body_1892_, v___x_1978_, v_a_1887_, v_a_1888_, v_a_1889_);
lean_dec_ref(v___x_1978_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref(v___x_1979_);
v___y_1896_ = v_a_1946_;
v_a_1897_ = v_a_1980_;
goto v___jp_1895_;
}
else
{
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1981_; 
v_a_1981_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1981_);
lean_dec_ref(v___x_1979_);
v___y_1896_ = v_a_1946_;
v_a_1897_ = v_a_1981_;
goto v___jp_1895_;
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
lean_dec(v_a_1946_);
lean_dec_ref(v_body_1894_);
lean_dec_ref(v_binderType_1893_);
lean_dec_ref(v_body_1892_);
lean_dec_ref(v_binderType_1891_);
v_a_1982_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1979_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1979_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
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
lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_dec_ref(v_lhs_1877_);
lean_dec_ref(v_rhs_1878_);
v___x_2013_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4);
v___x_2014_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2013_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
return v___x_2014_;
}
}
else
{
lean_object* v___x_2015_; 
lean_inc_ref(v_lhs_1877_);
v___x_2015_ = l_Lean_Meta_Grind_useFunCC___redArg(v_lhs_1877_, v_a_1880_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; uint8_t v___x_2017_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref(v___x_2015_);
v___x_2017_ = lean_unbox(v_a_2016_);
lean_dec(v_a_2016_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; 
v___x_2018_ = l_Lean_Expr_getAppNumArgs(v_lhs_1877_);
v___x_2019_ = l_Lean_Expr_getAppNumArgs(v_rhs_1878_);
v___x_2020_ = lean_nat_dec_eq(v___x_2019_, v___x_2018_);
lean_dec(v___x_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_dec(v___x_2018_);
lean_dec_ref(v_rhs_1878_);
lean_dec_ref(v_lhs_1877_);
v___x_2021_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6);
v___x_2022_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2021_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
return v___x_2022_;
}
else
{
lean_object* v___x_2023_; lean_object* v___x_2024_; uint8_t v___y_2040_; uint8_t v___y_2052_; lean_object* v___x_2056_; uint8_t v___x_2057_; uint8_t v___y_2062_; 
v___x_2023_ = l_Lean_Expr_getAppFn(v_lhs_1877_);
v___x_2024_ = l_Lean_Expr_getAppFn(v_rhs_1878_);
v___x_2056_ = lean_unsigned_to_nat(2u);
v___x_2057_ = lean_nat_dec_eq(v___x_2018_, v___x_2056_);
if (v___x_2057_ == 0)
{
v___y_2062_ = v___x_2057_;
goto v___jp_2061_;
}
else
{
lean_object* v___x_2066_; uint8_t v___x_2067_; 
v___x_2066_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10));
v___x_2067_ = l_Lean_Expr_isConstOf(v___x_2023_, v___x_2066_);
v___y_2062_ = v___x_2067_;
goto v___jp_2061_;
}
v___jp_2025_:
{
lean_object* v___x_2026_; 
lean_inc_ref(v_rhs_1878_);
lean_inc_ref(v_lhs_1877_);
v___x_2026_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(v_lhs_1877_, v_rhs_1878_, v___x_2023_, v___x_2024_, v___x_2018_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
lean_dec_ref(v___x_2024_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; uint8_t v___x_2028_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref(v___x_2026_);
v___x_2028_ = lean_unbox(v_a_2027_);
lean_dec(v_a_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; 
v___x_2029_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_1877_, v_rhs_1878_, v_heq_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
return v___x_2029_;
}
else
{
lean_object* v___x_2030_; 
v___x_2030_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_1877_, v_rhs_1878_, v_heq_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
lean_dec_ref(v_rhs_1878_);
lean_dec_ref(v_lhs_1877_);
return v___x_2030_;
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec_ref(v_rhs_1878_);
lean_dec_ref(v_lhs_1877_);
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
if (v___y_2040_ == 0)
{
goto v___jp_2025_;
}
else
{
lean_object* v___x_2041_; uint8_t v___x_2042_; 
v___x_2041_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_2042_ = l_Lean_Expr_isConstOf(v___x_2024_, v___x_2041_);
if (v___x_2042_ == 0)
{
goto v___jp_2025_;
}
else
{
lean_object* v___x_2043_; 
lean_dec_ref(v___x_2024_);
lean_dec_ref(v___x_2023_);
lean_dec(v___x_2018_);
lean_inc_ref(v_a_1888_);
v___x_2043_ = l_Lean_Meta_Grind_mkEqCongrProof(v_lhs_1877_, v_rhs_1878_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_2043_) == 0)
{
if (v_heq_1879_ == 0)
{
return v___x_2043_;
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2045_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref(v___x_2043_);
v___x_2045_ = l_Lean_Meta_mkHEqOfEq(v_a_2044_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
return v___x_2045_;
}
}
else
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
v___x_2048_ = lean_nat_dec_eq(v___x_2018_, v___x_2047_);
if (v___x_2048_ == 0)
{
v___y_2040_ = v___x_2048_;
goto v___jp_2039_;
}
else
{
lean_object* v___x_2049_; uint8_t v___x_2050_; 
v___x_2049_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1));
v___x_2050_ = l_Lean_Expr_isConstOf(v___x_2023_, v___x_2049_);
v___y_2040_ = v___x_2050_;
goto v___jp_2039_;
}
}
v___jp_2051_:
{
if (v___y_2052_ == 0)
{
goto v___jp_2046_;
}
else
{
lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2053_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8));
v___x_2054_ = l_Lean_Expr_isConstOf(v___x_2024_, v___x_2053_);
if (v___x_2054_ == 0)
{
goto v___jp_2046_;
}
else
{
lean_object* v___x_2055_; 
lean_dec_ref(v___x_2024_);
lean_dec_ref(v___x_2023_);
lean_dec(v___x_2018_);
v___x_2055_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_1877_, v_rhs_1878_, v_heq_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
lean_dec_ref(v_rhs_1878_);
lean_dec_ref(v_lhs_1877_);
return v___x_2055_;
}
}
}
v___jp_2058_:
{
if (v___x_2057_ == 0)
{
v___y_2052_ = v___x_2057_;
goto v___jp_2051_;
}
else
{
lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2059_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8));
v___x_2060_ = l_Lean_Expr_isConstOf(v___x_2023_, v___x_2059_);
v___y_2052_ = v___x_2060_;
goto v___jp_2051_;
}
}
v___jp_2061_:
{
if (v___y_2062_ == 0)
{
goto v___jp_2058_;
}
else
{
lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2063_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10));
v___x_2064_ = l_Lean_Expr_isConstOf(v___x_2024_, v___x_2063_);
if (v___x_2064_ == 0)
{
goto v___jp_2058_;
}
else
{
lean_object* v___x_2065_; 
lean_dec_ref(v___x_2024_);
lean_dec_ref(v___x_2023_);
lean_dec(v___x_2018_);
v___x_2065_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_1877_, v_rhs_1878_, v_heq_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
lean_dec_ref(v_rhs_1878_);
lean_dec_ref(v_lhs_1877_);
return v___x_2065_;
}
}
}
}
}
else
{
lean_object* v___x_2068_; 
v___x_2068_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_1877_, v_rhs_1878_, v_heq_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
return v___x_2068_;
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec_ref(v_rhs_1878_);
lean_dec_ref(v_lhs_1877_);
v_a_2069_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2015_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2015_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(lean_object* v_lhs_2077_, lean_object* v_rhs_2078_, lean_object* v_h_2079_, uint8_t v_flipped_2080_, uint8_t v_heq_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_){
_start:
{
lean_object* v___x_2093_; uint8_t v___x_2094_; 
v___x_2093_ = l_Lean_Meta_Grind_congrPlaceholderProof;
v___x_2094_ = lean_expr_eqv(v_h_2079_, v___x_2093_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; uint8_t v___x_2096_; 
v___x_2095_ = l_Lean_Meta_Grind_eqCongrSymmPlaceholderProof;
v___x_2096_ = lean_expr_eqv(v_h_2079_, v___x_2095_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; 
lean_dec_ref(v_rhs_2078_);
lean_dec_ref(v_lhs_2077_);
v___x_2097_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(v_h_2079_, v_flipped_2080_, v_heq_2081_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_);
return v___x_2097_;
}
else
{
lean_object* v___x_2098_; 
lean_dec_ref(v_h_2079_);
lean_inc_ref(v_a_2090_);
v___x_2098_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(v_lhs_2077_, v_rhs_2078_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_);
if (lean_obj_tag(v___x_2098_) == 0)
{
if (v_heq_2081_ == 0)
{
return v___x_2098_;
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2100_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref(v___x_2098_);
v___x_2100_ = l_Lean_Meta_mkHEqOfEq(v_a_2099_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_);
return v___x_2100_;
}
}
else
{
return v___x_2098_;
}
}
}
else
{
lean_object* v___x_2101_; 
lean_dec_ref(v_h_2079_);
v___x_2101_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(v_lhs_2077_, v_rhs_2078_, v_heq_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_);
return v___x_2101_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2103_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2104_ = lean_unsigned_to_nat(29u);
v___x_2105_ = lean_unsigned_to_nat(288u);
v___x_2106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0));
v___x_2107_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2108_ = l_mkPanicMessageWithDecl(v___x_2107_, v___x_2106_, v___x_2105_, v___x_2104_, v___x_2103_);
return v___x_2108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2(void){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2109_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2110_ = lean_unsigned_to_nat(35u);
v___x_2111_ = lean_unsigned_to_nat(287u);
v___x_2112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0));
v___x_2113_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2114_ = l_mkPanicMessageWithDecl(v___x_2113_, v___x_2112_, v___x_2111_, v___x_2110_, v___x_2109_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(lean_object* v_lhs_2115_, lean_object* v_common_2116_, lean_object* v_acc_2117_, uint8_t v_heq_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
uint8_t v___x_2130_; 
v___x_2130_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_lhs_2115_, v_common_2116_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = lean_st_ref_get(v_a_2119_);
lean_inc_ref(v_lhs_2115_);
v___x_2132_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2131_, v_lhs_2115_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v_target_x3f_2134_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref(v___x_2132_);
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
v_flipped_2136_ = lean_ctor_get_uint8(v_a_2133_, sizeof(void*)*11);
lean_dec(v_a_2133_);
v_val_2137_ = lean_ctor_get(v_target_x3f_2134_, 0);
lean_inc(v_val_2137_);
lean_dec_ref(v_target_x3f_2134_);
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
v___x_2142_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_lhs_2115_, v_val_2137_, v_val_2138_, v_flipped_2136_, v_heq_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2144_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref(v___x_2142_);
v___x_2144_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_acc_2117_, v_a_2143_, v_heq_2118_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2147_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref(v___x_2144_);
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
v_lhs_2115_ = v_val_2137_;
v_acc_2117_ = v___x_2147_;
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
lean_dec(v_acc_2117_);
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
lean_dec_ref(v_target_x3f_2134_);
lean_dec(v_proof_x3f_2135_);
lean_dec(v_a_2133_);
lean_dec(v_acc_2117_);
lean_dec_ref(v_lhs_2115_);
v___x_2167_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1);
v___x_2168_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2167_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
return v___x_2168_;
}
}
else
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
lean_dec(v_target_x3f_2134_);
lean_dec(v_a_2133_);
lean_dec(v_acc_2117_);
lean_dec_ref(v_lhs_2115_);
v___x_2169_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2);
v___x_2170_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2169_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
return v___x_2170_;
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec(v_acc_2117_);
lean_dec_ref(v_lhs_2115_);
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
lean_dec_ref(v_lhs_2115_);
v___x_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2179_, 0, v_acc_2117_);
return v___x_2179_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2181_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2182_ = lean_unsigned_to_nat(29u);
v___x_2183_ = lean_unsigned_to_nat(300u);
v___x_2184_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0));
v___x_2185_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2186_ = l_mkPanicMessageWithDecl(v___x_2185_, v___x_2184_, v___x_2183_, v___x_2182_, v___x_2181_);
return v___x_2186_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2187_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2188_ = lean_unsigned_to_nat(35u);
v___x_2189_ = lean_unsigned_to_nat(299u);
v___x_2190_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0));
v___x_2191_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2192_ = l_mkPanicMessageWithDecl(v___x_2191_, v___x_2190_, v___x_2189_, v___x_2188_, v___x_2187_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(lean_object* v_rhs_2193_, lean_object* v_common_2194_, lean_object* v_lhsEqCommon_x3f_2195_, uint8_t v_heq_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
uint8_t v___x_2208_; 
v___x_2208_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_rhs_2193_, v_common_2194_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = lean_st_ref_get(v_a_2197_);
lean_inc_ref(v_rhs_2193_);
v___x_2210_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2209_, v_rhs_2193_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v_target_x3f_2212_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2211_);
lean_dec_ref(v___x_2210_);
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
v_flipped_2214_ = lean_ctor_get_uint8(v_a_2211_, sizeof(void*)*11);
lean_dec(v_a_2211_);
v_val_2215_ = lean_ctor_get(v_target_x3f_2212_, 0);
lean_inc(v_val_2215_);
lean_dec_ref(v_target_x3f_2212_);
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
v___x_2222_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_val_2215_, v_rhs_2193_, v_val_2216_, v___y_2221_, v_heq_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v___x_2224_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_a_2223_);
lean_dec_ref(v___x_2222_);
v___x_2224_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_val_2215_, v_common_2194_, v_lhsEqCommon_x3f_2195_, v_heq_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2226_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref(v___x_2224_);
v___x_2226_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(v_a_2225_, v_a_2223_, v_heq_2196_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
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
lean_dec(v_lhsEqCommon_x3f_2195_);
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
lean_dec_ref(v_target_x3f_2212_);
lean_dec(v_proof_x3f_2213_);
lean_dec(v_a_2211_);
lean_dec(v_lhsEqCommon_x3f_2195_);
lean_dec_ref(v_rhs_2193_);
v___x_2256_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1);
v___x_2257_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2256_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
return v___x_2257_;
}
}
else
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
lean_dec(v_target_x3f_2212_);
lean_dec(v_a_2211_);
lean_dec(v_lhsEqCommon_x3f_2195_);
lean_dec_ref(v_rhs_2193_);
v___x_2258_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2);
v___x_2259_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_2258_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
return v___x_2259_;
}
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
lean_dec(v_lhsEqCommon_x3f_2195_);
lean_dec_ref(v_rhs_2193_);
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
lean_dec_ref(v_rhs_2193_);
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v_lhsEqCommon_x3f_2195_);
return v___x_2268_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2269_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2270_ = lean_unsigned_to_nat(72u);
v___x_2271_ = lean_unsigned_to_nat(321u);
v___x_2272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0));
v___x_2273_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2274_ = l_mkPanicMessageWithDecl(v___x_2273_, v___x_2272_, v___x_2271_, v___x_2270_, v___x_2269_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(lean_object* v_lhs_2275_, lean_object* v_rhs_2276_, uint8_t v_heq_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
uint8_t v___x_2289_; 
v___x_2289_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_lhs_2275_, v_rhs_2276_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2290_; 
lean_inc_ref(v_lhs_2275_);
v___x_2290_ = l_Lean_Meta_Grind_getRootENode___redArg(v_lhs_2275_, v_a_2278_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2291_);
lean_dec_ref(v___x_2290_);
v___x_2292_ = lean_st_ref_get(v_a_2278_);
lean_inc_ref(v_lhs_2275_);
v___x_2293_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2292_, v_lhs_2275_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref(v___x_2293_);
v___x_2295_ = lean_st_ref_get(v_a_2278_);
lean_inc_ref(v_rhs_2276_);
v___x_2296_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2295_, v_rhs_2276_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v_root_2298_; lean_object* v_root_2299_; uint8_t v___x_2300_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref(v___x_2296_);
v_root_2298_ = lean_ctor_get(v_a_2294_, 2);
lean_inc_ref(v_root_2298_);
lean_dec(v_a_2294_);
v_root_2299_ = lean_ctor_get(v_a_2297_, 2);
lean_inc_ref(v_root_2299_);
lean_dec(v_a_2297_);
v___x_2300_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_root_2298_, v_root_2299_);
lean_dec_ref(v_root_2299_);
lean_dec_ref(v_root_2298_);
if (v___x_2300_ == 0)
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
lean_dec(v_a_2291_);
lean_dec_ref(v_rhs_2276_);
lean_dec_ref(v_lhs_2275_);
v___x_2301_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2);
v___x_2302_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2301_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_2302_;
}
else
{
lean_object* v___x_2303_; 
lean_inc_ref(v_rhs_2276_);
lean_inc_ref(v_lhs_2275_);
v___x_2303_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(v_lhs_2275_, v_rhs_2276_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; uint8_t v_heqProofs_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref(v___x_2303_);
v_heqProofs_2305_ = lean_ctor_get_uint8(v_a_2291_, sizeof(void*)*11 + 4);
lean_dec(v_a_2291_);
v___x_2306_ = lean_box(0);
v___x_2307_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_2275_, v_a_2304_, v___x_2306_, v_heqProofs_2305_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2309_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
lean_dec_ref(v___x_2307_);
v___x_2309_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_2276_, v_a_2304_, v_a_2308_, v_heqProofs_2305_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
lean_dec(v_a_2304_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2325_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2312_ = v___x_2309_;
v_isShared_2313_ = v_isSharedCheck_2325_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2309_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2325_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
if (lean_obj_tag(v_a_2310_) == 1)
{
lean_object* v_val_2314_; uint8_t v___y_2319_; 
v_val_2314_ = lean_ctor_get(v_a_2310_, 0);
lean_inc(v_val_2314_);
lean_dec_ref(v_a_2310_);
if (v_heq_2277_ == 0)
{
if (v_heqProofs_2305_ == 0)
{
v___y_2319_ = v___x_2300_;
goto v___jp_2318_;
}
else
{
lean_del_object(v___x_2312_);
goto v___jp_2315_;
}
}
else
{
v___y_2319_ = v_heqProofs_2305_;
goto v___jp_2318_;
}
v___jp_2315_:
{
if (v_heq_2277_ == 0)
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Lean_Meta_mkEqOfHEq(v_val_2314_, v_heq_2277_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_2316_;
}
else
{
lean_object* v___x_2317_; 
v___x_2317_ = l_Lean_Meta_mkHEqOfEq(v_val_2314_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_2317_;
}
}
v___jp_2318_:
{
if (v___y_2319_ == 0)
{
lean_del_object(v___x_2312_);
goto v___jp_2315_;
}
else
{
lean_object* v___x_2321_; 
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v_val_2314_);
v___x_2321_ = v___x_2312_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_val_2314_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
else
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
lean_del_object(v___x_2312_);
lean_dec(v_a_2310_);
v___x_2323_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3);
v___x_2324_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2323_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_2324_;
}
}
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
v_a_2326_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2309_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2309_);
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
lean_dec_ref(v_rhs_2276_);
v_a_2334_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2307_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2307_);
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
lean_dec(v_a_2291_);
lean_dec_ref(v_rhs_2276_);
lean_dec_ref(v_lhs_2275_);
return v___x_2303_;
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec(v_a_2294_);
lean_dec(v_a_2291_);
lean_dec_ref(v_rhs_2276_);
lean_dec_ref(v_lhs_2275_);
v_a_2342_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2296_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2296_);
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
lean_dec(v_a_2291_);
lean_dec_ref(v_rhs_2276_);
lean_dec_ref(v_lhs_2275_);
v_a_2350_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2293_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2293_);
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
lean_dec_ref(v_rhs_2276_);
lean_dec_ref(v_lhs_2275_);
v_a_2358_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2290_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2290_);
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
lean_dec_ref(v_rhs_2276_);
v___x_2366_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(v_lhs_2275_, v_heq_2277_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
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
lean_object* v___x_2386_; lean_object* v_i_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2386_ = lean_unsigned_to_nat(1u);
v_i_2387_ = lean_nat_sub(v_i_2370_, v___x_2386_);
v___x_2388_ = l_Lean_Expr_appFn_x21(v_lhs_2368_);
v___x_2389_ = l_Lean_Expr_appFn_x21(v_rhs_2369_);
v___x_2390_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_2367_, v___x_2388_, v___x_2389_, v_i_2387_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
lean_dec_ref(v___x_2389_);
lean_dec_ref(v___x_2388_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v_argKinds_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; uint8_t v___y_2396_; uint8_t v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; uint8_t v___x_2410_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref(v___x_2390_);
v_argKinds_2392_ = lean_ctor_get(v_thm_2367_, 2);
v___x_2393_ = l_Lean_Expr_appArg_x21(v_lhs_2368_);
v___x_2394_ = l_Lean_Expr_appArg_x21(v_rhs_2369_);
v___x_2407_ = 0;
v___x_2408_ = lean_box(v___x_2407_);
v___x_2409_ = lean_array_get_borrowed(v___x_2408_, v_argKinds_2392_, v_i_2387_);
lean_dec(v_i_2387_);
v___x_2410_ = lean_unbox(v___x_2409_);
if (v___x_2410_ == 4)
{
v___y_2396_ = v___x_2383_;
goto v___jp_2395_;
}
else
{
uint8_t v___x_2411_; 
v___x_2411_ = 0;
v___y_2396_ = v___x_2411_;
goto v___jp_2395_;
}
v___jp_2395_:
{
lean_object* v___x_2397_; 
lean_inc_ref(v___x_2394_);
lean_inc_ref(v___x_2393_);
v___x_2397_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___x_2393_, v___x_2394_, v___y_2396_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2406_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2400_ = v___x_2397_;
v_isShared_2401_ = v_isSharedCheck_2406_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2397_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2406_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2402_ = l_Lean_mkApp3(v_a_2391_, v___x_2393_, v___x_2394_, v_a_2398_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 0, v___x_2402_);
v___x_2404_ = v___x_2400_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
else
{
lean_dec_ref(v___x_2394_);
lean_dec_ref(v___x_2393_);
lean_dec(v_a_2391_);
return v___x_2397_;
}
}
}
else
{
lean_dec(v_i_2387_);
return v___x_2390_;
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
lean_dec_ref(v___x_2432_);
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
lean_object* v_a_2440_; uint8_t v___x_2441_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2440_);
lean_dec_ref(v___x_2439_);
v___x_2441_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_f_2415_, v_g_2416_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__4));
v___x_2443_ = l_Lean_Core_mkFreshUserName(v___x_2442_, v_a_2429_, v_a_2430_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2445_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref(v___x_2443_);
lean_inc(v_a_2430_);
lean_inc_ref(v_a_2429_);
lean_inc(v_a_2428_);
lean_inc_ref(v_a_2427_);
lean_inc_ref(v_f_2415_);
v___x_2445_ = lean_infer_type(v_f_2415_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___f_2449_; lean_object* v___x_2450_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
lean_dec_ref(v___x_2445_);
v___x_2447_ = lean_box(v___x_2441_);
v___x_2448_ = lean_box(v___x_2436_);
v___f_2449_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___boxed), 17, 5);
lean_closure_set(v___f_2449_, 0, v_numArgs_2417_);
lean_closure_set(v___f_2449_, 1, v_rhs_2419_);
lean_closure_set(v___f_2449_, 2, v_lhs_2418_);
lean_closure_set(v___f_2449_, 3, v___x_2447_);
lean_closure_set(v___f_2449_, 4, v___x_2448_);
v___x_2450_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_a_2444_, v_a_2446_, v___f_2449_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2452_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2451_);
lean_dec_ref(v___x_2450_);
v___x_2452_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_f_2415_, v_g_2416_, v___x_2441_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2454_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
lean_dec_ref(v___x_2452_);
v___x_2454_ = l_Lean_Meta_mkEqNDRec(v_a_2451_, v_a_2440_, v_a_2453_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2456_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
lean_dec_ref(v___x_2454_);
v___x_2456_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_2455_, v_heq_2420_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
return v___x_2456_;
}
else
{
return v___x_2454_;
}
}
else
{
lean_dec(v_a_2451_);
lean_dec(v_a_2440_);
return v___x_2452_;
}
}
else
{
lean_dec(v_a_2440_);
lean_dec_ref(v_g_2416_);
lean_dec_ref(v_f_2415_);
return v___x_2450_;
}
}
else
{
lean_dec(v_a_2444_);
lean_dec(v_a_2440_);
lean_dec_ref(v_rhs_2419_);
lean_dec_ref(v_lhs_2418_);
lean_dec(v_numArgs_2417_);
lean_dec_ref(v_g_2416_);
lean_dec_ref(v_f_2415_);
return v___x_2445_;
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_dec(v_a_2440_);
lean_dec_ref(v_rhs_2419_);
lean_dec_ref(v_lhs_2418_);
lean_dec(v_numArgs_2417_);
lean_dec_ref(v_g_2416_);
lean_dec_ref(v_f_2415_);
v_a_2457_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2443_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2443_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
else
{
lean_object* v___x_2465_; 
lean_dec_ref(v_rhs_2419_);
lean_dec_ref(v_lhs_2418_);
lean_dec(v_numArgs_2417_);
lean_dec_ref(v_g_2416_);
lean_dec_ref(v_f_2415_);
v___x_2465_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_2440_, v_heq_2420_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
return v___x_2465_;
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
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec_ref(v_rhs_2419_);
lean_dec_ref(v_lhs_2418_);
lean_dec(v_numArgs_2417_);
lean_dec_ref(v_g_2416_);
lean_dec_ref(v_f_2415_);
v_a_2466_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2432_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2432_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1(void){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2475_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2476_ = lean_unsigned_to_nat(27u);
v___x_2477_ = lean_unsigned_to_nat(237u);
v___x_2478_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0));
v___x_2479_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2480_ = l_mkPanicMessageWithDecl(v___x_2479_, v___x_2478_, v___x_2477_, v___x_2476_, v___x_2475_);
return v___x_2480_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2(void){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2481_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__2));
v___x_2482_ = lean_unsigned_to_nat(27u);
v___x_2483_ = lean_unsigned_to_nat(236u);
v___x_2484_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0));
v___x_2485_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___closed__0));
v___x_2486_ = l_mkPanicMessageWithDecl(v___x_2485_, v___x_2484_, v___x_2483_, v___x_2482_, v___x_2481_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(lean_object* v_lhs_2487_, lean_object* v_rhs_2488_, uint8_t v_heq_2489_, lean_object* v_e_u2081_2490_, lean_object* v_e_u2082_2491_, lean_object* v_numArgs_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_){
_start:
{
if (lean_obj_tag(v_e_u2081_2490_) == 5)
{
if (lean_obj_tag(v_e_u2082_2491_) == 5)
{
lean_object* v_fn_2504_; lean_object* v_fn_2505_; lean_object* v___x_2506_; lean_object* v_numArgs_2507_; uint8_t v___x_2508_; 
v_fn_2504_ = lean_ctor_get(v_e_u2081_2490_, 0);
lean_inc_ref(v_fn_2504_);
lean_dec_ref(v_e_u2081_2490_);
v_fn_2505_ = lean_ctor_get(v_e_u2082_2491_, 0);
lean_inc_ref(v_fn_2505_);
lean_dec_ref(v_e_u2082_2491_);
v___x_2506_ = lean_unsigned_to_nat(1u);
v_numArgs_2507_ = lean_nat_add(v_numArgs_2492_, v___x_2506_);
lean_dec(v_numArgs_2492_);
v___x_2508_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_2504_, v_fn_2505_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; 
lean_inc_ref(v_fn_2505_);
lean_inc_ref(v_fn_2504_);
v___x_2509_ = l_Lean_Meta_Grind_hasSameType(v_fn_2504_, v_fn_2505_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; uint8_t v___x_2511_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_a_2510_);
lean_dec_ref(v___x_2509_);
v___x_2511_ = lean_unbox(v_a_2510_);
lean_dec(v_a_2510_);
if (v___x_2511_ == 0)
{
v_e_u2081_2490_ = v_fn_2504_;
v_e_u2082_2491_ = v_fn_2505_;
v_numArgs_2492_ = v_numArgs_2507_;
goto _start;
}
else
{
lean_object* v___x_2513_; 
v___x_2513_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_2504_, v_fn_2505_, v_numArgs_2507_, v_lhs_2487_, v_rhs_2488_, v_heq_2489_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_);
return v___x_2513_;
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec(v_numArgs_2507_);
lean_dec_ref(v_fn_2505_);
lean_dec_ref(v_fn_2504_);
lean_dec_ref(v_rhs_2488_);
lean_dec_ref(v_lhs_2487_);
v_a_2514_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2509_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2509_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
else
{
lean_object* v___x_2522_; 
v___x_2522_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_2504_, v_fn_2505_, v_numArgs_2507_, v_lhs_2487_, v_rhs_2488_, v_heq_2489_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_);
return v___x_2522_;
}
}
else
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
lean_dec_ref(v_e_u2081_2490_);
lean_dec(v_numArgs_2492_);
lean_dec_ref(v_e_u2082_2491_);
lean_dec_ref(v_rhs_2488_);
lean_dec_ref(v_lhs_2487_);
v___x_2523_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1);
v___x_2524_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2523_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_);
return v___x_2524_;
}
}
else
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
lean_dec(v_numArgs_2492_);
lean_dec_ref(v_e_u2082_2491_);
lean_dec_ref(v_e_u2081_2490_);
lean_dec_ref(v_rhs_2488_);
lean_dec_ref(v_lhs_2487_);
v___x_2525_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2);
v___x_2526_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_2525_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_);
return v___x_2526_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(lean_object* v_lhs_2527_, lean_object* v_rhs_2528_, uint8_t v_heq_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_rhs_2528_);
lean_inc_ref(v_lhs_2527_);
v___x_2542_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(v_lhs_2527_, v_rhs_2528_, v_heq_2529_, v_lhs_2527_, v_rhs_2528_, v___x_2541_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC___boxed(lean_object* v_lhs_2543_, lean_object* v_rhs_2544_, lean_object* v_heq_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
uint8_t v_heq_boxed_2557_; lean_object* v_res_2558_; 
v_heq_boxed_2557_ = lean_unbox(v_heq_2545_);
v_res_2558_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_2543_, v_rhs_2544_, v_heq_boxed_2557_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
lean_dec(v_a_2547_);
lean_dec(v_a_2546_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___boxed(lean_object* v_lhs_2559_, lean_object* v_rhs_2560_, lean_object* v_heq_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
uint8_t v_heq_boxed_2573_; lean_object* v_res_2574_; 
v_heq_boxed_2573_ = lean_unbox(v_heq_2561_);
v_res_2574_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_2559_, v_rhs_2560_, v_heq_boxed_2573_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
lean_dec(v_a_2565_);
lean_dec_ref(v_a_2564_);
lean_dec(v_a_2563_);
lean_dec(v_a_2562_);
lean_dec_ref(v_rhs_2560_);
lean_dec_ref(v_lhs_2559_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___boxed(lean_object* v_lhs_2575_, lean_object* v_rhs_2576_, lean_object* v_heq_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
uint8_t v_heq_boxed_2589_; lean_object* v_res_2590_; 
v_heq_boxed_2589_ = lean_unbox(v_heq_2577_);
v_res_2590_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_2575_, v_rhs_2576_, v_heq_boxed_2589_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
lean_dec(v_a_2583_);
lean_dec_ref(v_a_2582_);
lean_dec(v_a_2581_);
lean_dec_ref(v_a_2580_);
lean_dec(v_a_2579_);
lean_dec(v_a_2578_);
lean_dec_ref(v_rhs_2576_);
lean_dec_ref(v_lhs_2575_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof___boxed(lean_object* v_lhs_2591_, lean_object* v_rhs_2592_, lean_object* v_h_2593_, lean_object* v_flipped_2594_, lean_object* v_heq_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_){
_start:
{
uint8_t v_flipped_boxed_2607_; uint8_t v_heq_boxed_2608_; lean_object* v_res_2609_; 
v_flipped_boxed_2607_ = lean_unbox(v_flipped_2594_);
v_heq_boxed_2608_ = lean_unbox(v_heq_2595_);
v_res_2609_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(v_lhs_2591_, v_rhs_2592_, v_h_2593_, v_flipped_boxed_2607_, v_heq_boxed_2608_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
lean_dec(v_a_2597_);
lean_dec(v_a_2596_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___boxed(lean_object* v_lhs_2610_, lean_object* v_rhs_2611_, lean_object* v_heq_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_){
_start:
{
uint8_t v_heq_boxed_2624_; lean_object* v_res_2625_; 
v_heq_boxed_2624_ = lean_unbox(v_heq_2612_);
v_res_2625_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_2610_, v_rhs_2611_, v_heq_boxed_2624_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
lean_dec(v_a_2618_);
lean_dec_ref(v_a_2617_);
lean_dec(v_a_2616_);
lean_dec_ref(v_a_2615_);
lean_dec(v_a_2614_);
lean_dec(v_a_2613_);
lean_dec_ref(v_rhs_2611_);
lean_dec_ref(v_lhs_2610_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper___boxed(lean_object* v_thm_2626_, lean_object* v_lhs_2627_, lean_object* v_rhs_2628_, lean_object* v_i_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_2626_, v_lhs_2627_, v_rhs_2628_, v_i_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_);
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
lean_dec(v_i_2629_);
lean_dec_ref(v_rhs_2628_);
lean_dec_ref(v_lhs_2627_);
lean_dec_ref(v_thm_2626_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___boxed(lean_object** _args){
lean_object* v_lhs_2642_ = _args[0];
lean_object* v_rhs_2643_ = _args[1];
lean_object* v_heq_2644_ = _args[2];
lean_object* v_e_u2081_2645_ = _args[3];
lean_object* v_e_u2082_2646_ = _args[4];
lean_object* v_numArgs_2647_ = _args[5];
lean_object* v_a_2648_ = _args[6];
lean_object* v_a_2649_ = _args[7];
lean_object* v_a_2650_ = _args[8];
lean_object* v_a_2651_ = _args[9];
lean_object* v_a_2652_ = _args[10];
lean_object* v_a_2653_ = _args[11];
lean_object* v_a_2654_ = _args[12];
lean_object* v_a_2655_ = _args[13];
lean_object* v_a_2656_ = _args[14];
lean_object* v_a_2657_ = _args[15];
lean_object* v_a_2658_ = _args[16];
_start:
{
uint8_t v_heq_boxed_2659_; lean_object* v_res_2660_; 
v_heq_boxed_2659_ = lean_unbox(v_heq_2644_);
v_res_2660_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(v_lhs_2642_, v_rhs_2643_, v_heq_boxed_2659_, v_e_u2081_2645_, v_e_u2082_2646_, v_numArgs_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
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
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___boxed(lean_object* v_lhs_2661_, lean_object* v_common_2662_, lean_object* v_acc_2663_, lean_object* v_heq_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
uint8_t v_heq_boxed_2676_; lean_object* v_res_2677_; 
v_heq_boxed_2676_ = lean_unbox(v_heq_2664_);
v_res_2677_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_2661_, v_common_2662_, v_acc_2663_, v_heq_boxed_2676_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
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
lean_dec_ref(v_common_2662_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___boxed(lean_object** _args){
lean_object* v_f_2678_ = _args[0];
lean_object* v_g_2679_ = _args[1];
lean_object* v_numArgs_2680_ = _args[2];
lean_object* v_lhs_2681_ = _args[3];
lean_object* v_rhs_2682_ = _args[4];
lean_object* v_heq_2683_ = _args[5];
lean_object* v_a_2684_ = _args[6];
lean_object* v_a_2685_ = _args[7];
lean_object* v_a_2686_ = _args[8];
lean_object* v_a_2687_ = _args[9];
lean_object* v_a_2688_ = _args[10];
lean_object* v_a_2689_ = _args[11];
lean_object* v_a_2690_ = _args[12];
lean_object* v_a_2691_ = _args[13];
lean_object* v_a_2692_ = _args[14];
lean_object* v_a_2693_ = _args[15];
lean_object* v_a_2694_ = _args[16];
_start:
{
uint8_t v_heq_boxed_2695_; lean_object* v_res_2696_; 
v_heq_boxed_2695_ = lean_unbox(v_heq_2683_);
v_res_2696_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_2678_, v_g_2679_, v_numArgs_2680_, v_lhs_2681_, v_rhs_2682_, v_heq_boxed_2695_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
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
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___boxed(lean_object* v_rhs_2697_, lean_object* v_common_2698_, lean_object* v_lhsEqCommon_x3f_2699_, lean_object* v_heq_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_){
_start:
{
uint8_t v_heq_boxed_2712_; lean_object* v_res_2713_; 
v_heq_boxed_2712_ = lean_unbox(v_heq_2700_);
v_res_2713_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_2697_, v_common_2698_, v_lhsEqCommon_x3f_2699_, v_heq_boxed_2712_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
lean_dec(v_a_2708_);
lean_dec_ref(v_a_2707_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
lean_dec(v_a_2702_);
lean_dec(v_a_2701_);
lean_dec_ref(v_common_2698_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop___boxed(lean_object* v_lhs_2714_, lean_object* v_rhs_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_2714_, v_rhs_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_);
lean_dec(v_a_2725_);
lean_dec_ref(v_a_2724_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec(v_a_2716_);
lean_dec_ref(v_rhs_2715_);
lean_dec_ref(v_lhs_2714_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___boxed(lean_object* v_lhs_2728_, lean_object* v_rhs_2729_, lean_object* v_heq_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_){
_start:
{
uint8_t v_heq_boxed_2742_; lean_object* v_res_2743_; 
v_heq_boxed_2742_ = lean_unbox(v_heq_2730_);
v_res_2743_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_2728_, v_rhs_2729_, v_heq_boxed_2742_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_);
lean_dec(v_a_2740_);
lean_dec_ref(v_a_2739_);
lean_dec(v_a_2738_);
lean_dec_ref(v_a_2737_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
lean_dec(v_a_2732_);
lean_dec(v_a_2731_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___boxed(lean_object* v_lhs_2744_, lean_object* v_rhs_2745_, lean_object* v_heq_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_){
_start:
{
uint8_t v_heq_boxed_2758_; lean_object* v_res_2759_; 
v_heq_boxed_2758_ = lean_unbox(v_heq_2746_);
v_res_2759_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_lhs_2744_, v_rhs_2745_, v_heq_boxed_2758_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_);
lean_dec(v_a_2756_);
lean_dec_ref(v_a_2755_);
lean_dec(v_a_2754_);
lean_dec_ref(v_a_2753_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_a_2748_);
lean_dec(v_a_2747_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrProof___boxed(lean_object* v_lhs_2760_, lean_object* v_rhs_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_Meta_Grind_mkEqCongrProof(v_lhs_2760_, v_rhs_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_);
lean_dec(v_a_2771_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_a_2765_);
lean_dec_ref(v_a_2764_);
lean_dec(v_a_2763_);
lean_dec(v_a_2762_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqCongrSymmProof___boxed(lean_object* v_lhs_2774_, lean_object* v_rhs_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(v_lhs_2774_, v_rhs_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
lean_dec(v_a_2785_);
lean_dec(v_a_2783_);
lean_dec_ref(v_a_2782_);
lean_dec(v_a_2781_);
lean_dec_ref(v_a_2780_);
lean_dec(v_a_2779_);
lean_dec_ref(v_a_2778_);
lean_dec(v_a_2777_);
lean_dec(v_a_2776_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___boxed(lean_object* v_lhs_2788_, lean_object* v_rhs_2789_, lean_object* v_heq_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
uint8_t v_heq_boxed_2802_; lean_object* v_res_2803_; 
v_heq_boxed_2802_ = lean_unbox(v_heq_2790_);
v_res_2803_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(v_lhs_2788_, v_rhs_2789_, v_heq_boxed_2802_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
lean_dec(v_a_2796_);
lean_dec_ref(v_a_2795_);
lean_dec(v_a_2794_);
lean_dec_ref(v_a_2793_);
lean_dec(v_a_2792_);
lean_dec(v_a_2791_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(lean_object* v_00_u03b1_2804_, lean_object* v_ref_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_2805_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___boxed(lean_object* v_00_u03b1_2818_, lean_object* v_ref_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(v_00_u03b1_2818_, v_ref_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec(v___y_2820_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(lean_object* v_00_u03b1_2832_, lean_object* v_name_2833_, uint8_t v_bi_2834_, lean_object* v_type_2835_, lean_object* v_k_2836_, uint8_t v_kind_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v___x_2849_; 
v___x_2849_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_2833_, v_bi_2834_, v_type_2835_, v_k_2836_, v_kind_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___boxed(lean_object** _args){
lean_object* v_00_u03b1_2850_ = _args[0];
lean_object* v_name_2851_ = _args[1];
lean_object* v_bi_2852_ = _args[2];
lean_object* v_type_2853_ = _args[3];
lean_object* v_k_2854_ = _args[4];
lean_object* v_kind_2855_ = _args[5];
lean_object* v___y_2856_ = _args[6];
lean_object* v___y_2857_ = _args[7];
lean_object* v___y_2858_ = _args[8];
lean_object* v___y_2859_ = _args[9];
lean_object* v___y_2860_ = _args[10];
lean_object* v___y_2861_ = _args[11];
lean_object* v___y_2862_ = _args[12];
lean_object* v___y_2863_ = _args[13];
lean_object* v___y_2864_ = _args[14];
lean_object* v___y_2865_ = _args[15];
lean_object* v___y_2866_ = _args[16];
_start:
{
uint8_t v_bi_boxed_2867_; uint8_t v_kind_boxed_2868_; lean_object* v_res_2869_; 
v_bi_boxed_2867_ = lean_unbox(v_bi_2852_);
v_kind_boxed_2868_ = lean_unbox(v_kind_2855_);
v_res_2869_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(v_00_u03b1_2850_, v_name_2851_, v_bi_boxed_2867_, v_type_2853_, v_k_2854_, v_kind_boxed_2868_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec(v___y_2857_);
lean_dec(v___y_2856_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(lean_object* v_00_u03b1_2870_, lean_object* v_name_2871_, lean_object* v_type_2872_, lean_object* v_k_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v___x_2885_; 
v___x_2885_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_name_2871_, v_type_2872_, v_k_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___boxed(lean_object* v_00_u03b1_2886_, lean_object* v_name_2887_, lean_object* v_type_2888_, lean_object* v_k_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(v_00_u03b1_2886_, v_name_2887_, v_type_2888_, v_k_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec(v___y_2890_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(lean_object* v_00_u03b1_2902_, lean_object* v_msg_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v_msg_2903_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___boxed(lean_object* v_00_u03b1_2916_, lean_object* v_msg_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(v_00_u03b1_2916_, v_msg_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec(v___y_2918_);
return v_res_2929_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__1(void){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__0));
v___x_2932_ = l_Lean_stringToMessageData(v___x_2931_);
return v___x_2932_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__3(void){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2934_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__2));
v___x_2935_ = l_Lean_stringToMessageData(v___x_2934_);
return v___x_2935_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__5(void){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2937_ = ((lean_object*)(l_Lean_Meta_Grind_mkEqProofImpl___closed__4));
v___x_2938_ = l_Lean_stringToMessageData(v___x_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* lean_grind_mk_eq_proof(lean_object* v_a_2939_, lean_object* v_b_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_){
_start:
{
lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___x_2965_; 
lean_inc_ref(v_b_2940_);
lean_inc_ref(v_a_2939_);
v___x_2965_ = l_Lean_Meta_Grind_hasSameType(v_a_2939_, v_b_2940_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; uint8_t v___x_2967_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2966_);
lean_dec_ref(v___x_2965_);
v___x_2967_ = lean_unbox(v_a_2966_);
lean_dec(v_a_2966_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; 
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
lean_dec(v_a_2942_);
lean_dec(v_a_2941_);
lean_inc(v_a_2950_);
lean_inc_ref(v_a_2949_);
lean_inc(v_a_2948_);
lean_inc_ref(v_a_2947_);
lean_inc_ref(v_a_2939_);
v___x_2968_ = lean_infer_type(v_a_2939_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2970_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_a_2969_);
lean_dec_ref(v___x_2968_);
lean_inc(v_a_2950_);
lean_inc_ref(v_a_2949_);
lean_inc(v_a_2948_);
lean_inc_ref(v_a_2947_);
lean_inc_ref(v_b_2940_);
v___x_2970_ = lean_infer_type(v_b_2940_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v_a_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_a_2971_);
lean_dec_ref(v___x_2970_);
v___x_2972_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__1, &l_Lean_Meta_Grind_mkEqProofImpl___closed__1_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__1);
v___x_2973_ = l_Lean_indentExpr(v_a_2939_);
v___x_2974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2972_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
v___x_2975_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__3, &l_Lean_Meta_Grind_mkEqProofImpl___closed__3_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__3);
v___x_2976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2974_);
lean_ctor_set(v___x_2976_, 1, v___x_2975_);
v___x_2977_ = l_Lean_indentExpr(v_a_2969_);
v___x_2978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2976_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
v___x_2979_ = lean_obj_once(&l_Lean_Meta_Grind_mkEqProofImpl___closed__5, &l_Lean_Meta_Grind_mkEqProofImpl___closed__5_once, _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__5);
v___x_2980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2978_);
lean_ctor_set(v___x_2980_, 1, v___x_2979_);
v___x_2981_ = l_Lean_indentExpr(v_b_2940_);
v___x_2982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2980_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
v___x_2983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2982_);
lean_ctor_set(v___x_2983_, 1, v___x_2975_);
v___x_2984_ = l_Lean_indentExpr(v_a_2971_);
v___x_2985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2983_);
lean_ctor_set(v___x_2985_, 1, v___x_2984_);
v___x_2986_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v___x_2985_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_);
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2989_ = v___x_2986_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2986_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
else
{
lean_dec(v_a_2969_);
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
lean_dec_ref(v_b_2940_);
lean_dec_ref(v_a_2939_);
return v___x_2970_;
}
}
else
{
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
lean_dec_ref(v_b_2940_);
lean_dec_ref(v_a_2939_);
return v___x_2968_;
}
}
else
{
v___y_2953_ = v_a_2941_;
v___y_2954_ = v_a_2942_;
v___y_2955_ = v_a_2943_;
v___y_2956_ = v_a_2944_;
v___y_2957_ = v_a_2945_;
v___y_2958_ = v_a_2946_;
v___y_2959_ = v_a_2947_;
v___y_2960_ = v_a_2948_;
v___y_2961_ = v_a_2949_;
v___y_2962_ = v_a_2950_;
goto v___jp_2952_;
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
lean_dec(v_a_2942_);
lean_dec(v_a_2941_);
lean_dec_ref(v_b_2940_);
lean_dec_ref(v_a_2939_);
v_a_2995_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2965_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2965_);
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
v___jp_2952_:
{
uint8_t v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = 0;
v___x_2964_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_2939_, v_b_2940_, v___x_2963_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec(v___y_2954_);
lean_dec(v___y_2953_);
return v___x_2964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqProofImpl___boxed(lean_object* v_a_3003_, lean_object* v_b_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = lean_grind_mk_eq_proof(v_a_3003_, v_b_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* lean_grind_mk_heq_proof(lean_object* v_a_3017_, lean_object* v_b_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_){
_start:
{
uint8_t v___x_3030_; lean_object* v___x_3031_; 
v___x_3030_ = 1;
v___x_3031_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_3017_, v_b_3018_, v___x_3030_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_);
lean_dec(v_a_3028_);
lean_dec_ref(v_a_3027_);
lean_dec(v_a_3026_);
lean_dec_ref(v_a_3025_);
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
lean_dec(v_a_3022_);
lean_dec_ref(v_a_3021_);
lean_dec(v_a_3020_);
lean_dec(v_a_3019_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHEqProofImpl___boxed(lean_object* v_a_3032_, lean_object* v_b_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = lean_grind_mk_heq_proof(v_a_3032_, v_b_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_);
return v_res_3045_;
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
