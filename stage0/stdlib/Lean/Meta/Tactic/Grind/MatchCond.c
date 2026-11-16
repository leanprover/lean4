// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.MatchCond
// Imports: import Init.Grind import Lean.Meta.Tactic.Contradiction import Lean.Meta.Tactic.Grind.ProveEq public import Lean.Meta.Tactic.Grind.PropagatorAttr
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_proveEq_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_proveHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isBVar(lean_object*);
lean_object* l_Lean_Meta_Grind_registerParent___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_normLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_heq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg(lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ty"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(73, 30, 115, 12, 44, 231, 45, 94)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "MatchCond"};
static const lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__3_value),LEAN_SCALAR_PTR_LITERAL(109, 233, 187, 249, 156, 65, 204, 232)}};
static const lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchCond"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(181, 170, 56, 23, 185, 62, 169, 45)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "satifised"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__7 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__7_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "\nthe following equality is false"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__9 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__9_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "found term that has not been internalized"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "\nwhile trying to construct a proof for `MatchCond`"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "go\?: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ">>> "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "proveFalse"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(181, 170, 56, 23, 185, 62, 169, 45)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 57, 131, 114, 246, 81, 253, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " =\?= "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_tryToProveFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1_value)} };
static const lean_object* l_Lean_Meta_Grind_tryToProveFalse___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_tryToProveFalse___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateMatchCondUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "failed to construct proof for"};
static const lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateMatchCondUp___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateMatchCondUp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___closed__1;
static const lean_string_object l_Lean_Meta_Grind_propagateMatchCondUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "visiting"};
static const lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateMatchCondUp___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateMatchCondUp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(lean_object* v_e_7_){
_start:
{
lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_8_ = l_Lean_Expr_cleanupAnnotations(v_e_7_);
v___x_9_ = l_Lean_Expr_isApp(v___x_8_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; 
lean_dec_ref(v___x_8_);
v___x_10_ = lean_box(0);
return v___x_10_;
}
else
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = l_Lean_Expr_appFnCleanup___redArg(v___x_8_);
v___x_12_ = l_Lean_Expr_isApp(v___x_11_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; 
lean_dec_ref(v___x_11_);
lean_dec_ref(v___x_8_);
v___x_13_ = lean_box(0);
return v___x_13_;
}
else
{
lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_14_ = l_Lean_Expr_appFnCleanup___redArg(v___x_11_);
v___x_15_ = l_Lean_Expr_isApp(v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; 
lean_dec_ref(v___x_14_);
lean_dec_ref(v___x_11_);
lean_dec_ref(v___x_8_);
v___x_16_ = lean_box(0);
return v___x_16_;
}
else
{
lean_object* v_arg_17_; lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v_arg_17_ = lean_ctor_get(v___x_8_, 1);
lean_inc_ref(v_arg_17_);
lean_dec_ref(v___x_8_);
v___x_18_ = l_Lean_Expr_appFnCleanup___redArg(v___x_14_);
v___x_19_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1));
v___x_20_ = l_Lean_Expr_isConstOf(v___x_18_, v___x_19_);
if (v___x_20_ == 0)
{
uint8_t v___x_21_; 
lean_dec_ref(v___x_11_);
v___x_21_ = l_Lean_Expr_isApp(v___x_18_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; 
lean_dec_ref(v___x_18_);
lean_dec_ref(v_arg_17_);
lean_dec_ref(v___x_14_);
v___x_22_ = lean_box(0);
return v___x_22_;
}
else
{
lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_23_ = l_Lean_Expr_appFnCleanup___redArg(v___x_18_);
v___x_24_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3));
v___x_25_ = l_Lean_Expr_isConstOf(v___x_23_, v___x_24_);
lean_dec_ref(v___x_23_);
if (v___x_25_ == 0)
{
lean_object* v___x_26_; 
lean_dec_ref(v___x_18_);
lean_dec_ref(v_arg_17_);
lean_dec_ref(v___x_14_);
v___x_26_ = lean_box(0);
return v___x_26_;
}
else
{
lean_object* v_arg_27_; lean_object* v_arg_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_arg_27_ = lean_ctor_get(v___x_14_, 1);
lean_inc_ref(v_arg_27_);
lean_dec_ref(v___x_14_);
v_arg_28_ = lean_ctor_get(v___x_18_, 1);
lean_inc_ref(v_arg_28_);
lean_dec_ref(v___x_18_);
v___x_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_29_, 0, v_arg_28_);
v___x_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_30_, 0, v_arg_27_);
lean_ctor_set(v___x_30_, 1, v_arg_17_);
v___x_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_31_, 0, v___x_29_);
lean_ctor_set(v___x_31_, 1, v___x_30_);
v___x_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
}
else
{
lean_object* v_arg_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec_ref(v___x_18_);
lean_dec_ref(v___x_14_);
v_arg_33_ = lean_ctor_get(v___x_11_, 1);
lean_inc_ref(v_arg_33_);
lean_dec_ref(v___x_11_);
v___x_34_ = lean_box(0);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v_arg_33_);
lean_ctor_set(v___x_35_, 1, v_arg_17_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_34_);
lean_ctor_set(v___x_36_, 1, v___x_35_);
v___x_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
return v___x_37_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___boxed(lean_object* v_e_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_e_38_);
lean_dec_ref(v_e_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg___lam__0(lean_object* v_body_40_, lean_object* v___x_41_, lean_object* v_____r_42_, lean_object* v_r_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_44_, 0, v_r_43_);
lean_ctor_set(v___x_44_, 1, v_body_40_);
v___x_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_41_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
v___x_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg(lean_object* v_a_47_){
_start:
{
lean_object* v___y_49_; lean_object* v_snd_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_96_; 
v_snd_53_ = lean_ctor_get(v_a_47_, 1);
v_isSharedCheck_96_ = !lean_is_exclusive(v_a_47_);
if (v_isSharedCheck_96_ == 0)
{
lean_object* v_unused_97_; 
v_unused_97_ = lean_ctor_get(v_a_47_, 0);
lean_dec(v_unused_97_);
v___x_55_ = v_a_47_;
v_isShared_56_ = v_isSharedCheck_96_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_snd_53_);
lean_dec(v_a_47_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_96_;
goto v_resetjp_54_;
}
v___jp_48_:
{
if (lean_obj_tag(v___y_49_) == 0)
{
lean_object* v_a_50_; 
v_a_50_ = lean_ctor_get(v___y_49_, 0);
lean_inc(v_a_50_);
lean_dec_ref_known(v___y_49_, 1);
return v_a_50_;
}
else
{
lean_object* v_a_51_; 
v_a_51_ = lean_ctor_get(v___y_49_, 0);
lean_inc(v_a_51_);
lean_dec_ref_known(v___y_49_, 1);
v_a_47_ = v_a_51_;
goto _start;
}
}
v_resetjp_54_:
{
lean_object* v_snd_57_; 
v_snd_57_ = lean_ctor_get(v_snd_53_, 1);
lean_inc(v_snd_57_);
if (lean_obj_tag(v_snd_57_) == 7)
{
lean_object* v_fst_58_; lean_object* v_binderType_59_; lean_object* v_body_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
lean_del_object(v___x_55_);
v_fst_58_ = lean_ctor_get(v_snd_53_, 0);
lean_inc(v_fst_58_);
lean_dec(v_snd_53_);
v_binderType_59_ = lean_ctor_get(v_snd_57_, 1);
lean_inc_ref(v_binderType_59_);
v_body_60_ = lean_ctor_get(v_snd_57_, 2);
lean_inc_ref(v_body_60_);
lean_dec_ref_known(v_snd_57_, 3);
v___x_61_ = lean_box(0);
v___x_62_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_binderType_59_);
lean_dec_ref(v_binderType_59_);
if (lean_obj_tag(v___x_62_) == 1)
{
lean_object* v_val_63_; lean_object* v_snd_64_; lean_object* v_fst_65_; lean_object* v_fst_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_79_; 
v_val_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc(v_val_63_);
lean_dec_ref_known(v___x_62_, 1);
v_snd_64_ = lean_ctor_get(v_val_63_, 1);
lean_inc(v_snd_64_);
v_fst_65_ = lean_ctor_get(v_val_63_, 0);
lean_inc(v_fst_65_);
lean_dec(v_val_63_);
v_fst_66_ = lean_ctor_get(v_snd_64_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v_snd_64_);
if (v_isSharedCheck_79_ == 0)
{
lean_object* v_unused_80_; 
v_unused_80_ = lean_ctor_get(v_snd_64_, 1);
lean_dec(v_unused_80_);
v___x_68_ = v_snd_64_;
v_isShared_69_ = v_isSharedCheck_79_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_fst_66_);
lean_dec(v_snd_64_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_79_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
uint8_t v___x_70_; 
v___x_70_ = l_Lean_Expr_hasLooseBVars(v_fst_66_);
if (v___x_70_ == 0)
{
lean_object* v___x_72_; 
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 1, v_fst_65_);
v___x_72_ = v___x_68_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_fst_66_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v_fst_65_);
v___x_72_ = v_reuseFailAlloc_76_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = lean_array_push(v_fst_58_, v___x_72_);
v___x_74_ = lean_box(0);
v___x_75_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg___lam__0(v_body_60_, v___x_61_, v___x_74_, v___x_73_);
v___y_49_ = v___x_75_;
goto v___jp_48_;
}
}
else
{
lean_object* v___x_77_; lean_object* v___x_78_; 
lean_del_object(v___x_68_);
lean_dec(v_fst_66_);
lean_dec(v_fst_65_);
v___x_77_ = lean_box(0);
v___x_78_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg___lam__0(v_body_60_, v___x_61_, v___x_77_, v_fst_58_);
v___y_49_ = v___x_78_;
goto v___jp_48_;
}
}
}
else
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v___x_62_);
v___x_81_ = lean_box(0);
v___x_82_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg___lam__0(v_body_60_, v___x_61_, v___x_81_, v_fst_58_);
v___y_49_ = v___x_82_;
goto v___jp_48_;
}
}
else
{
lean_object* v_fst_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_94_; 
v_fst_83_ = lean_ctor_get(v_snd_53_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v_snd_53_);
if (v_isSharedCheck_94_ == 0)
{
lean_object* v_unused_95_; 
v_unused_95_ = lean_ctor_get(v_snd_53_, 1);
lean_dec(v_unused_95_);
v___x_85_ = v_snd_53_;
v_isShared_86_ = v_isSharedCheck_94_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_fst_83_);
lean_dec(v_snd_53_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_94_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; lean_object* v___x_89_; 
lean_inc(v_fst_83_);
v___x_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_87_, 0, v_fst_83_);
if (v_isShared_86_ == 0)
{
v___x_89_ = v___x_85_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_fst_83_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_snd_57_);
v___x_89_ = v_reuseFailAlloc_93_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_91_; 
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v___x_89_);
lean_ctor_set(v___x_55_, 0, v___x_87_);
v___x_91_ = v___x_55_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_87_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v___x_89_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss(lean_object* v_e_100_){
_start:
{
lean_object* v_r_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v_fst_106_; 
v_r_101_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss___closed__0));
v___x_102_ = lean_box(0);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v_r_101_);
lean_ctor_set(v___x_103_, 1, v_e_100_);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_102_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg(v___x_104_);
v_fst_106_ = lean_ctor_get(v___x_105_, 0);
if (lean_obj_tag(v_fst_106_) == 0)
{
lean_object* v_snd_107_; lean_object* v_fst_108_; 
v_snd_107_ = lean_ctor_get(v___x_105_, 1);
lean_inc(v_snd_107_);
lean_dec_ref(v___x_105_);
v_fst_108_ = lean_ctor_get(v_snd_107_, 0);
lean_inc(v_fst_108_);
lean_dec(v_snd_107_);
return v_fst_108_;
}
else
{
lean_object* v_val_109_; 
lean_inc_ref(v_fst_106_);
lean_dec_ref(v___x_105_);
v_val_109_ = lean_ctor_get(v_fst_106_, 0);
lean_inc(v_val_109_);
lean_dec_ref_known(v_fst_106_, 1);
return v_val_109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0(lean_object* v_inst_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg(v_a_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f_spec__0(lean_object* v_msg_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = l_Lean_instInhabitedExpr;
v___x_115_ = lean_panic_fn_borrowed(v___x_114_, v_msg_113_);
return v___x_115_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_119_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__2));
v___x_120_ = lean_unsigned_to_nat(14u);
v___x_121_ = lean_unsigned_to_nat(22u);
v___x_122_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__1));
v___x_123_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__0));
v___x_124_ = l_mkPanicMessageWithDecl(v___x_123_, v___x_122_, v___x_121_, v___x_120_, v___x_119_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f(lean_object* v_e_125_, lean_object* v_lhsNew_126_, lean_object* v_ty_x3f_127_){
_start:
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = l_Lean_Expr_cleanupAnnotations(v_e_125_);
v___x_129_ = l_Lean_Expr_isApp(v___x_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; 
lean_dec_ref(v___x_128_);
lean_dec(v_ty_x3f_127_);
lean_dec_ref(v_lhsNew_126_);
v___x_130_ = lean_box(0);
return v___x_130_;
}
else
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = l_Lean_Expr_appFnCleanup___redArg(v___x_128_);
v___x_132_ = l_Lean_Expr_isApp(v___x_131_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
lean_dec_ref(v___x_131_);
lean_dec_ref(v___x_128_);
lean_dec(v_ty_x3f_127_);
lean_dec_ref(v_lhsNew_126_);
v___x_133_ = lean_box(0);
return v___x_133_;
}
else
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = l_Lean_Expr_appFnCleanup___redArg(v___x_131_);
v___x_135_ = l_Lean_Expr_isApp(v___x_134_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; 
lean_dec_ref(v___x_134_);
lean_dec_ref(v___x_131_);
lean_dec_ref(v___x_128_);
lean_dec(v_ty_x3f_127_);
lean_dec_ref(v_lhsNew_126_);
v___x_136_ = lean_box(0);
return v___x_136_;
}
else
{
lean_object* v_arg_137_; lean_object* v_arg_138_; lean_object* v_arg_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_arg_137_ = lean_ctor_get(v___x_128_, 1);
lean_inc_ref(v_arg_137_);
lean_dec_ref(v___x_128_);
v_arg_138_ = lean_ctor_get(v___x_131_, 1);
lean_inc_ref(v_arg_138_);
lean_dec_ref(v___x_131_);
v_arg_139_ = lean_ctor_get(v___x_134_, 1);
lean_inc_ref(v_arg_139_);
v___x_140_ = l_Lean_Expr_appFnCleanup___redArg(v___x_134_);
lean_dec_ref(v___x_134_);
v___x_141_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1));
v___x_142_ = l_Lean_Expr_isConstOf(v___x_140_, v___x_141_);
if (v___x_142_ == 0)
{
uint8_t v___x_143_; 
v___x_143_ = l_Lean_Expr_isApp(v___x_140_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; 
lean_dec_ref(v___x_140_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_138_);
lean_dec_ref(v_arg_137_);
lean_dec(v_ty_x3f_127_);
lean_dec_ref(v_lhsNew_126_);
v___x_144_ = lean_box(0);
return v___x_144_;
}
else
{
lean_object* v___x_145_; lean_object* v___y_147_; lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_145_ = l_Lean_Expr_appFnCleanup___redArg(v___x_140_);
lean_dec_ref(v___x_140_);
v___x_150_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3));
v___x_151_ = l_Lean_Expr_isConstOf(v___x_145_, v___x_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; 
lean_dec_ref(v___x_145_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_138_);
lean_dec_ref(v_arg_137_);
lean_dec(v_ty_x3f_127_);
lean_dec_ref(v_lhsNew_126_);
v___x_152_ = lean_box(0);
return v___x_152_;
}
else
{
uint8_t v___x_153_; 
v___x_153_ = l_Lean_Expr_hasLooseBVars(v_arg_139_);
lean_dec_ref(v_arg_139_);
if (v___x_153_ == 0)
{
if (lean_obj_tag(v_ty_x3f_127_) == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3);
v___x_155_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f_spec__0(v___x_154_);
v___y_147_ = v___x_155_;
goto v___jp_146_;
}
else
{
lean_object* v_val_156_; 
v_val_156_ = lean_ctor_get(v_ty_x3f_127_, 0);
lean_inc(v_val_156_);
lean_dec_ref_known(v_ty_x3f_127_, 1);
v___y_147_ = v_val_156_;
goto v___jp_146_;
}
}
else
{
lean_object* v___x_157_; 
lean_dec_ref(v___x_145_);
lean_dec_ref(v_arg_138_);
lean_dec_ref(v_arg_137_);
lean_dec(v_ty_x3f_127_);
lean_dec_ref(v_lhsNew_126_);
v___x_157_ = lean_box(0);
return v___x_157_;
}
}
v___jp_146_:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = l_Lean_mkApp4(v___x_145_, v___y_147_, v_lhsNew_126_, v_arg_138_, v_arg_137_);
v___x_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
return v___x_149_;
}
}
}
else
{
uint8_t v___x_158_; 
lean_dec(v_ty_x3f_127_);
v___x_158_ = l_Lean_Expr_hasLooseBVars(v_arg_138_);
lean_dec_ref(v_arg_138_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = l_Lean_mkApp3(v___x_140_, v_arg_139_, v_lhsNew_126_, v_arg_137_);
v___x_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
else
{
lean_object* v___x_161_; 
lean_dec_ref(v___x_140_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_137_);
lean_dec_ref(v_lhsNew_126_);
v___x_161_ = lean_box(0);
return v___x_161_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___boxed(lean_object* v_e_162_, lean_object* v_lhsNew_163_, lean_object* v_ty_x3f_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f(v_e_162_, v_lhsNew_163_, v_ty_x3f_164_);
lean_dec_ref(v_e_162_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(lean_object* v_xs_166_, lean_object* v_tys_167_, lean_object* v_e_168_, lean_object* v_i_169_){
_start:
{
if (lean_obj_tag(v_e_168_) == 7)
{
lean_object* v_binderName_170_; lean_object* v_binderType_171_; lean_object* v_body_172_; uint8_t v_binderInfo_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v_binderName_170_ = lean_ctor_get(v_e_168_, 0);
v_binderType_171_ = lean_ctor_get(v_e_168_, 1);
v_body_172_ = lean_ctor_get(v_e_168_, 2);
v_binderInfo_173_ = lean_ctor_get_uint8(v_e_168_, sizeof(void*)*3 + 8);
v___x_174_ = lean_array_get_size(v_xs_166_);
v___x_175_ = lean_nat_dec_lt(v_i_169_, v___x_174_);
if (v___x_175_ == 0)
{
return v_e_168_;
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_176_ = lean_box(0);
v___x_177_ = lean_array_fget_borrowed(v_xs_166_, v_i_169_);
v___x_178_ = lean_array_get_borrowed(v___x_176_, v_tys_167_, v_i_169_);
lean_inc(v___x_178_);
lean_inc(v___x_177_);
v___x_179_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f(v_binderType_171_, v___x_177_, v___x_178_);
if (lean_obj_tag(v___x_179_) == 1)
{
lean_object* v_val_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; size_t v___x_184_; size_t v___x_185_; uint8_t v___x_186_; 
v_val_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_val_180_);
lean_dec_ref_known(v___x_179_, 1);
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_add(v_i_169_, v___x_181_);
lean_inc_ref(v_body_172_);
v___x_183_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_166_, v_tys_167_, v_body_172_, v___x_182_);
lean_dec(v___x_182_);
v___x_184_ = lean_ptr_addr(v_binderType_171_);
v___x_185_ = lean_ptr_addr(v_val_180_);
v___x_186_ = lean_usize_dec_eq(v___x_184_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
lean_inc(v_binderName_170_);
lean_dec_ref_known(v_e_168_, 3);
v___x_187_ = l_Lean_Expr_forallE___override(v_binderName_170_, v_val_180_, v___x_183_, v_binderInfo_173_);
return v___x_187_;
}
else
{
size_t v___x_188_; size_t v___x_189_; uint8_t v___x_190_; 
v___x_188_ = lean_ptr_addr(v_body_172_);
v___x_189_ = lean_ptr_addr(v___x_183_);
v___x_190_ = lean_usize_dec_eq(v___x_188_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; 
lean_inc(v_binderName_170_);
lean_dec_ref_known(v_e_168_, 3);
v___x_191_ = l_Lean_Expr_forallE___override(v_binderName_170_, v_val_180_, v___x_183_, v_binderInfo_173_);
return v___x_191_;
}
else
{
uint8_t v___x_192_; 
v___x_192_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_173_, v_binderInfo_173_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; 
lean_inc(v_binderName_170_);
lean_dec_ref_known(v_e_168_, 3);
v___x_193_ = l_Lean_Expr_forallE___override(v_binderName_170_, v_val_180_, v___x_183_, v_binderInfo_173_);
return v___x_193_;
}
else
{
lean_dec_ref(v___x_183_);
lean_dec(v_val_180_);
return v_e_168_;
}
}
}
}
else
{
lean_object* v___x_194_; size_t v___x_195_; size_t v___x_196_; uint8_t v___x_197_; 
lean_dec(v___x_179_);
lean_inc_ref(v_body_172_);
v___x_194_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_166_, v_tys_167_, v_body_172_, v_i_169_);
v___x_195_ = lean_ptr_addr(v_binderType_171_);
v___x_196_ = lean_ptr_addr(v_binderType_171_);
v___x_197_ = lean_usize_dec_eq(v___x_195_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
lean_inc_ref(v_binderType_171_);
lean_inc(v_binderName_170_);
lean_dec_ref_known(v_e_168_, 3);
v___x_198_ = l_Lean_Expr_forallE___override(v_binderName_170_, v_binderType_171_, v___x_194_, v_binderInfo_173_);
return v___x_198_;
}
else
{
size_t v___x_199_; size_t v___x_200_; uint8_t v___x_201_; 
v___x_199_ = lean_ptr_addr(v_body_172_);
v___x_200_ = lean_ptr_addr(v___x_194_);
v___x_201_ = lean_usize_dec_eq(v___x_199_, v___x_200_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; 
lean_inc_ref(v_binderType_171_);
lean_inc(v_binderName_170_);
lean_dec_ref_known(v_e_168_, 3);
v___x_202_ = l_Lean_Expr_forallE___override(v_binderName_170_, v_binderType_171_, v___x_194_, v_binderInfo_173_);
return v___x_202_;
}
else
{
uint8_t v___x_203_; 
v___x_203_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_173_, v_binderInfo_173_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; 
lean_inc_ref(v_binderType_171_);
lean_inc(v_binderName_170_);
lean_dec_ref_known(v_e_168_, 3);
v___x_204_ = l_Lean_Expr_forallE___override(v_binderName_170_, v_binderType_171_, v___x_194_, v_binderInfo_173_);
return v___x_204_;
}
else
{
lean_dec_ref(v___x_194_);
return v_e_168_;
}
}
}
}
}
}
else
{
return v_e_168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss___boxed(lean_object* v_xs_205_, lean_object* v_tys_206_, lean_object* v_e_207_, lean_object* v_i_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_205_, v_tys_206_, v_e_207_, v_i_208_);
lean_dec(v_i_208_);
lean_dec_ref(v_tys_206_);
lean_dec_ref(v_xs_205_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0(lean_object* v_k_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v_b_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___x_223_; 
lean_inc(v___y_221_);
lean_inc_ref(v___y_220_);
lean_inc(v___y_219_);
lean_inc_ref(v___y_218_);
lean_inc(v___y_216_);
lean_inc_ref(v___y_215_);
lean_inc(v___y_214_);
lean_inc_ref(v___y_213_);
lean_inc(v___y_212_);
lean_inc(v___y_211_);
v___x_223_ = lean_apply_12(v_k_210_, v_b_217_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, lean_box(0));
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v_b_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0(v_k_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v_b_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
lean_dec(v___y_225_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(lean_object* v_name_238_, uint8_t v_bi_239_, lean_object* v_type_240_, lean_object* v_k_241_, uint8_t v_kind_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___f_254_; lean_object* v___x_255_; 
lean_inc(v___y_248_);
lean_inc_ref(v___y_247_);
lean_inc(v___y_246_);
lean_inc_ref(v___y_245_);
lean_inc(v___y_244_);
lean_inc(v___y_243_);
v___f_254_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_254_, 0, v_k_241_);
lean_closure_set(v___f_254_, 1, v___y_243_);
lean_closure_set(v___f_254_, 2, v___y_244_);
lean_closure_set(v___f_254_, 3, v___y_245_);
lean_closure_set(v___f_254_, 4, v___y_246_);
lean_closure_set(v___f_254_, 5, v___y_247_);
lean_closure_set(v___f_254_, 6, v___y_248_);
v___x_255_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_238_, v_bi_239_, v_type_240_, v___f_254_, v_kind_242_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
if (lean_obj_tag(v___x_255_) == 0)
{
return v___x_255_;
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_255_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___boxed(lean_object* v_name_264_, lean_object* v_bi_265_, lean_object* v_type_266_, lean_object* v_k_267_, lean_object* v_kind_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
uint8_t v_bi_boxed_280_; uint8_t v_kind_boxed_281_; lean_object* v_res_282_; 
v_bi_boxed_280_ = lean_unbox(v_bi_265_);
v_kind_boxed_281_ = lean_unbox(v_kind_268_);
v_res_282_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_264_, v_bi_boxed_280_, v_type_266_, v_k_267_, v_kind_boxed_281_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
lean_dec(v___y_269_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(lean_object* v_name_283_, lean_object* v_type_284_, lean_object* v_k_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
uint8_t v___x_297_; uint8_t v___x_298_; lean_object* v___x_299_; 
v___x_297_ = 0;
v___x_298_ = 0;
v___x_299_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_283_, v___x_297_, v_type_284_, v_k_285_, v___x_298_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg___boxed(lean_object* v_name_300_, lean_object* v_type_301_, lean_object* v_k_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v_name_300_, v_type_301_, v_k_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec(v___y_303_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed(lean_object** _args){
lean_object* v_i_318_ = _args[0];
lean_object* v_xs_319_ = _args[1];
lean_object* v_tys_320_ = _args[2];
lean_object* v_tysxs_321_ = _args[3];
lean_object* v_args_322_ = _args[4];
lean_object* v_val_323_ = _args[5];
lean_object* v_fst_324_ = _args[6];
lean_object* v_e_325_ = _args[7];
lean_object* v_lhss_u03b1s_326_ = _args[8];
lean_object* v_ty_327_ = _args[9];
lean_object* v___y_328_ = _args[10];
lean_object* v___y_329_ = _args[11];
lean_object* v___y_330_ = _args[12];
lean_object* v___y_331_ = _args[13];
lean_object* v___y_332_ = _args[14];
lean_object* v___y_333_ = _args[15];
lean_object* v___y_334_ = _args[16];
lean_object* v___y_335_ = _args[17];
lean_object* v___y_336_ = _args[18];
lean_object* v___y_337_ = _args[19];
lean_object* v___y_338_ = _args[20];
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(v_i_318_, v_xs_319_, v_tys_320_, v_tysxs_321_, v_args_322_, v_val_323_, v_fst_324_, v_e_325_, v_lhss_u03b1s_326_, v_ty_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v___y_329_);
lean_dec(v___y_328_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(lean_object* v_i_343_, lean_object* v_xs_344_, lean_object* v_tys_345_, lean_object* v_tysxs_346_, lean_object* v_args_347_, lean_object* v_fst_348_, lean_object* v_e_349_, lean_object* v_lhss_u03b1s_350_, lean_object* v_x_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_363_ = lean_unsigned_to_nat(1u);
v___x_364_ = lean_nat_add(v_i_343_, v___x_363_);
lean_inc_ref(v_x_351_);
v___x_365_ = lean_array_push(v_xs_344_, v_x_351_);
v___x_366_ = lean_box(0);
v___x_367_ = lean_array_push(v_tys_345_, v___x_366_);
v___x_368_ = lean_array_push(v_tysxs_346_, v_x_351_);
v___x_369_ = lean_array_push(v_args_347_, v_fst_348_);
v___x_370_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_349_, v_lhss_u03b1s_350_, v___x_364_, v___x_365_, v___x_367_, v___x_368_, v___x_369_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed(lean_object** _args){
lean_object* v_i_371_ = _args[0];
lean_object* v_xs_372_ = _args[1];
lean_object* v_tys_373_ = _args[2];
lean_object* v_tysxs_374_ = _args[3];
lean_object* v_args_375_ = _args[4];
lean_object* v_fst_376_ = _args[5];
lean_object* v_e_377_ = _args[6];
lean_object* v_lhss_u03b1s_378_ = _args[7];
lean_object* v_x_379_ = _args[8];
lean_object* v___y_380_ = _args[9];
lean_object* v___y_381_ = _args[10];
lean_object* v___y_382_ = _args[11];
lean_object* v___y_383_ = _args[12];
lean_object* v___y_384_ = _args[13];
lean_object* v___y_385_ = _args[14];
lean_object* v___y_386_ = _args[15];
lean_object* v___y_387_ = _args[16];
lean_object* v___y_388_ = _args[17];
lean_object* v___y_389_ = _args[18];
lean_object* v___y_390_ = _args[19];
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(v_i_371_, v_xs_372_, v_tys_373_, v_tysxs_374_, v_args_375_, v_fst_376_, v_e_377_, v_lhss_u03b1s_378_, v_x_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec(v___y_380_);
lean_dec(v_i_371_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(lean_object* v_e_392_, lean_object* v_lhss_u03b1s_393_, lean_object* v_i_394_, lean_object* v_xs_395_, lean_object* v_tys_396_, lean_object* v_tysxs_397_, lean_object* v_args_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_array_get_size(v_lhss_u03b1s_393_);
v___x_411_ = lean_nat_dec_lt(v_i_394_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v_eAbst_413_; uint8_t v___x_414_; uint8_t v___x_415_; lean_object* v___x_416_; 
lean_dec(v_i_394_);
lean_dec_ref(v_lhss_u03b1s_393_);
v___x_412_ = lean_unsigned_to_nat(0u);
v_eAbst_413_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_395_, v_tys_396_, v_e_392_, v___x_412_);
lean_dec_ref(v_tys_396_);
lean_dec_ref(v_xs_395_);
v___x_414_ = 1;
v___x_415_ = 1;
v___x_416_ = l_Lean_Meta_mkLambdaFVars(v_tysxs_397_, v_eAbst_413_, v___x_411_, v___x_414_, v___x_411_, v___x_414_, v___x_415_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
lean_dec_ref(v_tysxs_397_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_a_417_);
lean_dec_ref_known(v___x_416_, 1);
v___x_418_ = l_Lean_mkAppN(v_a_417_, v_args_398_);
v___x_419_ = l_Lean_Meta_Sym_shareCommon(v___x_418_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_428_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_428_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_428_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_428_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v_args_398_);
lean_ctor_set(v___x_424_, 1, v_a_420_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_424_);
v___x_426_ = v___x_422_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec_ref(v_args_398_);
v_a_429_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_419_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_419_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_dec_ref(v_args_398_);
v_a_437_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_416_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_416_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
else
{
lean_object* v___x_445_; lean_object* v_snd_446_; 
v___x_445_ = lean_array_fget_borrowed(v_lhss_u03b1s_393_, v_i_394_);
v_snd_446_ = lean_ctor_get(v___x_445_, 1);
if (lean_obj_tag(v_snd_446_) == 1)
{
lean_object* v_fst_447_; lean_object* v_val_448_; lean_object* v___f_449_; lean_object* v___x_450_; 
v_fst_447_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_fst_447_);
v_val_448_ = lean_ctor_get(v_snd_446_, 0);
lean_inc_n(v_val_448_, 2);
lean_inc(v_i_394_);
v___f_449_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed), 21, 9);
lean_closure_set(v___f_449_, 0, v_i_394_);
lean_closure_set(v___f_449_, 1, v_xs_395_);
lean_closure_set(v___f_449_, 2, v_tys_396_);
lean_closure_set(v___f_449_, 3, v_tysxs_397_);
lean_closure_set(v___f_449_, 4, v_args_398_);
lean_closure_set(v___f_449_, 5, v_val_448_);
lean_closure_set(v___f_449_, 6, v_fst_447_);
lean_closure_set(v___f_449_, 7, v_e_392_);
lean_closure_set(v___f_449_, 8, v_lhss_u03b1s_393_);
lean_inc(v_a_408_);
lean_inc_ref(v_a_407_);
lean_inc(v_a_406_);
lean_inc_ref(v_a_405_);
v___x_450_ = lean_infer_type(v_val_448_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_a_451_);
lean_dec_ref_known(v___x_450_, 1);
v___x_452_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__1));
v___x_453_ = lean_name_append_index_after(v___x_452_, v_i_394_);
v___x_454_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v___x_453_, v_a_451_, v___f_449_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
return v___x_454_;
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
lean_dec_ref(v___f_449_);
lean_dec(v_i_394_);
v_a_455_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_450_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_450_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
else
{
lean_object* v_fst_463_; lean_object* v___f_464_; lean_object* v___x_465_; 
v_fst_463_ = lean_ctor_get(v___x_445_, 0);
lean_inc_n(v_fst_463_, 2);
lean_inc(v_i_394_);
v___f_464_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed), 20, 8);
lean_closure_set(v___f_464_, 0, v_i_394_);
lean_closure_set(v___f_464_, 1, v_xs_395_);
lean_closure_set(v___f_464_, 2, v_tys_396_);
lean_closure_set(v___f_464_, 3, v_tysxs_397_);
lean_closure_set(v___f_464_, 4, v_args_398_);
lean_closure_set(v___f_464_, 5, v_fst_463_);
lean_closure_set(v___f_464_, 6, v_e_392_);
lean_closure_set(v___f_464_, 7, v_lhss_u03b1s_393_);
lean_inc(v_a_408_);
lean_inc_ref(v_a_407_);
lean_inc(v_a_406_);
lean_inc_ref(v_a_405_);
v___x_465_ = lean_infer_type(v_fst_463_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_466_);
lean_dec_ref_known(v___x_465_, 1);
v___x_467_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1));
v___x_468_ = lean_name_append_index_after(v___x_467_, v_i_394_);
v___x_469_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v___x_468_, v_a_466_, v___f_464_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
return v___x_469_;
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
lean_dec_ref(v___f_464_);
lean_dec(v_i_394_);
v_a_470_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_465_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_465_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(lean_object* v_i_478_, lean_object* v_xs_479_, lean_object* v_ty_480_, lean_object* v_tys_481_, lean_object* v_tysxs_482_, lean_object* v_args_483_, lean_object* v_val_484_, lean_object* v_fst_485_, lean_object* v_e_486_, lean_object* v_lhss_u03b1s_487_, lean_object* v_x_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_500_ = lean_unsigned_to_nat(1u);
v___x_501_ = lean_nat_add(v_i_478_, v___x_500_);
lean_inc_ref(v_x_488_);
v___x_502_ = lean_array_push(v_xs_479_, v_x_488_);
lean_inc_ref(v_ty_480_);
v___x_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_503_, 0, v_ty_480_);
v___x_504_ = lean_array_push(v_tys_481_, v___x_503_);
v___x_505_ = lean_array_push(v_tysxs_482_, v_ty_480_);
v___x_506_ = lean_array_push(v___x_505_, v_x_488_);
v___x_507_ = lean_array_push(v_args_483_, v_val_484_);
v___x_508_ = lean_array_push(v___x_507_, v_fst_485_);
v___x_509_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_486_, v_lhss_u03b1s_487_, v___x_501_, v___x_502_, v___x_504_, v___x_506_, v___x_508_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0___boxed(lean_object** _args){
lean_object* v_i_510_ = _args[0];
lean_object* v_xs_511_ = _args[1];
lean_object* v_ty_512_ = _args[2];
lean_object* v_tys_513_ = _args[3];
lean_object* v_tysxs_514_ = _args[4];
lean_object* v_args_515_ = _args[5];
lean_object* v_val_516_ = _args[6];
lean_object* v_fst_517_ = _args[7];
lean_object* v_e_518_ = _args[8];
lean_object* v_lhss_u03b1s_519_ = _args[9];
lean_object* v_x_520_ = _args[10];
lean_object* v___y_521_ = _args[11];
lean_object* v___y_522_ = _args[12];
lean_object* v___y_523_ = _args[13];
lean_object* v___y_524_ = _args[14];
lean_object* v___y_525_ = _args[15];
lean_object* v___y_526_ = _args[16];
lean_object* v___y_527_ = _args[17];
lean_object* v___y_528_ = _args[18];
lean_object* v___y_529_ = _args[19];
lean_object* v___y_530_ = _args[20];
lean_object* v___y_531_ = _args[21];
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(v_i_510_, v_xs_511_, v_ty_512_, v_tys_513_, v_tysxs_514_, v_args_515_, v_val_516_, v_fst_517_, v_e_518_, v_lhss_u03b1s_519_, v_x_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec(v___y_521_);
lean_dec(v_i_510_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(lean_object* v_i_533_, lean_object* v_xs_534_, lean_object* v_tys_535_, lean_object* v_tysxs_536_, lean_object* v_args_537_, lean_object* v_val_538_, lean_object* v_fst_539_, lean_object* v_e_540_, lean_object* v_lhss_u03b1s_541_, lean_object* v_ty_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___f_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
lean_inc_ref(v_ty_542_);
lean_inc(v_i_533_);
v___f_554_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0___boxed), 22, 10);
lean_closure_set(v___f_554_, 0, v_i_533_);
lean_closure_set(v___f_554_, 1, v_xs_534_);
lean_closure_set(v___f_554_, 2, v_ty_542_);
lean_closure_set(v___f_554_, 3, v_tys_535_);
lean_closure_set(v___f_554_, 4, v_tysxs_536_);
lean_closure_set(v___f_554_, 5, v_args_537_);
lean_closure_set(v___f_554_, 6, v_val_538_);
lean_closure_set(v___f_554_, 7, v_fst_539_);
lean_closure_set(v___f_554_, 8, v_e_540_);
lean_closure_set(v___f_554_, 9, v_lhss_u03b1s_541_);
v___x_555_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1));
v___x_556_ = lean_name_append_index_after(v___x_555_, v_i_533_);
v___x_557_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v___x_556_, v_ty_542_, v___f_554_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___boxed(lean_object** _args){
lean_object* v_e_558_ = _args[0];
lean_object* v_lhss_u03b1s_559_ = _args[1];
lean_object* v_i_560_ = _args[2];
lean_object* v_xs_561_ = _args[3];
lean_object* v_tys_562_ = _args[4];
lean_object* v_tysxs_563_ = _args[5];
lean_object* v_args_564_ = _args[6];
lean_object* v_a_565_ = _args[7];
lean_object* v_a_566_ = _args[8];
lean_object* v_a_567_ = _args[9];
lean_object* v_a_568_ = _args[10];
lean_object* v_a_569_ = _args[11];
lean_object* v_a_570_ = _args[12];
lean_object* v_a_571_ = _args[13];
lean_object* v_a_572_ = _args[14];
lean_object* v_a_573_ = _args[15];
lean_object* v_a_574_ = _args[16];
lean_object* v_a_575_ = _args[17];
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_558_, v_lhss_u03b1s_559_, v_i_560_, v_xs_561_, v_tys_562_, v_tysxs_563_, v_args_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec(v_a_565_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0(lean_object* v_00_u03b1_577_, lean_object* v_name_578_, uint8_t v_bi_579_, lean_object* v_type_580_, lean_object* v_k_581_, uint8_t v_kind_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_578_, v_bi_579_, v_type_580_, v_k_581_, v_kind_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_595_ = _args[0];
lean_object* v_name_596_ = _args[1];
lean_object* v_bi_597_ = _args[2];
lean_object* v_type_598_ = _args[3];
lean_object* v_k_599_ = _args[4];
lean_object* v_kind_600_ = _args[5];
lean_object* v___y_601_ = _args[6];
lean_object* v___y_602_ = _args[7];
lean_object* v___y_603_ = _args[8];
lean_object* v___y_604_ = _args[9];
lean_object* v___y_605_ = _args[10];
lean_object* v___y_606_ = _args[11];
lean_object* v___y_607_ = _args[12];
lean_object* v___y_608_ = _args[13];
lean_object* v___y_609_ = _args[14];
lean_object* v___y_610_ = _args[15];
lean_object* v___y_611_ = _args[16];
_start:
{
uint8_t v_bi_boxed_612_; uint8_t v_kind_boxed_613_; lean_object* v_res_614_; 
v_bi_boxed_612_ = lean_unbox(v_bi_597_);
v_kind_boxed_613_ = lean_unbox(v_kind_600_);
v_res_614_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0(v_00_u03b1_595_, v_name_596_, v_bi_boxed_612_, v_type_598_, v_k_599_, v_kind_boxed_613_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec(v___y_601_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0(lean_object* v_00_u03b1_615_, lean_object* v_name_616_, lean_object* v_type_617_, lean_object* v_k_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v_name_616_, v_type_617_, v_k_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___boxed(lean_object* v_00_u03b1_631_, lean_object* v_name_632_, lean_object* v_type_633_, lean_object* v_k_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0(v_00_u03b1_631_, v_name_632_, v_type_633_, v_k_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec(v___y_635_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter___redArg(lean_object* v_x_647_, lean_object* v_h__1_648_){
_start:
{
lean_object* v_fst_649_; lean_object* v_snd_650_; lean_object* v___x_651_; 
v_fst_649_ = lean_ctor_get(v_x_647_, 0);
lean_inc(v_fst_649_);
v_snd_650_ = lean_ctor_get(v_x_647_, 1);
lean_inc(v_snd_650_);
lean_dec_ref(v_x_647_);
v___x_651_ = lean_apply_2(v_h__1_648_, v_fst_649_, v_snd_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter(lean_object* v_motive_652_, lean_object* v_x_653_, lean_object* v_h__1_654_){
_start:
{
lean_object* v_fst_655_; lean_object* v_snd_656_; lean_object* v___x_657_; 
v_fst_655_ = lean_ctor_get(v_x_653_, 0);
lean_inc(v_fst_655_);
v_snd_656_ = lean_ctor_get(v_x_653_, 1);
lean_inc(v_snd_656_);
lean_dec_ref(v_x_653_);
v___x_657_ = lean_apply_2(v_h__1_654_, v_fst_655_, v_snd_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter___redArg(lean_object* v_00_u03b1_x3f_658_, lean_object* v_h__1_659_, lean_object* v_h__2_660_){
_start:
{
if (lean_obj_tag(v_00_u03b1_x3f_658_) == 1)
{
lean_object* v_val_661_; lean_object* v___x_662_; 
lean_dec(v_h__2_660_);
v_val_661_ = lean_ctor_get(v_00_u03b1_x3f_658_, 0);
lean_inc(v_val_661_);
lean_dec_ref_known(v_00_u03b1_x3f_658_, 1);
v___x_662_ = lean_apply_1(v_h__1_659_, v_val_661_);
return v___x_662_;
}
else
{
lean_object* v___x_663_; 
lean_dec(v_h__1_659_);
v___x_663_ = lean_apply_2(v_h__2_660_, v_00_u03b1_x3f_658_, lean_box(0));
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter(lean_object* v_motive_664_, lean_object* v_00_u03b1_x3f_665_, lean_object* v_h__1_666_, lean_object* v_h__2_667_){
_start:
{
if (lean_obj_tag(v_00_u03b1_x3f_665_) == 1)
{
lean_object* v_val_668_; lean_object* v___x_669_; 
lean_dec(v_h__2_667_);
v_val_668_ = lean_ctor_get(v_00_u03b1_x3f_665_, 0);
lean_inc(v_val_668_);
lean_dec_ref_known(v_00_u03b1_x3f_665_, 1);
v___x_669_ = lean_apply_1(v_h__1_666_, v_val_668_);
return v___x_669_;
}
else
{
lean_object* v___x_670_; 
lean_dec(v_h__1_666_);
v___x_670_ = lean_apply_2(v_h__2_667_, v_00_u03b1_x3f_665_, lean_box(0));
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(lean_object* v_matchCond_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = l_Lean_Expr_cleanupAnnotations(v_matchCond_680_);
v___x_697_ = l_Lean_Expr_isApp(v___x_696_);
if (v___x_697_ == 0)
{
lean_dec_ref(v___x_696_);
goto v___jp_692_;
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_698_ = l_Lean_Expr_appFnCleanup___redArg(v___x_696_);
v___x_699_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_700_ = l_Lean_Expr_isConstOf(v___x_698_, v___x_699_);
lean_dec_ref(v___x_698_);
if (v___x_700_ == 0)
{
lean_dec_ref(v___x_696_);
goto v___jp_692_;
}
else
{
lean_object* v_arg_701_; lean_object* v_lhss_u03b1s_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
lean_dec_ref(v_matchCond_680_);
v_arg_701_ = lean_ctor_get(v___x_696_, 1);
lean_inc_ref_n(v_arg_701_, 2);
lean_dec_ref(v___x_696_);
v_lhss_u03b1s_702_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss(v_arg_701_);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0));
v___x_705_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_arg_701_, v_lhss_u03b1s_702_, v___x_703_, v___x_704_, v___x_704_, v___x_704_, v___x_704_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
return v___x_705_;
}
}
v___jp_692_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_693_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0));
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v_matchCond_680_);
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___boxed(lean_object* v_matchCond_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(v_matchCond_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec(v_a_707_);
return v_res_718_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0(void){
_start:
{
lean_object* v___x_722_; lean_object* v_dummy_723_; 
v___x_722_ = lean_box(0);
v_dummy_723_ = l_Lean_Expr_sort___override(v___x_722_);
return v_dummy_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(lean_object* v_matchCond_x3f_724_, lean_object* v_lhs_725_, lean_object* v_rhs_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
uint8_t v___x_738_; 
v___x_738_ = l_Lean_Expr_hasLooseBVars(v_lhs_725_);
if (v___x_738_ == 0)
{
uint8_t v___x_739_; lean_object* v___x_740_; 
v___x_739_ = 1;
lean_inc_ref(v_lhs_725_);
v___x_740_ = l_Lean_Meta_Grind_getRootENode___redArg(v_lhs_725_, v_a_727_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_902_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_902_ == 0)
{
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_902_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_902_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
uint8_t v_ctor_745_; 
v_ctor_745_ = lean_ctor_get_uint8(v_a_741_, sizeof(void*)*12 + 2);
if (v_ctor_745_ == 0)
{
uint8_t v_interpreted_746_; 
v_interpreted_746_ = lean_ctor_get_uint8(v_a_741_, sizeof(void*)*12 + 1);
if (v_interpreted_746_ == 0)
{
lean_dec(v_a_741_);
if (lean_obj_tag(v_matchCond_x3f_724_) == 1)
{
lean_object* v_val_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v_val_747_ = lean_ctor_get(v_matchCond_x3f_724_, 0);
lean_inc(v_val_747_);
lean_dec_ref_known(v_matchCond_x3f_724_, 1);
v___x_748_ = l_Lean_Expr_getAppFn(v_rhs_726_);
lean_dec_ref(v_rhs_726_);
v___x_749_ = l_Lean_Expr_isBVar(v___x_748_);
lean_dec_ref(v___x_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; 
lean_del_object(v___x_743_);
v___x_750_ = l_Lean_Meta_Grind_registerParent___redArg(v_val_747_, v_lhs_725_, v_a_727_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_758_; 
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; 
v_unused_759_ = lean_ctor_get(v___x_750_, 0);
lean_dec(v_unused_759_);
v___x_752_ = v___x_750_;
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
else
{
lean_dec(v___x_750_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_754_ = lean_box(v_interpreted_746_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_754_);
v___x_756_ = v___x_752_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
v_a_760_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_750_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_750_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
else
{
lean_object* v___x_768_; lean_object* v___x_770_; 
lean_dec(v_val_747_);
lean_dec_ref(v_lhs_725_);
v___x_768_ = lean_box(v_interpreted_746_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_768_);
v___x_770_ = v___x_743_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
else
{
lean_object* v___x_772_; lean_object* v___x_774_; 
lean_dec_ref(v_rhs_726_);
lean_dec_ref(v_lhs_725_);
lean_dec(v_matchCond_x3f_724_);
v___x_772_ = lean_box(v_interpreted_746_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_772_);
v___x_774_ = v___x_743_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
else
{
lean_object* v_self_776_; uint8_t v___x_777_; 
lean_dec_ref(v_lhs_725_);
lean_dec(v_matchCond_x3f_724_);
v_self_776_ = lean_ctor_get(v_a_741_, 0);
lean_inc_ref(v_self_776_);
lean_dec(v_a_741_);
v___x_777_ = l_Lean_Expr_hasLooseBVars(v_rhs_726_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; 
lean_del_object(v___x_743_);
lean_inc_ref(v_rhs_726_);
v___x_778_ = l_Lean_Meta_isLitValue(v_rhs_726_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; uint8_t v___x_780_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v___x_780_ = lean_unbox(v_a_779_);
if (v___x_780_ == 0)
{
lean_dec_ref(v_self_776_);
lean_dec_ref(v_rhs_726_);
return v___x_778_;
}
else
{
lean_object* v___x_781_; 
lean_inc(v_a_779_);
lean_dec_ref_known(v___x_778_, 1);
v___x_781_ = l_Lean_Meta_normLitValue(v_self_776_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_783_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_781_, 1);
v___x_783_ = l_Lean_Meta_normLitValue(v_rhs_726_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_796_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_796_ == 0)
{
v___x_786_ = v___x_783_;
v_isShared_787_ = v_isSharedCheck_796_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_783_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_796_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
uint8_t v___x_788_; 
v___x_788_ = lean_expr_eqv(v_a_782_, v_a_784_);
lean_dec(v_a_784_);
lean_dec(v_a_782_);
if (v___x_788_ == 0)
{
lean_object* v___x_790_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v_a_779_);
v___x_790_ = v___x_786_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_779_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
else
{
lean_object* v___x_792_; lean_object* v___x_794_; 
lean_dec(v_a_779_);
v___x_792_ = lean_box(v___x_777_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_792_);
v___x_794_ = v___x_786_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec(v_a_782_);
lean_dec(v_a_779_);
v_a_797_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_783_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_783_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec(v_a_779_);
lean_dec_ref(v_rhs_726_);
v_a_805_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_781_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_781_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
else
{
lean_dec_ref(v_self_776_);
lean_dec_ref(v_rhs_726_);
return v___x_778_;
}
}
else
{
lean_object* v___x_813_; lean_object* v___x_815_; 
lean_dec_ref(v_self_776_);
lean_dec_ref(v_rhs_726_);
v___x_813_ = lean_box(v_ctor_745_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_813_);
v___x_815_ = v___x_743_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
lean_object* v_self_817_; lean_object* v___x_818_; 
lean_del_object(v___x_743_);
lean_dec_ref(v_lhs_725_);
v_self_817_ = lean_ctor_get(v_a_741_, 0);
lean_inc_ref_n(v_self_817_, 2);
lean_dec(v_a_741_);
v___x_818_ = l_Lean_Meta_isConstructorApp_x3f(v_self_817_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_893_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_893_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_893_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_893_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
if (lean_obj_tag(v_a_819_) == 1)
{
lean_object* v_val_823_; lean_object* v___x_824_; 
lean_del_object(v___x_821_);
v_val_823_ = lean_ctor_get(v_a_819_, 0);
lean_inc(v_val_823_);
lean_dec_ref_known(v_a_819_, 1);
lean_inc_ref(v_rhs_726_);
v___x_824_ = l_Lean_Meta_isConstructorApp_x3f(v_rhs_726_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_880_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_880_ == 0)
{
v___x_827_ = v___x_824_;
v_isShared_828_ = v_isSharedCheck_880_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_824_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_880_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
if (lean_obj_tag(v_a_825_) == 1)
{
lean_object* v_toConstantVal_829_; lean_object* v_val_830_; lean_object* v_toConstantVal_831_; lean_object* v_numParams_832_; lean_object* v_numFields_833_; lean_object* v_name_834_; lean_object* v_name_835_; uint8_t v___x_836_; 
v_toConstantVal_829_ = lean_ctor_get(v_val_823_, 0);
lean_inc_ref(v_toConstantVal_829_);
v_val_830_ = lean_ctor_get(v_a_825_, 0);
lean_inc(v_val_830_);
lean_dec_ref_known(v_a_825_, 1);
v_toConstantVal_831_ = lean_ctor_get(v_val_830_, 0);
lean_inc_ref(v_toConstantVal_831_);
lean_dec(v_val_830_);
v_numParams_832_ = lean_ctor_get(v_val_823_, 3);
lean_inc(v_numParams_832_);
v_numFields_833_ = lean_ctor_get(v_val_823_, 4);
lean_inc(v_numFields_833_);
lean_dec(v_val_823_);
v_name_834_ = lean_ctor_get(v_toConstantVal_829_, 0);
lean_inc(v_name_834_);
lean_dec_ref(v_toConstantVal_829_);
v_name_835_ = lean_ctor_get(v_toConstantVal_831_, 0);
lean_inc(v_name_835_);
lean_dec_ref(v_toConstantVal_831_);
v___x_836_ = lean_name_eq(v_name_834_, v_name_835_);
lean_dec(v_name_835_);
lean_dec(v_name_834_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_839_; 
lean_dec(v_numFields_833_);
lean_dec(v_numParams_832_);
lean_dec_ref(v_self_817_);
lean_dec_ref(v_rhs_726_);
lean_dec(v_matchCond_x3f_724_);
v___x_837_ = lean_box(v___x_739_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_837_);
v___x_839_ = v___x_827_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
else
{
lean_object* v_nargs_841_; lean_object* v_nargs_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v_dummy_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
lean_del_object(v___x_827_);
v_nargs_841_ = l_Lean_Expr_getAppNumArgs(v_self_817_);
v_nargs_842_ = l_Lean_Expr_getAppNumArgs(v_rhs_726_);
v___x_843_ = lean_nat_add(v_numParams_832_, v_numFields_833_);
lean_dec(v_numFields_833_);
v___x_844_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0));
v_dummy_845_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0);
lean_inc(v_nargs_841_);
v___x_846_ = lean_mk_array(v_nargs_841_, v_dummy_845_);
v___x_847_ = lean_unsigned_to_nat(1u);
v___x_848_ = lean_nat_sub(v_nargs_841_, v___x_847_);
lean_dec(v_nargs_841_);
v___x_849_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_817_, v___x_846_, v___x_848_);
lean_inc(v_nargs_842_);
v___x_850_ = lean_mk_array(v_nargs_842_, v_dummy_845_);
v___x_851_ = lean_nat_sub(v_nargs_842_, v___x_847_);
lean_dec(v_nargs_842_);
v___x_852_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_rhs_726_, v___x_850_, v___x_851_);
v___x_853_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v___x_843_, v___x_849_, v___x_852_, v_matchCond_x3f_724_, v_numParams_832_, v___x_844_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec_ref(v___x_852_);
lean_dec_ref(v___x_849_);
lean_dec(v___x_843_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_867_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_867_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_867_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_867_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v_fst_858_; 
v_fst_858_ = lean_ctor_get(v_a_854_, 0);
lean_inc(v_fst_858_);
lean_dec(v_a_854_);
if (lean_obj_tag(v_fst_858_) == 0)
{
lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_859_ = lean_box(v___x_738_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_859_);
v___x_861_ = v___x_856_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
else
{
lean_object* v_val_863_; lean_object* v___x_865_; 
v_val_863_ = lean_ctor_get(v_fst_858_, 0);
lean_inc(v_val_863_);
lean_dec_ref_known(v_fst_858_, 1);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v_val_863_);
v___x_865_ = v___x_856_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_val_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
v_a_868_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_853_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_853_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
}
else
{
lean_object* v___x_876_; lean_object* v___x_878_; 
lean_dec(v_a_825_);
lean_dec(v_val_823_);
lean_dec_ref(v_self_817_);
lean_dec_ref(v_rhs_726_);
lean_dec(v_matchCond_x3f_724_);
v___x_876_ = lean_box(v___x_738_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_876_);
v___x_878_ = v___x_827_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec(v_val_823_);
lean_dec_ref(v_self_817_);
lean_dec_ref(v_rhs_726_);
lean_dec(v_matchCond_x3f_724_);
v_a_881_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_824_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_824_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
else
{
lean_object* v___x_889_; lean_object* v___x_891_; 
lean_dec(v_a_819_);
lean_dec_ref(v_self_817_);
lean_dec_ref(v_rhs_726_);
lean_dec(v_matchCond_x3f_724_);
v___x_889_ = lean_box(v___x_738_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_889_);
v___x_891_ = v___x_821_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec_ref(v_self_817_);
lean_dec_ref(v_rhs_726_);
lean_dec(v_matchCond_x3f_724_);
v_a_894_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_818_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_818_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec_ref(v_rhs_726_);
lean_dec_ref(v_lhs_725_);
lean_dec(v_matchCond_x3f_724_);
v_a_903_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_740_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_740_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
else
{
uint8_t v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
lean_dec_ref(v_rhs_726_);
lean_dec_ref(v_lhs_725_);
lean_dec(v_matchCond_x3f_724_);
v___x_911_ = 0;
v___x_912_ = lean_box(v___x_911_);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
return v___x_913_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(lean_object* v_upperBound_914_, lean_object* v___x_915_, lean_object* v___x_916_, lean_object* v_matchCond_x3f_917_, lean_object* v_a_918_, lean_object* v_b_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
uint8_t v___x_931_; 
v___x_931_ = lean_nat_dec_lt(v_a_918_, v_upperBound_914_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; 
lean_dec(v_a_918_);
lean_dec(v_matchCond_x3f_917_);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v_b_919_);
return v___x_932_;
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec_ref(v_b_919_);
v___x_933_ = l_Lean_instInhabitedExpr;
v___x_934_ = lean_box(0);
v___x_935_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0));
v___x_936_ = lean_array_get_borrowed(v___x_933_, v___x_915_, v_a_918_);
v___x_937_ = lean_array_get_borrowed(v___x_933_, v___x_916_, v_a_918_);
lean_inc(v___x_937_);
lean_inc(v___x_936_);
lean_inc(v_matchCond_x3f_917_);
v___x_938_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v_matchCond_x3f_917_, v___x_936_, v___x_937_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_953_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_953_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_953_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_953_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
uint8_t v___x_943_; 
v___x_943_ = lean_unbox(v_a_939_);
lean_dec(v_a_939_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; lean_object* v___x_945_; 
lean_del_object(v___x_941_);
v___x_944_ = lean_unsigned_to_nat(1u);
v___x_945_ = lean_nat_add(v_a_918_, v___x_944_);
lean_dec(v_a_918_);
v_a_918_ = v___x_945_;
v_b_919_ = v___x_935_;
goto _start;
}
else
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
lean_dec(v_a_918_);
lean_dec(v_matchCond_x3f_917_);
v___x_947_ = lean_box(v___x_931_);
v___x_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v___x_934_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_949_);
v___x_951_ = v___x_941_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec(v_a_918_);
lean_dec(v_matchCond_x3f_917_);
v_a_954_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_938_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_938_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_962_ = _args[0];
lean_object* v___x_963_ = _args[1];
lean_object* v___x_964_ = _args[2];
lean_object* v_matchCond_x3f_965_ = _args[3];
lean_object* v_a_966_ = _args[4];
lean_object* v_b_967_ = _args[5];
lean_object* v___y_968_ = _args[6];
lean_object* v___y_969_ = _args[7];
lean_object* v___y_970_ = _args[8];
lean_object* v___y_971_ = _args[9];
lean_object* v___y_972_ = _args[10];
lean_object* v___y_973_ = _args[11];
lean_object* v___y_974_ = _args[12];
lean_object* v___y_975_ = _args[13];
lean_object* v___y_976_ = _args[14];
lean_object* v___y_977_ = _args[15];
lean_object* v___y_978_ = _args[16];
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v_upperBound_962_, v___x_963_, v___x_964_, v_matchCond_x3f_965_, v_a_966_, v_b_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___x_964_);
lean_dec_ref(v___x_963_);
lean_dec(v_upperBound_962_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___boxed(lean_object* v_matchCond_x3f_980_, lean_object* v_lhs_981_, lean_object* v_rhs_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v_matchCond_x3f_980_, v_lhs_981_, v_rhs_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec(v_a_983_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(lean_object* v_upperBound_995_, lean_object* v___x_996_, lean_object* v___x_997_, lean_object* v_matchCond_x3f_998_, lean_object* v_inst_999_, lean_object* v_R_1000_, lean_object* v_a_1001_, lean_object* v_b_1002_, lean_object* v_c_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v_upperBound_995_, v___x_996_, v___x_997_, v_matchCond_x3f_998_, v_a_1001_, v_b_1002_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_1016_ = _args[0];
lean_object* v___x_1017_ = _args[1];
lean_object* v___x_1018_ = _args[2];
lean_object* v_matchCond_x3f_1019_ = _args[3];
lean_object* v_inst_1020_ = _args[4];
lean_object* v_R_1021_ = _args[5];
lean_object* v_a_1022_ = _args[6];
lean_object* v_b_1023_ = _args[7];
lean_object* v_c_1024_ = _args[8];
lean_object* v___y_1025_ = _args[9];
lean_object* v___y_1026_ = _args[10];
lean_object* v___y_1027_ = _args[11];
lean_object* v___y_1028_ = _args[12];
lean_object* v___y_1029_ = _args[13];
lean_object* v___y_1030_ = _args[14];
lean_object* v___y_1031_ = _args[15];
lean_object* v___y_1032_ = _args[16];
lean_object* v___y_1033_ = _args[17];
lean_object* v___y_1034_ = _args[18];
lean_object* v___y_1035_ = _args[19];
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(v_upperBound_1016_, v___x_1017_, v___x_1018_, v_matchCond_x3f_1019_, v_inst_1020_, v_R_1021_, v_a_1022_, v_b_1023_, v_c_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___x_1018_);
lean_dec_ref(v___x_1017_);
lean_dec(v_upperBound_1016_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(lean_object* v_e_1037_, lean_object* v_matchCond_x3f_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_e_1037_);
if (lean_obj_tag(v___x_1050_) == 1)
{
lean_object* v_val_1051_; lean_object* v_snd_1052_; lean_object* v_fst_1053_; lean_object* v_snd_1054_; lean_object* v___x_1055_; 
v_val_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_val_1051_);
lean_dec_ref_known(v___x_1050_, 1);
v_snd_1052_ = lean_ctor_get(v_val_1051_, 1);
lean_inc(v_snd_1052_);
lean_dec(v_val_1051_);
v_fst_1053_ = lean_ctor_get(v_snd_1052_, 0);
lean_inc(v_fst_1053_);
v_snd_1054_ = lean_ctor_get(v_snd_1052_, 1);
lean_inc(v_snd_1054_);
lean_dec(v_snd_1052_);
v___x_1055_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v_matchCond_x3f_1038_, v_fst_1053_, v_snd_1054_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
return v___x_1055_;
}
else
{
uint8_t v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
lean_dec(v___x_1050_);
lean_dec(v_matchCond_x3f_1038_);
v___x_1056_ = 0;
v___x_1057_ = lean_box(v___x_1056_);
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
return v___x_1058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp___boxed(lean_object* v_e_1059_, lean_object* v_matchCond_x3f_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_e_1059_, v_matchCond_x3f_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
lean_dec(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v_e_1059_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(uint8_t v___x_1073_, lean_object* v_snd_1074_, lean_object* v_____r_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1087_ = lean_box(v___x_1073_);
v___x_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
v___x_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set(v___x_1089_, 1, v_snd_1074_);
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0___boxed(lean_object* v___x_1092_, lean_object* v_snd_1093_, lean_object* v_____r_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
uint8_t v___x_23483__boxed_1106_; lean_object* v_res_1107_; 
v___x_23483__boxed_1106_ = lean_unbox(v___x_1092_);
v_res_1107_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_23483__boxed_1106_, v_snd_1093_, v_____r_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec(v___y_1095_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(lean_object* v_msgData_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; lean_object* v_env_1115_; uint8_t v___x_1116_; lean_object* v_env_1117_; lean_object* v___x_1118_; lean_object* v_toCold_1119_; lean_object* v_mctx_1120_; lean_object* v_lctx_1121_; lean_object* v_options_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1114_ = lean_st_ref_get(v___y_1112_);
v_env_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc_ref(v_env_1115_);
lean_dec(v___x_1114_);
v___x_1116_ = 0;
v_env_1117_ = l_Lean_Environment_setRecordingDeps(v_env_1115_, v___x_1116_);
v___x_1118_ = lean_st_ref_get(v___y_1110_);
v_toCold_1119_ = lean_ctor_get(v___y_1111_, 0);
v_mctx_1120_ = lean_ctor_get(v___x_1118_, 0);
lean_inc_ref(v_mctx_1120_);
lean_dec(v___x_1118_);
v_lctx_1121_ = lean_ctor_get(v___y_1109_, 2);
v_options_1122_ = lean_ctor_get(v_toCold_1119_, 2);
lean_inc_ref(v_options_1122_);
lean_inc_ref(v_lctx_1121_);
v___x_1123_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1123_, 0, v_env_1117_);
lean_ctor_set(v___x_1123_, 1, v_mctx_1120_);
lean_ctor_set(v___x_1123_, 2, v_lctx_1121_);
lean_ctor_set(v___x_1123_, 3, v_options_1122_);
v___x_1124_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
lean_ctor_set(v___x_1124_, 1, v_msgData_1108_);
v___x_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0___boxed(lean_object* v_msgData_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(v_msgData_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
return v_res_1132_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1133_; double v___x_1134_; 
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_float_of_nat(v___x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(lean_object* v_cls_1138_, lean_object* v_msg_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_ref_1145_; lean_object* v___x_1146_; lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1192_; 
v_ref_1145_ = lean_ctor_get(v___y_1142_, 2);
v___x_1146_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(v_msg_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1192_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1192_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v_traceState_1152_; lean_object* v_env_1153_; lean_object* v_nextMacroScope_1154_; lean_object* v_ngen_1155_; lean_object* v_auxDeclNGen_1156_; lean_object* v_cache_1157_; lean_object* v_recordedDeps_1158_; lean_object* v_messages_1159_; lean_object* v_infoState_1160_; lean_object* v_snapshotTasks_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1191_; 
v___x_1151_ = lean_st_ref_take(v___y_1143_);
v_traceState_1152_ = lean_ctor_get(v___x_1151_, 4);
v_env_1153_ = lean_ctor_get(v___x_1151_, 0);
v_nextMacroScope_1154_ = lean_ctor_get(v___x_1151_, 1);
v_ngen_1155_ = lean_ctor_get(v___x_1151_, 2);
v_auxDeclNGen_1156_ = lean_ctor_get(v___x_1151_, 3);
v_cache_1157_ = lean_ctor_get(v___x_1151_, 5);
v_recordedDeps_1158_ = lean_ctor_get(v___x_1151_, 6);
v_messages_1159_ = lean_ctor_get(v___x_1151_, 7);
v_infoState_1160_ = lean_ctor_get(v___x_1151_, 8);
v_snapshotTasks_1161_ = lean_ctor_get(v___x_1151_, 9);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1163_ = v___x_1151_;
v_isShared_1164_ = v_isSharedCheck_1191_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_snapshotTasks_1161_);
lean_inc(v_infoState_1160_);
lean_inc(v_messages_1159_);
lean_inc(v_recordedDeps_1158_);
lean_inc(v_cache_1157_);
lean_inc(v_traceState_1152_);
lean_inc(v_auxDeclNGen_1156_);
lean_inc(v_ngen_1155_);
lean_inc(v_nextMacroScope_1154_);
lean_inc(v_env_1153_);
lean_dec(v___x_1151_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1191_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
uint64_t v_tid_1165_; lean_object* v_traces_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1190_; 
v_tid_1165_ = lean_ctor_get_uint64(v_traceState_1152_, sizeof(void*)*1);
v_traces_1166_ = lean_ctor_get(v_traceState_1152_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_traceState_1152_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1168_ = v_traceState_1152_;
v_isShared_1169_ = v_isSharedCheck_1190_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_traces_1166_);
lean_dec(v_traceState_1152_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1190_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; double v___x_1172_; uint8_t v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1170_ = lean_box(0);
v___x_1171_ = lean_box(0);
v___x_1172_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0);
v___x_1173_ = 0;
v___x_1174_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1));
v___x_1175_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1175_, 0, v_cls_1138_);
lean_ctor_set(v___x_1175_, 1, v___x_1171_);
lean_ctor_set(v___x_1175_, 2, v___x_1174_);
lean_ctor_set_float(v___x_1175_, sizeof(void*)*3, v___x_1172_);
lean_ctor_set_float(v___x_1175_, sizeof(void*)*3 + 8, v___x_1172_);
lean_ctor_set_uint8(v___x_1175_, sizeof(void*)*3 + 16, v___x_1173_);
v___x_1176_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__2));
v___x_1177_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1175_);
lean_ctor_set(v___x_1177_, 1, v_a_1147_);
lean_ctor_set(v___x_1177_, 2, v___x_1176_);
lean_inc(v_ref_1145_);
v___x_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1178_, 0, v_ref_1145_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = l_Lean_PersistentArray_push___redArg(v_traces_1166_, v___x_1178_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v___x_1179_);
v___x_1181_ = v___x_1168_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1179_);
lean_ctor_set_uint64(v_reuseFailAlloc_1189_, sizeof(void*)*1, v_tid_1165_);
v___x_1181_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1183_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 4, v___x_1181_);
v___x_1183_ = v___x_1163_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_env_1153_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_nextMacroScope_1154_);
lean_ctor_set(v_reuseFailAlloc_1188_, 2, v_ngen_1155_);
lean_ctor_set(v_reuseFailAlloc_1188_, 3, v_auxDeclNGen_1156_);
lean_ctor_set(v_reuseFailAlloc_1188_, 4, v___x_1181_);
lean_ctor_set(v_reuseFailAlloc_1188_, 5, v_cache_1157_);
lean_ctor_set(v_reuseFailAlloc_1188_, 6, v_recordedDeps_1158_);
lean_ctor_set(v_reuseFailAlloc_1188_, 7, v_messages_1159_);
lean_ctor_set(v_reuseFailAlloc_1188_, 8, v_infoState_1160_);
lean_ctor_set(v_reuseFailAlloc_1188_, 9, v_snapshotTasks_1161_);
v___x_1183_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1184_ = lean_st_ref_put(v___y_1143_, v___x_1183_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1170_);
v___x_1186_ = v___x_1149_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1170_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___boxed(lean_object* v_cls_1193_, lean_object* v_msg_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1193_, v_msg_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
return v_res_1200_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_1212_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5));
v___x_1213_ = l_Lean_Name_append(v___x_1212_, v___x_1211_);
return v___x_1213_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__7));
v___x_1216_ = l_Lean_stringToMessageData(v___x_1215_);
return v___x_1216_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__9));
v___x_1219_ = l_Lean_stringToMessageData(v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(uint8_t v___x_1220_, lean_object* v_e_1221_, lean_object* v_a_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v___y_1235_; lean_object* v_snd_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1319_; 
v_snd_1255_ = lean_ctor_get(v_a_1222_, 1);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_a_1222_);
if (v_isSharedCheck_1319_ == 0)
{
lean_object* v_unused_1320_; 
v_unused_1320_ = lean_ctor_get(v_a_1222_, 0);
lean_dec(v_unused_1320_);
v___x_1257_ = v_a_1222_;
v_isShared_1258_ = v_isSharedCheck_1319_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_snd_1255_);
lean_dec(v_a_1222_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1319_;
goto v_resetjp_1256_;
}
v___jp_1234_:
{
if (lean_obj_tag(v___y_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1246_; 
v_a_1236_ = lean_ctor_get(v___y_1235_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___y_1235_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1238_ = v___y_1235_;
v_isShared_1239_ = v_isSharedCheck_1246_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___y_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1246_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
if (lean_obj_tag(v_a_1236_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1242_; 
lean_dec_ref(v_e_1221_);
v_a_1240_ = lean_ctor_get(v_a_1236_, 0);
lean_inc(v_a_1240_);
lean_dec_ref_known(v_a_1236_, 1);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v_a_1240_);
v___x_1242_ = v___x_1238_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
else
{
lean_object* v_a_1244_; 
lean_del_object(v___x_1238_);
v_a_1244_ = lean_ctor_get(v_a_1236_, 0);
lean_inc(v_a_1244_);
lean_dec_ref_known(v_a_1236_, 1);
v_a_1222_ = v_a_1244_;
goto _start;
}
}
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
lean_dec_ref(v_e_1221_);
v_a_1247_ = lean_ctor_get(v___y_1235_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___y_1235_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___y_1235_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___y_1235_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; 
v___x_1259_ = lean_box(0);
if (lean_obj_tag(v_snd_1255_) == 7)
{
lean_object* v_binderType_1260_; lean_object* v_body_1261_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v_binderType_1260_ = lean_ctor_get(v_snd_1255_, 1);
v_body_1261_ = lean_ctor_get(v_snd_1255_, 2);
lean_inc_ref(v_e_1221_);
v___x_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1265_, 0, v_e_1221_);
v___x_1266_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_binderType_1260_, v___x_1265_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; uint8_t v___x_1268_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1266_, 1);
v___x_1268_ = lean_unbox(v_a_1267_);
lean_dec(v_a_1267_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1270_; 
lean_inc_ref(v_body_1261_);
lean_dec_ref_known(v_snd_1255_, 3);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v_body_1261_);
lean_ctor_set(v___x_1257_, 0, v___x_1259_);
v___x_1270_ = v___x_1257_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_body_1261_);
v___x_1270_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
v_a_1222_ = v___x_1270_;
goto _start;
}
}
else
{
lean_object* v_toCold_1273_; lean_object* v_options_1274_; uint8_t v_hasTrace_1275_; 
lean_del_object(v___x_1257_);
v_toCold_1273_ = lean_ctor_get(v___y_1231_, 0);
v_options_1274_ = lean_ctor_get(v_toCold_1273_, 2);
v_hasTrace_1275_ = lean_ctor_get_uint8(v_options_1274_, sizeof(void*)*1);
if (v_hasTrace_1275_ == 0)
{
goto v___jp_1262_;
}
else
{
lean_object* v_inheritedTraceOptions_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v_inheritedTraceOptions_1276_ = lean_ctor_get(v_toCold_1273_, 11);
v___x_1277_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_1278_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_1279_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1276_, v_options_1274_, v___x_1278_);
if (v___x_1279_ == 0)
{
goto v___jp_1262_;
}
else
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Lean_Meta_Grind_updateLastTag(v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_dec_ref_known(v___x_1280_, 1);
v___x_1281_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8);
lean_inc_ref(v_snd_1255_);
v___x_1282_ = l_Lean_indentExpr(v_snd_1255_);
v___x_1283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1281_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10);
v___x_1285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
lean_inc_ref(v_binderType_1260_);
v___x_1286_ = l_Lean_indentExpr(v_binderType_1260_);
v___x_1287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_1277_, v___x_1287_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v___x_1290_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
lean_dec_ref_known(v___x_1288_, 1);
v___x_1290_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_1220_, v_snd_1255_, v_a_1289_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
v___y_1235_ = v___x_1290_;
goto v___jp_1234_;
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec_ref_known(v_snd_1255_, 3);
lean_dec_ref(v_e_1221_);
v_a_1291_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1288_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1288_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_dec_ref_known(v_snd_1255_, 3);
lean_dec_ref(v_e_1221_);
v_a_1299_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1280_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1280_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec_ref_known(v_snd_1255_, 3);
lean_del_object(v___x_1257_);
lean_dec_ref(v_e_1221_);
v_a_1307_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1266_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1266_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
v___jp_1262_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_box(0);
v___x_1264_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_1220_, v_snd_1255_, v___x_1263_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
v___y_1235_ = v___x_1264_;
goto v___jp_1234_;
}
}
else
{
lean_object* v___x_1316_; 
lean_dec_ref(v_e_1221_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1259_);
v___x_1316_ = v___x_1257_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_snd_1255_);
v___x_1316_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; 
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
return v___x_1317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___boxed(lean_object* v___x_1321_, lean_object* v_e_1322_, lean_object* v_a_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
uint8_t v___x_23698__boxed_1335_; lean_object* v_res_1336_; 
v___x_23698__boxed_1335_ = lean_unbox(v___x_1321_);
v_res_1336_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_23698__boxed_1335_, v_e_1322_, v_a_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec(v___y_1324_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(lean_object* v_e_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v___x_1353_; 
lean_inc_ref(v_e_1337_);
v___x_1353_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1337_, v_a_1345_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1354_);
lean_dec_ref_known(v___x_1353_, 1);
v___x_1355_ = l_Lean_Expr_cleanupAnnotations(v_a_1354_);
lean_dec(v_a_1354_);
v___x_1356_ = l_Lean_Expr_isApp(v___x_1355_);
if (v___x_1356_ == 0)
{
lean_dec_ref(v___x_1355_);
lean_dec_ref(v_e_1337_);
goto v___jp_1349_;
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1357_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1355_);
v___x_1358_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_1359_ = l_Lean_Expr_isConstOf(v___x_1357_, v___x_1358_);
lean_dec_ref(v___x_1357_);
if (v___x_1359_ == 0)
{
lean_dec_ref(v___x_1355_);
lean_dec_ref(v_e_1337_);
goto v___jp_1349_;
}
else
{
lean_object* v_arg_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v_arg_1360_ = lean_ctor_get(v___x_1355_, 1);
lean_inc_ref(v_arg_1360_);
lean_dec_ref(v___x_1355_);
v___x_1361_ = lean_box(0);
v___x_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
lean_ctor_set(v___x_1362_, 1, v_arg_1360_);
v___x_1363_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_1359_, v_e_1337_, v___x_1362_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1378_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1378_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1378_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v_fst_1368_; 
v_fst_1368_ = lean_ctor_get(v_a_1364_, 0);
lean_inc(v_fst_1368_);
lean_dec(v_a_1364_);
if (lean_obj_tag(v_fst_1368_) == 0)
{
uint8_t v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1369_ = 0;
v___x_1370_ = lean_box(v___x_1369_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1370_);
v___x_1372_ = v___x_1366_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
else
{
lean_object* v_val_1374_; lean_object* v___x_1376_; 
v_val_1374_ = lean_ctor_get(v_fst_1368_, 0);
lean_inc(v_val_1374_);
lean_dec_ref_known(v_fst_1368_, 1);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v_val_1374_);
v___x_1376_ = v___x_1366_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_val_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
v_a_1379_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1363_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1363_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec_ref(v_e_1337_);
v_a_1387_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1353_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1353_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
v___jp_1349_:
{
uint8_t v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = 0;
v___x_1351_ = lean_box(v___x_1350_);
v___x_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
return v___x_1352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied___boxed(lean_object* v_e_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
lean_dec(v_a_1397_);
lean_dec(v_a_1396_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(lean_object* v_cls_1408_, lean_object* v_msg_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1408_, v_msg_1409_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___boxed(lean_object* v_cls_1422_, lean_object* v_msg_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(v_cls_1422_, v_msg_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec(v___y_1424_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(uint8_t v___x_1436_, lean_object* v_e_1437_, lean_object* v_inst_1438_, lean_object* v_a_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_1436_, v_e_1437_, v_a_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___boxed(lean_object* v___x_1452_, lean_object* v_e_1453_, lean_object* v_inst_1454_, lean_object* v_a_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
uint8_t v___x_24059__boxed_1467_; lean_object* v_res_1468_; 
v___x_24059__boxed_1467_ = lean_unbox(v___x_1452_);
v_res_1468_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(v___x_24059__boxed_1467_, v_e_1453_, v_inst_1454_, v_a_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec(v___y_1456_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(lean_object* v_k_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v_b_1476_, lean_object* v_c_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v___x_1483_; 
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1480_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
lean_inc(v___y_1475_);
lean_inc_ref(v___y_1474_);
lean_inc(v___y_1473_);
lean_inc_ref(v___y_1472_);
lean_inc(v___y_1471_);
lean_inc(v___y_1470_);
v___x_1483_ = lean_apply_13(v_k_1469_, v_b_1476_, v_c_1477_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, lean_box(0));
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed(lean_object* v_k_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v_b_1491_, lean_object* v_c_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(v_k_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v_b_1491_, v_c_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec(v___y_1485_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(lean_object* v_type_1499_, lean_object* v_k_1500_, uint8_t v_cleanupAnnotations_1501_, uint8_t v_whnfType_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v___f_1514_; lean_object* v___x_1515_; 
lean_inc(v___y_1508_);
lean_inc_ref(v___y_1507_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc(v___y_1503_);
v___f_1514_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1514_, 0, v_k_1500_);
lean_closure_set(v___f_1514_, 1, v___y_1503_);
lean_closure_set(v___f_1514_, 2, v___y_1504_);
lean_closure_set(v___f_1514_, 3, v___y_1505_);
lean_closure_set(v___f_1514_, 4, v___y_1506_);
lean_closure_set(v___f_1514_, 5, v___y_1507_);
lean_closure_set(v___f_1514_, 6, v___y_1508_);
v___x_1515_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1499_, v___f_1514_, v_cleanupAnnotations_1501_, v_whnfType_1502_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1515_) == 0)
{
return v___x_1515_;
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1515_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1515_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___boxed(lean_object* v_type_1524_, lean_object* v_k_1525_, lean_object* v_cleanupAnnotations_1526_, lean_object* v_whnfType_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1539_; uint8_t v_whnfType_boxed_1540_; lean_object* v_res_1541_; 
v_cleanupAnnotations_boxed_1539_ = lean_unbox(v_cleanupAnnotations_1526_);
v_whnfType_boxed_1540_ = lean_unbox(v_whnfType_1527_);
v_res_1541_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_1524_, v_k_1525_, v_cleanupAnnotations_boxed_1539_, v_whnfType_boxed_1540_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec(v___y_1528_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(lean_object* v_00_u03b1_1542_, lean_object* v_type_1543_, lean_object* v_k_1544_, uint8_t v_cleanupAnnotations_1545_, uint8_t v_whnfType_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_1543_, v_k_1544_, v_cleanupAnnotations_1545_, v_whnfType_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___boxed(lean_object* v_00_u03b1_1559_, lean_object* v_type_1560_, lean_object* v_k_1561_, lean_object* v_cleanupAnnotations_1562_, lean_object* v_whnfType_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1575_; uint8_t v_whnfType_boxed_1576_; lean_object* v_res_1577_; 
v_cleanupAnnotations_boxed_1575_ = lean_unbox(v_cleanupAnnotations_1562_);
v_whnfType_boxed_1576_ = lean_unbox(v_whnfType_1563_);
v_res_1577_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(v_00_u03b1_1559_, v_type_1560_, v_k_1561_, v_cleanupAnnotations_boxed_1575_, v_whnfType_boxed_1576_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec(v___y_1564_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed(lean_object** _args){
lean_object* v_e_1581_ = _args[0];
lean_object* v_name_1582_ = _args[1];
lean_object* v_name_1583_ = _args[2];
lean_object* v_a_1584_ = _args[3];
lean_object* v_a_1585_ = _args[4];
lean_object* v_xs_1586_ = _args[5];
lean_object* v_x_1587_ = _args[6];
lean_object* v___y_1588_ = _args[7];
lean_object* v___y_1589_ = _args[8];
lean_object* v___y_1590_ = _args[9];
lean_object* v___y_1591_ = _args[10];
lean_object* v___y_1592_ = _args[11];
lean_object* v___y_1593_ = _args[12];
lean_object* v___y_1594_ = _args[13];
lean_object* v___y_1595_ = _args[14];
lean_object* v___y_1596_ = _args[15];
lean_object* v___y_1597_ = _args[16];
lean_object* v___y_1598_ = _args[17];
_start:
{
uint8_t v_a_82904__boxed_1599_; lean_object* v_res_1600_; 
v_a_82904__boxed_1599_ = lean_unbox(v_a_1584_);
v_res_1600_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(v_e_1581_, v_name_1582_, v_name_1583_, v_a_82904__boxed_1599_, v_a_1585_, v_xs_1586_, v_x_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v_x_1587_);
lean_dec_ref(v_xs_1586_);
lean_dec(v_name_1583_);
lean_dec(v_name_1582_);
return v_res_1600_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1(void){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__0));
v___x_1603_ = l_Lean_stringToMessageData(v___x_1602_);
return v___x_1603_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3(void){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__2));
v___x_1606_ = l_Lean_stringToMessageData(v___x_1605_);
return v___x_1606_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5(void){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__4));
v___x_1609_ = l_Lean_stringToMessageData(v___x_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(lean_object* v_e_1610_, lean_object* v_h_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
uint8_t v___y_1627_; lean_object* v___y_1628_; uint8_t v___y_1629_; lean_object* v___y_1630_; uint8_t v___y_1631_; lean_object* v_h_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; uint8_t v___y_1847_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v_toCold_2021_; lean_object* v_options_2022_; uint8_t v_hasTrace_2023_; 
v_toCold_2021_ = lean_ctor_get(v_a_1620_, 0);
v_options_2022_ = lean_ctor_get(v_toCold_2021_, 2);
v_hasTrace_2023_ = lean_ctor_get_uint8(v_options_2022_, sizeof(void*)*1);
if (v_hasTrace_2023_ == 0)
{
v___y_1924_ = v_a_1612_;
v___y_1925_ = v_a_1613_;
v___y_1926_ = v_a_1614_;
v___y_1927_ = v_a_1615_;
v___y_1928_ = v_a_1616_;
v___y_1929_ = v_a_1617_;
v___y_1930_ = v_a_1618_;
v___y_1931_ = v_a_1619_;
v___y_1932_ = v_a_1620_;
v___y_1933_ = v_a_1621_;
goto v___jp_1923_;
}
else
{
lean_object* v_inheritedTraceOptions_2024_; lean_object* v_cls_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v_inheritedTraceOptions_2024_ = lean_ctor_get(v_toCold_2021_, 11);
v_cls_2025_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_2026_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_2027_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2024_, v_options_2022_, v___x_2026_);
if (v___x_2027_ == 0)
{
v___y_1924_ = v_a_1612_;
v___y_1925_ = v_a_1613_;
v___y_1926_ = v_a_1614_;
v___y_1927_ = v_a_1615_;
v___y_1928_ = v_a_1616_;
v___y_1929_ = v_a_1617_;
v___y_1930_ = v_a_1618_;
v___y_1931_ = v_a_1619_;
v___y_1932_ = v_a_1620_;
v___y_1933_ = v_a_1621_;
goto v___jp_1923_;
}
else
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Lean_Meta_Grind_updateLastTag(v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v___x_2029_; 
lean_dec_ref_known(v___x_2028_, 1);
lean_inc(v_a_1621_);
lean_inc_ref(v_a_1620_);
lean_inc(v_a_1619_);
lean_inc_ref(v_a_1618_);
lean_inc_ref(v_h_1611_);
v___x_2029_ = lean_infer_type(v_h_1611_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2029_, 1);
v___x_2031_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5);
v___x_2032_ = l_Lean_MessageData_ofExpr(v_a_2030_);
v___x_2033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2031_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v___x_2034_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_2025_, v___x_2033_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_dec_ref_known(v___x_2034_, 1);
v___y_1924_ = v_a_1612_;
v___y_1925_ = v_a_1613_;
v___y_1926_ = v_a_1614_;
v___y_1927_ = v_a_1615_;
v___y_1928_ = v_a_1616_;
v___y_1929_ = v_a_1617_;
v___y_1930_ = v_a_1618_;
v___y_1931_ = v_a_1619_;
v___y_1932_ = v_a_1620_;
v___y_1933_ = v_a_1621_;
goto v___jp_1923_;
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2034_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2034_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v_a_2043_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2029_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2029_);
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
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v_a_2051_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2028_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2028_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
v___jp_1623_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = lean_box(0);
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
return v___x_1625_;
}
v___jp_1626_:
{
if (v___y_1631_ == 0)
{
lean_dec_ref(v_e_1610_);
if (v___y_1629_ == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_dec_ref(v_h_1632_);
lean_dec_ref(v___y_1630_);
lean_dec_ref(v___y_1628_);
v___x_1643_ = lean_box(0);
v___x_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
return v___x_1644_;
}
else
{
lean_object* v___x_1645_; 
lean_inc_ref(v___y_1628_);
v___x_1645_ = l_Lean_Meta_isLitValue(v___y_1628_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1714_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1648_ = v___x_1645_;
v_isShared_1649_ = v_isSharedCheck_1714_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1645_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1714_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
uint8_t v___x_1650_; 
v___x_1650_ = lean_unbox(v_a_1646_);
lean_dec(v_a_1646_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
lean_dec_ref(v_h_1632_);
lean_dec_ref(v___y_1630_);
lean_dec_ref(v___y_1628_);
v___x_1651_ = lean_box(0);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v___x_1651_);
v___x_1653_ = v___x_1648_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
else
{
lean_object* v___x_1655_; 
lean_del_object(v___x_1648_);
lean_inc_ref(v___y_1630_);
v___x_1655_ = l_Lean_Meta_normLitValue(v___y_1630_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1657_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref_known(v___x_1655_, 1);
lean_inc_ref(v___y_1628_);
v___x_1657_ = l_Lean_Meta_normLitValue(v___y_1628_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1697_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1697_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1697_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
uint8_t v___x_1662_; 
v___x_1662_ = lean_expr_eqv(v_a_1656_, v_a_1658_);
lean_dec(v_a_1658_);
lean_dec(v_a_1656_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; 
lean_del_object(v___x_1660_);
v___x_1663_ = l_Lean_Meta_mkEq(v___y_1630_, v___y_1628_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1663_, 1);
v___x_1665_ = l_Lean_mkNot(v_a_1664_);
v___x_1666_ = l_Lean_Meta_mkDecideProof(v___x_1665_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1676_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1676_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1676_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1671_ = l_Lean_Expr_app___override(v_a_1667_, v_h_1632_);
v___x_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v___x_1672_);
v___x_1674_ = v___x_1669_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
lean_dec_ref(v_h_1632_);
v_a_1677_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1666_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1666_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec_ref(v_h_1632_);
v_a_1685_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1663_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1663_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1695_; 
lean_dec_ref(v_h_1632_);
lean_dec_ref(v___y_1630_);
lean_dec_ref(v___y_1628_);
v___x_1693_ = lean_box(0);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1693_);
v___x_1695_ = v___x_1660_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1693_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec(v_a_1656_);
lean_dec_ref(v_h_1632_);
lean_dec_ref(v___y_1630_);
lean_dec_ref(v___y_1628_);
v_a_1698_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1657_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1657_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec_ref(v_h_1632_);
lean_dec_ref(v___y_1630_);
lean_dec_ref(v___y_1628_);
v_a_1706_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1655_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1655_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec_ref(v_h_1632_);
lean_dec_ref(v___y_1630_);
lean_dec_ref(v___y_1628_);
v_a_1715_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1645_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1645_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
else
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_Meta_isConstructorApp_x3f(v___y_1630_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1824_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1726_ = v___x_1723_;
v_isShared_1727_ = v_isSharedCheck_1824_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1723_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1824_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
if (lean_obj_tag(v_a_1724_) == 1)
{
lean_object* v_val_1728_; lean_object* v___x_1729_; 
lean_del_object(v___x_1726_);
v_val_1728_ = lean_ctor_get(v_a_1724_, 0);
lean_inc(v_val_1728_);
lean_dec_ref_known(v_a_1724_, 1);
v___x_1729_ = l_Lean_Meta_isConstructorApp_x3f(v___y_1628_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1811_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1732_ = v___x_1729_;
v_isShared_1733_ = v_isSharedCheck_1811_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1729_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1811_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
if (lean_obj_tag(v_a_1730_) == 1)
{
lean_object* v_val_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1806_; 
lean_del_object(v___x_1732_);
v_val_1734_ = lean_ctor_get(v_a_1730_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_a_1730_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1736_ = v_a_1730_;
v_isShared_1737_ = v_isSharedCheck_1806_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_val_1734_);
lean_dec(v_a_1730_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1806_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_1637_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1740_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___x_1738_, 1);
v___x_1740_ = l_Lean_Meta_mkNoConfusion(v_a_1739_, v_h_1632_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_toConstantVal_1741_; lean_object* v_toConstantVal_1742_; lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1789_; 
v_toConstantVal_1741_ = lean_ctor_get(v_val_1728_, 0);
lean_inc_ref(v_toConstantVal_1741_);
lean_dec(v_val_1728_);
v_toConstantVal_1742_ = lean_ctor_get(v_val_1734_, 0);
lean_inc_ref(v_toConstantVal_1742_);
lean_dec(v_val_1734_);
v_a_1743_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1745_ = v___x_1740_;
v_isShared_1746_ = v_isSharedCheck_1789_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1740_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1789_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v_name_1747_; lean_object* v_name_1748_; uint8_t v___x_1749_; 
v_name_1747_ = lean_ctor_get(v_toConstantVal_1741_, 0);
lean_inc(v_name_1747_);
lean_dec_ref(v_toConstantVal_1741_);
v_name_1748_ = lean_ctor_get(v_toConstantVal_1742_, 0);
lean_inc(v_name_1748_);
lean_dec_ref(v_toConstantVal_1742_);
v___x_1749_ = lean_name_eq(v_name_1747_, v_name_1748_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1751_; 
lean_dec(v_name_1748_);
lean_dec(v_name_1747_);
lean_dec_ref(v_e_1610_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v_a_1743_);
v___x_1751_ = v___x_1736_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1743_);
v___x_1751_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___x_1753_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1751_);
v___x_1753_ = v___x_1745_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1751_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
else
{
lean_object* v___x_1756_; lean_object* v___f_1757_; uint8_t v___x_1758_; lean_object* v___x_1759_; 
lean_del_object(v___x_1745_);
lean_del_object(v___x_1736_);
v___x_1756_ = lean_box(v___y_1627_);
lean_inc(v_a_1743_);
v___f_1757_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed), 18, 5);
lean_closure_set(v___f_1757_, 0, v_e_1610_);
lean_closure_set(v___f_1757_, 1, v_name_1747_);
lean_closure_set(v___f_1757_, 2, v_name_1748_);
lean_closure_set(v___f_1757_, 3, v___x_1756_);
lean_closure_set(v___f_1757_, 4, v_a_1743_);
v___x_1758_ = 0;
lean_inc(v___y_1642_);
lean_inc_ref(v___y_1641_);
lean_inc(v___y_1640_);
lean_inc_ref(v___y_1639_);
v___x_1759_ = lean_infer_type(v_a_1743_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1761_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
lean_dec_ref_known(v___x_1759_, 1);
v___x_1761_ = l_Lean_Meta_whnfD(v_a_1760_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1772_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1764_ = v___x_1761_;
v_isShared_1765_ = v_isSharedCheck_1772_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1761_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1772_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
if (lean_obj_tag(v_a_1762_) == 7)
{
lean_object* v_binderType_1766_; lean_object* v___x_1767_; 
lean_del_object(v___x_1764_);
v_binderType_1766_ = lean_ctor_get(v_a_1762_, 1);
lean_inc_ref(v_binderType_1766_);
lean_dec_ref_known(v_a_1762_, 3);
v___x_1767_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_binderType_1766_, v___f_1757_, v___x_1758_, v___x_1758_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
return v___x_1767_;
}
else
{
lean_object* v___x_1768_; lean_object* v___x_1770_; 
lean_dec(v_a_1762_);
lean_dec_ref(v___f_1757_);
v___x_1768_ = lean_box(0);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v___x_1768_);
v___x_1770_ = v___x_1764_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec_ref(v___f_1757_);
v_a_1773_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1761_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1761_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec_ref(v___f_1757_);
v_a_1781_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1759_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1759_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
lean_del_object(v___x_1736_);
lean_dec(v_val_1734_);
lean_dec(v_val_1728_);
lean_dec_ref(v_e_1610_);
v_a_1790_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1740_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1740_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_del_object(v___x_1736_);
lean_dec(v_val_1734_);
lean_dec(v_val_1728_);
lean_dec_ref(v_h_1632_);
lean_dec_ref(v_e_1610_);
v_a_1798_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1738_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1738_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
}
else
{
lean_object* v___x_1807_; lean_object* v___x_1809_; 
lean_dec(v_a_1730_);
lean_dec(v_val_1728_);
lean_dec_ref(v_h_1632_);
lean_dec_ref(v_e_1610_);
v___x_1807_ = lean_box(0);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v___x_1807_);
v___x_1809_ = v___x_1732_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec(v_val_1728_);
lean_dec_ref(v_h_1632_);
lean_dec_ref(v_e_1610_);
v_a_1812_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1729_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1729_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1822_; 
lean_dec(v_a_1724_);
lean_dec_ref(v_h_1632_);
lean_dec_ref(v___y_1628_);
lean_dec_ref(v_e_1610_);
v___x_1820_ = lean_box(0);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1820_);
v___x_1822_ = v___x_1726_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
lean_dec_ref(v_h_1632_);
lean_dec_ref(v___y_1628_);
lean_dec_ref(v_e_1610_);
v_a_1825_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1723_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1723_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
v___jp_1833_:
{
lean_object* v_self_1848_; uint8_t v_interpreted_1849_; uint8_t v_ctor_1850_; lean_object* v___x_1851_; 
v_self_1848_ = lean_ctor_get(v___y_1844_, 0);
lean_inc_ref_n(v_self_1848_, 2);
v_interpreted_1849_ = lean_ctor_get_uint8(v___y_1844_, sizeof(void*)*12 + 1);
v_ctor_1850_ = lean_ctor_get_uint8(v___y_1844_, sizeof(void*)*12 + 2);
lean_dec_ref(v___y_1844_);
lean_inc_ref(v___y_1839_);
v___x_1851_ = l_Lean_Meta_Grind_hasSameType(v_self_1848_, v___y_1839_, v___y_1836_, v___y_1842_, v___y_1841_, v___y_1846_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1914_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1854_ = v___x_1851_;
v_isShared_1855_ = v_isSharedCheck_1914_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1851_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1914_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
uint8_t v___x_1856_; 
v___x_1856_ = lean_unbox(v_a_1852_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; lean_object* v___x_1859_; 
lean_dec(v_a_1852_);
lean_dec_ref(v_self_1848_);
lean_dec_ref(v___y_1845_);
lean_dec_ref(v___y_1839_);
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v___x_1857_ = lean_box(0);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v___x_1857_);
v___x_1859_ = v___x_1854_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
else
{
lean_del_object(v___x_1854_);
if (v___y_1847_ == 0)
{
lean_object* v___x_1861_; 
lean_inc(v___y_1846_);
lean_inc_ref(v___y_1841_);
lean_inc(v___y_1842_);
lean_inc_ref(v___y_1836_);
lean_inc(v___y_1843_);
lean_inc_ref(v___y_1835_);
lean_inc(v___y_1834_);
lean_inc_ref(v___y_1840_);
lean_inc(v___y_1837_);
lean_inc(v___y_1838_);
lean_inc_ref(v_self_1848_);
v___x_1861_ = lean_grind_mk_eq_proof(v_self_1848_, v___y_1845_, v___y_1838_, v___y_1837_, v___y_1840_, v___y_1834_, v___y_1835_, v___y_1843_, v___y_1836_, v___y_1842_, v___y_1841_, v___y_1846_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1863_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1862_);
lean_dec_ref_known(v___x_1861_, 1);
v___x_1863_ = l_Lean_Meta_mkEqTrans(v_a_1862_, v_h_1611_, v___y_1836_, v___y_1842_, v___y_1841_, v___y_1846_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; uint8_t v___x_1865_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref_known(v___x_1863_, 1);
v___x_1865_ = lean_unbox(v_a_1852_);
lean_dec(v_a_1852_);
v___y_1627_ = v___x_1865_;
v___y_1628_ = v___y_1839_;
v___y_1629_ = v_interpreted_1849_;
v___y_1630_ = v_self_1848_;
v___y_1631_ = v_ctor_1850_;
v_h_1632_ = v_a_1864_;
v___y_1633_ = v___y_1838_;
v___y_1634_ = v___y_1837_;
v___y_1635_ = v___y_1840_;
v___y_1636_ = v___y_1834_;
v___y_1637_ = v___y_1835_;
v___y_1638_ = v___y_1843_;
v___y_1639_ = v___y_1836_;
v___y_1640_ = v___y_1842_;
v___y_1641_ = v___y_1841_;
v___y_1642_ = v___y_1846_;
goto v___jp_1626_;
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec(v_a_1852_);
lean_dec_ref(v_self_1848_);
lean_dec_ref(v___y_1839_);
lean_dec_ref(v_e_1610_);
v_a_1866_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1863_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1863_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec(v_a_1852_);
lean_dec_ref(v_self_1848_);
lean_dec_ref(v___y_1839_);
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v_a_1874_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1861_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1861_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
else
{
lean_object* v___x_1882_; 
lean_inc(v___y_1846_);
lean_inc_ref(v___y_1841_);
lean_inc(v___y_1842_);
lean_inc_ref(v___y_1836_);
lean_inc(v___y_1843_);
lean_inc_ref(v___y_1835_);
lean_inc(v___y_1834_);
lean_inc_ref(v___y_1840_);
lean_inc(v___y_1837_);
lean_inc(v___y_1838_);
lean_inc_ref(v_self_1848_);
v___x_1882_ = lean_grind_mk_heq_proof(v_self_1848_, v___y_1845_, v___y_1838_, v___y_1837_, v___y_1840_, v___y_1834_, v___y_1835_, v___y_1843_, v___y_1836_, v___y_1842_, v___y_1841_, v___y_1846_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1884_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref_known(v___x_1882_, 1);
v___x_1884_ = l_Lean_Meta_mkHEqTrans(v_a_1883_, v_h_1611_, v___y_1836_, v___y_1842_, v___y_1841_, v___y_1846_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; uint8_t v___x_1886_; lean_object* v___x_1887_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref_known(v___x_1884_, 1);
v___x_1886_ = 0;
v___x_1887_ = l_Lean_Meta_mkEqOfHEq(v_a_1885_, v___x_1886_, v___y_1836_, v___y_1842_, v___y_1841_, v___y_1846_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; uint8_t v___x_1889_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref_known(v___x_1887_, 1);
v___x_1889_ = lean_unbox(v_a_1852_);
lean_dec(v_a_1852_);
v___y_1627_ = v___x_1889_;
v___y_1628_ = v___y_1839_;
v___y_1629_ = v_interpreted_1849_;
v___y_1630_ = v_self_1848_;
v___y_1631_ = v_ctor_1850_;
v_h_1632_ = v_a_1888_;
v___y_1633_ = v___y_1838_;
v___y_1634_ = v___y_1837_;
v___y_1635_ = v___y_1840_;
v___y_1636_ = v___y_1834_;
v___y_1637_ = v___y_1835_;
v___y_1638_ = v___y_1843_;
v___y_1639_ = v___y_1836_;
v___y_1640_ = v___y_1842_;
v___y_1641_ = v___y_1841_;
v___y_1642_ = v___y_1846_;
goto v___jp_1626_;
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec(v_a_1852_);
lean_dec_ref(v_self_1848_);
lean_dec_ref(v___y_1839_);
lean_dec_ref(v_e_1610_);
v_a_1890_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1887_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1887_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v_a_1852_);
lean_dec_ref(v_self_1848_);
lean_dec_ref(v___y_1839_);
lean_dec_ref(v_e_1610_);
v_a_1898_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1884_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1884_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec(v_a_1852_);
lean_dec_ref(v_self_1848_);
lean_dec_ref(v___y_1839_);
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v_a_1906_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1882_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1882_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
lean_dec_ref(v_self_1848_);
lean_dec_ref(v___y_1845_);
lean_dec_ref(v___y_1839_);
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v_a_1915_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1851_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1851_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
v___jp_1923_:
{
lean_object* v___x_1934_; 
lean_inc(v___y_1933_);
lean_inc_ref(v___y_1932_);
lean_inc(v___y_1931_);
lean_inc_ref(v___y_1930_);
lean_inc_ref(v_h_1611_);
v___x_1934_ = lean_infer_type(v_h_1611_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_2012_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_2012_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_2012_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1939_; 
v___x_1939_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_a_1935_);
lean_dec(v_a_1935_);
if (lean_obj_tag(v___x_1939_) == 1)
{
lean_object* v_val_1940_; lean_object* v_snd_1941_; lean_object* v_fst_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_2007_; 
lean_del_object(v___x_1937_);
v_val_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_val_1940_);
lean_dec_ref_known(v___x_1939_, 1);
v_snd_1941_ = lean_ctor_get(v_val_1940_, 1);
v_fst_1942_ = lean_ctor_get(v_val_1940_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_val_1940_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1944_ = v_val_1940_;
v_isShared_1945_ = v_isSharedCheck_2007_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_snd_1941_);
lean_inc(v_fst_1942_);
lean_dec(v_val_1940_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_2007_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v_fst_1946_; lean_object* v_snd_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_2006_; 
v_fst_1946_ = lean_ctor_get(v_snd_1941_, 0);
v_snd_1947_ = lean_ctor_get(v_snd_1941_, 1);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_snd_1941_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1949_ = v_snd_1941_;
v_isShared_1950_ = v_isSharedCheck_2006_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_snd_1947_);
lean_inc(v_fst_1946_);
lean_dec(v_snd_1941_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_2006_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_Meta_Sym_shareCommon(v_fst_1946_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1953_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
v___x_1953_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_a_1952_, v___y_1924_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref_known(v___x_1953_, 1);
if (lean_obj_tag(v_a_1954_) == 1)
{
lean_del_object(v___x_1949_);
lean_del_object(v___x_1944_);
if (lean_obj_tag(v_fst_1942_) == 0)
{
lean_object* v_val_1955_; uint8_t v___x_1956_; 
v_val_1955_ = lean_ctor_get(v_a_1954_, 0);
lean_inc(v_val_1955_);
lean_dec_ref_known(v_a_1954_, 1);
v___x_1956_ = 0;
v___y_1834_ = v___y_1927_;
v___y_1835_ = v___y_1928_;
v___y_1836_ = v___y_1930_;
v___y_1837_ = v___y_1925_;
v___y_1838_ = v___y_1924_;
v___y_1839_ = v_snd_1947_;
v___y_1840_ = v___y_1926_;
v___y_1841_ = v___y_1932_;
v___y_1842_ = v___y_1931_;
v___y_1843_ = v___y_1929_;
v___y_1844_ = v_val_1955_;
v___y_1845_ = v_a_1952_;
v___y_1846_ = v___y_1933_;
v___y_1847_ = v___x_1956_;
goto v___jp_1833_;
}
else
{
lean_object* v_val_1957_; uint8_t v___x_1958_; 
lean_dec_ref_known(v_fst_1942_, 1);
v_val_1957_ = lean_ctor_get(v_a_1954_, 0);
lean_inc(v_val_1957_);
lean_dec_ref_known(v_a_1954_, 1);
v___x_1958_ = 1;
v___y_1834_ = v___y_1927_;
v___y_1835_ = v___y_1928_;
v___y_1836_ = v___y_1930_;
v___y_1837_ = v___y_1925_;
v___y_1838_ = v___y_1924_;
v___y_1839_ = v_snd_1947_;
v___y_1840_ = v___y_1926_;
v___y_1841_ = v___y_1932_;
v___y_1842_ = v___y_1931_;
v___y_1843_ = v___y_1929_;
v___y_1844_ = v_val_1957_;
v___y_1845_ = v_a_1952_;
v___y_1846_ = v___y_1933_;
v___y_1847_ = v___x_1958_;
goto v___jp_1833_;
}
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1962_; 
lean_dec(v_a_1954_);
lean_dec(v_snd_1947_);
lean_dec(v_fst_1942_);
lean_dec_ref(v_h_1611_);
v___x_1959_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1);
v___x_1960_ = l_Lean_indentExpr(v_a_1952_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set_tag(v___x_1949_, 7);
lean_ctor_set(v___x_1949_, 1, v___x_1960_);
lean_ctor_set(v___x_1949_, 0, v___x_1959_);
v___x_1962_ = v___x_1949_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1959_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
lean_object* v___x_1963_; lean_object* v___x_1965_; 
v___x_1963_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3);
if (v_isShared_1945_ == 0)
{
lean_ctor_set_tag(v___x_1944_, 7);
lean_ctor_set(v___x_1944_, 1, v___x_1963_);
lean_ctor_set(v___x_1944_, 0, v___x_1962_);
v___x_1965_ = v___x_1944_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1962_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v___x_1963_);
v___x_1965_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = l_Lean_indentExpr(v_e_1610_);
v___x_1967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1965_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1928_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; uint8_t v_verbose_1970_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1968_, 1);
v_verbose_1970_ = lean_ctor_get_uint8(v_a_1969_, 0);
lean_dec(v_a_1969_);
if (v_verbose_1970_ == 0)
{
lean_dec_ref_known(v___x_1967_, 2);
goto v___jp_1623_;
}
else
{
lean_object* v___x_1971_; 
v___x_1971_ = l_Lean_Meta_Sym_reportIssue(v___x_1967_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_dec_ref_known(v___x_1971_, 1);
goto v___jp_1623_;
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1971_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1971_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref_known(v___x_1967_, 2);
v_a_1980_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1968_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1968_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_dec(v_a_1952_);
lean_del_object(v___x_1949_);
lean_dec(v_snd_1947_);
lean_del_object(v___x_1944_);
lean_dec(v_fst_1942_);
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v_a_1990_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1953_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1953_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
else
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
lean_del_object(v___x_1949_);
lean_dec(v_snd_1947_);
lean_del_object(v___x_1944_);
lean_dec(v_fst_1942_);
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v_a_1998_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1951_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1951_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
}
}
else
{
lean_object* v___x_2008_; lean_object* v___x_2010_; 
lean_dec(v___x_1939_);
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v___x_2008_ = lean_box(0);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 0, v___x_2008_);
v___x_2010_ = v___x_1937_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2008_);
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
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v_a_2013_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1934_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_1934_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(lean_object* v_e_2059_, lean_object* v_xs_2060_, lean_object* v___x_2061_, lean_object* v___x_2062_, uint8_t v_a_2063_, lean_object* v_a_2064_, lean_object* v_as_2065_, size_t v_sz_2066_, size_t v_i_2067_, lean_object* v_b_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
uint8_t v___y_2081_; uint8_t v___x_2129_; 
v___x_2129_ = lean_name_eq(v___x_2061_, v___x_2062_);
if (v___x_2129_ == 0)
{
uint8_t v___x_2130_; 
v___x_2130_ = 1;
v___y_2081_ = v___x_2130_;
goto v___jp_2080_;
}
else
{
uint8_t v___x_2131_; 
v___x_2131_ = 0;
v___y_2081_ = v___x_2131_;
goto v___jp_2080_;
}
v___jp_2080_:
{
uint8_t v___x_2082_; 
v___x_2082_ = lean_usize_dec_lt(v_i_2067_, v_sz_2066_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; 
lean_dec_ref(v_a_2064_);
lean_dec_ref(v_e_2059_);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v_b_2068_);
return v___x_2083_;
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v_a_2086_; lean_object* v___x_2087_; 
lean_dec_ref(v_b_2068_);
v___x_2084_ = lean_box(0);
v___x_2085_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_a_2086_ = lean_array_uget_borrowed(v_as_2065_, v_i_2067_);
lean_inc(v_a_2086_);
lean_inc_ref(v_e_2059_);
v___x_2087_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2059_, v_a_2086_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2087_, 1);
if (lean_obj_tag(v_a_2088_) == 1)
{
lean_object* v_val_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2117_; 
lean_dec_ref(v_e_2059_);
v_val_2089_ = lean_ctor_get(v_a_2088_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_a_2088_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2091_ = v_a_2088_;
v_isShared_2092_ = v_isSharedCheck_2117_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_val_2089_);
lean_dec(v_a_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2117_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
uint8_t v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = 1;
v___x_2094_ = l_Lean_Meta_mkLambdaFVars(v_xs_2060_, v_val_2089_, v___y_2081_, v_a_2063_, v___y_2081_, v_a_2063_, v___x_2093_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2108_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2108_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2108_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2099_ = l_Lean_Expr_app___override(v_a_2064_, v_a_2095_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2099_);
v___x_2101_ = v___x_2091_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2105_; 
v___x_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
v___x_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
lean_ctor_set(v___x_2103_, 1, v___x_2084_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2103_);
v___x_2105_ = v___x_2097_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
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
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_del_object(v___x_2091_);
lean_dec_ref(v_a_2064_);
v_a_2109_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2094_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2094_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
}
else
{
size_t v___x_2118_; size_t v___x_2119_; 
lean_dec(v_a_2088_);
v___x_2118_ = ((size_t)1ULL);
v___x_2119_ = lean_usize_add(v_i_2067_, v___x_2118_);
v_i_2067_ = v___x_2119_;
v_b_2068_ = v___x_2085_;
goto _start;
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec_ref(v_a_2064_);
lean_dec_ref(v_e_2059_);
v_a_2121_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2087_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2087_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(lean_object* v_e_2132_, lean_object* v_name_2133_, lean_object* v_name_2134_, uint8_t v_a_2135_, lean_object* v_a_2136_, lean_object* v_xs_2137_, lean_object* v_x_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; size_t v_sz_2152_; size_t v___x_2153_; lean_object* v___x_2154_; 
v___x_2150_ = lean_box(0);
v___x_2151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_sz_2152_ = lean_array_size(v_xs_2137_);
v___x_2153_ = ((size_t)0ULL);
v___x_2154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_2132_, v_xs_2137_, v_name_2133_, v_name_2134_, v_a_2135_, v_a_2136_, v_xs_2137_, v_sz_2152_, v___x_2153_, v___x_2151_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2167_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2157_ = v___x_2154_;
v_isShared_2158_ = v_isSharedCheck_2167_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2154_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2167_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v_fst_2159_; 
v_fst_2159_ = lean_ctor_get(v_a_2155_, 0);
lean_inc(v_fst_2159_);
lean_dec(v_a_2155_);
if (lean_obj_tag(v_fst_2159_) == 0)
{
lean_object* v___x_2161_; 
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v___x_2150_);
v___x_2161_ = v___x_2157_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2150_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
else
{
lean_object* v_val_2163_; lean_object* v___x_2165_; 
v_val_2163_ = lean_ctor_get(v_fst_2159_, 0);
lean_inc(v_val_2163_);
lean_dec_ref_known(v_fst_2159_, 1);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v_val_2163_);
v___x_2165_ = v___x_2157_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_val_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
v_a_2168_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2154_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2154_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_e_2176_ = _args[0];
lean_object* v_xs_2177_ = _args[1];
lean_object* v___x_2178_ = _args[2];
lean_object* v___x_2179_ = _args[3];
lean_object* v_a_2180_ = _args[4];
lean_object* v_a_2181_ = _args[5];
lean_object* v_as_2182_ = _args[6];
lean_object* v_sz_2183_ = _args[7];
lean_object* v_i_2184_ = _args[8];
lean_object* v_b_2185_ = _args[9];
lean_object* v___y_2186_ = _args[10];
lean_object* v___y_2187_ = _args[11];
lean_object* v___y_2188_ = _args[12];
lean_object* v___y_2189_ = _args[13];
lean_object* v___y_2190_ = _args[14];
lean_object* v___y_2191_ = _args[15];
lean_object* v___y_2192_ = _args[16];
lean_object* v___y_2193_ = _args[17];
lean_object* v___y_2194_ = _args[18];
lean_object* v___y_2195_ = _args[19];
lean_object* v___y_2196_ = _args[20];
_start:
{
uint8_t v_a_82930__boxed_2197_; size_t v_sz_boxed_2198_; size_t v_i_boxed_2199_; lean_object* v_res_2200_; 
v_a_82930__boxed_2197_ = lean_unbox(v_a_2180_);
v_sz_boxed_2198_ = lean_unbox_usize(v_sz_2183_);
lean_dec(v_sz_2183_);
v_i_boxed_2199_ = lean_unbox_usize(v_i_2184_);
lean_dec(v_i_2184_);
v_res_2200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_2176_, v_xs_2177_, v___x_2178_, v___x_2179_, v_a_82930__boxed_2197_, v_a_2181_, v_as_2182_, v_sz_boxed_2198_, v_i_boxed_2199_, v_b_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v_as_2182_);
lean_dec(v___x_2179_);
lean_dec(v___x_2178_);
lean_dec_ref(v_xs_2177_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___boxed(lean_object* v_e_2201_, lean_object* v_h_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2201_, v_h_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
lean_dec(v_a_2210_);
lean_dec_ref(v_a_2209_);
lean_dec(v_a_2208_);
lean_dec_ref(v_a_2207_);
lean_dec(v_a_2206_);
lean_dec_ref(v_a_2205_);
lean_dec(v_a_2204_);
lean_dec(v_a_2203_);
return v_res_2214_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__0));
v___x_2217_ = l_Lean_stringToMessageData(v___x_2216_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(lean_object* v_e_2218_, lean_object* v_xs_2219_, uint8_t v___x_2220_, lean_object* v_as_2221_, size_t v_sz_2222_, size_t v_i_2223_, lean_object* v_b_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_a_2237_; uint8_t v___x_2241_; 
v___x_2241_ = lean_usize_dec_lt(v_i_2223_, v_sz_2222_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; 
lean_dec_ref(v_e_2218_);
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v_b_2224_);
return v___x_2242_;
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v_a_2246_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___x_2297_; 
lean_dec_ref(v_b_2224_);
v___x_2243_ = lean_box(0);
v___x_2244_ = lean_box(0);
v___x_2245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_a_2246_ = lean_array_uget_borrowed(v_as_2221_, v_i_2223_);
lean_inc(v___y_2234_);
lean_inc_ref(v___y_2233_);
lean_inc(v___y_2232_);
lean_inc_ref(v___y_2231_);
lean_inc(v_a_2246_);
v___x_2297_ = lean_infer_type(v_a_2246_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2299_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___x_2297_, 1);
v___x_2299_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_a_2298_, v___x_2244_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; uint8_t v___x_2301_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v___x_2301_ = lean_unbox(v_a_2300_);
lean_dec(v_a_2300_);
if (v___x_2301_ == 0)
{
lean_dec(v_a_2298_);
v_a_2237_ = v___x_2245_;
goto v___jp_2236_;
}
else
{
lean_object* v_toCold_2302_; lean_object* v_options_2303_; uint8_t v_hasTrace_2304_; 
v_toCold_2302_ = lean_ctor_get(v___y_2233_, 0);
v_options_2303_ = lean_ctor_get(v_toCold_2302_, 2);
v_hasTrace_2304_ = lean_ctor_get_uint8(v_options_2303_, sizeof(void*)*1);
if (v_hasTrace_2304_ == 0)
{
lean_dec(v_a_2298_);
v___y_2248_ = v___y_2225_;
v___y_2249_ = v___y_2226_;
v___y_2250_ = v___y_2227_;
v___y_2251_ = v___y_2228_;
v___y_2252_ = v___y_2229_;
v___y_2253_ = v___y_2230_;
v___y_2254_ = v___y_2231_;
v___y_2255_ = v___y_2232_;
v___y_2256_ = v___y_2233_;
v___y_2257_ = v___y_2234_;
goto v___jp_2247_;
}
else
{
lean_object* v_inheritedTraceOptions_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; 
v_inheritedTraceOptions_2305_ = lean_ctor_get(v_toCold_2302_, 11);
v___x_2306_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_2307_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_2308_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2305_, v_options_2303_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_dec(v_a_2298_);
v___y_2248_ = v___y_2225_;
v___y_2249_ = v___y_2226_;
v___y_2250_ = v___y_2227_;
v___y_2251_ = v___y_2228_;
v___y_2252_ = v___y_2229_;
v___y_2253_ = v___y_2230_;
v___y_2254_ = v___y_2231_;
v___y_2255_ = v___y_2232_;
v___y_2256_ = v___y_2233_;
v___y_2257_ = v___y_2234_;
goto v___jp_2247_;
}
else
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Lean_Meta_Grind_updateLastTag(v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
lean_dec_ref_known(v___x_2309_, 1);
v___x_2310_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1);
v___x_2311_ = l_Lean_MessageData_ofExpr(v_a_2298_);
v___x_2312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2310_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
v___x_2313_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_2306_, v___x_2312_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_dec_ref_known(v___x_2313_, 1);
v___y_2248_ = v___y_2225_;
v___y_2249_ = v___y_2226_;
v___y_2250_ = v___y_2227_;
v___y_2251_ = v___y_2228_;
v___y_2252_ = v___y_2229_;
v___y_2253_ = v___y_2230_;
v___y_2254_ = v___y_2231_;
v___y_2255_ = v___y_2232_;
v___y_2256_ = v___y_2233_;
v___y_2257_ = v___y_2234_;
goto v___jp_2247_;
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec_ref(v_e_2218_);
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
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
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec(v_a_2298_);
lean_dec_ref(v_e_2218_);
v_a_2322_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2309_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2309_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
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
}
}
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
lean_dec(v_a_2298_);
lean_dec_ref(v_e_2218_);
v_a_2330_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2332_ = v___x_2299_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2299_);
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
lean_dec_ref(v_e_2218_);
v_a_2338_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2297_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2297_);
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
v___jp_2247_:
{
lean_object* v___x_2258_; 
lean_inc(v_a_2246_);
lean_inc_ref(v_e_2218_);
v___x_2258_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2218_, v_a_2246_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_a_2259_);
lean_dec_ref_known(v___x_2258_, 1);
if (lean_obj_tag(v_a_2259_) == 1)
{
lean_object* v_val_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2288_; 
lean_dec_ref(v_e_2218_);
v_val_2260_ = lean_ctor_get(v_a_2259_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v_a_2259_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2262_ = v_a_2259_;
v_isShared_2263_ = v_isSharedCheck_2288_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_val_2260_);
lean_dec(v_a_2259_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2288_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
uint8_t v___x_2264_; uint8_t v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = 0;
v___x_2265_ = 1;
v___x_2266_ = l_Lean_Meta_mkLambdaFVars(v_xs_2219_, v_val_2260_, v___x_2264_, v___x_2220_, v___x_2264_, v___x_2220_, v___x_2265_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2279_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2269_ = v___x_2266_;
v_isShared_2270_ = v_isSharedCheck_2279_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2266_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2279_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v_a_2267_);
v___x_2272_ = v___x_2262_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
v___x_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
lean_ctor_set(v___x_2274_, 1, v___x_2243_);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 0, v___x_2274_);
v___x_2276_ = v___x_2269_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_del_object(v___x_2262_);
v_a_2280_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2266_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2266_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
}
else
{
lean_dec(v_a_2259_);
v_a_2237_ = v___x_2245_;
goto v___jp_2236_;
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec_ref(v_e_2218_);
v_a_2289_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2258_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2258_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
}
v___jp_2236_:
{
size_t v___x_2238_; size_t v___x_2239_; 
v___x_2238_ = ((size_t)1ULL);
v___x_2239_ = lean_usize_add(v_i_2223_, v___x_2238_);
lean_inc_ref(v_a_2237_);
v_i_2223_ = v___x_2239_;
v_b_2224_ = v_a_2237_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_e_2346_ = _args[0];
lean_object* v_xs_2347_ = _args[1];
lean_object* v___x_2348_ = _args[2];
lean_object* v_as_2349_ = _args[3];
lean_object* v_sz_2350_ = _args[4];
lean_object* v_i_2351_ = _args[5];
lean_object* v_b_2352_ = _args[6];
lean_object* v___y_2353_ = _args[7];
lean_object* v___y_2354_ = _args[8];
lean_object* v___y_2355_ = _args[9];
lean_object* v___y_2356_ = _args[10];
lean_object* v___y_2357_ = _args[11];
lean_object* v___y_2358_ = _args[12];
lean_object* v___y_2359_ = _args[13];
lean_object* v___y_2360_ = _args[14];
lean_object* v___y_2361_ = _args[15];
lean_object* v___y_2362_ = _args[16];
lean_object* v___y_2363_ = _args[17];
_start:
{
uint8_t v___x_21114__boxed_2364_; size_t v_sz_boxed_2365_; size_t v_i_boxed_2366_; lean_object* v_res_2367_; 
v___x_21114__boxed_2364_ = lean_unbox(v___x_2348_);
v_sz_boxed_2365_ = lean_unbox_usize(v_sz_2350_);
lean_dec(v_sz_2350_);
v_i_boxed_2366_ = lean_unbox_usize(v_i_2351_);
lean_dec(v_i_2351_);
v_res_2367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2346_, v_xs_2347_, v___x_21114__boxed_2364_, v_as_2349_, v_sz_boxed_2365_, v_i_boxed_2366_, v_b_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v_as_2349_);
lean_dec_ref(v_xs_2347_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(lean_object* v_e_2368_, uint8_t v___x_2369_, lean_object* v_xs_2370_, lean_object* v_x_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; size_t v_sz_2385_; size_t v___x_2386_; lean_object* v___x_2387_; 
v___x_2383_ = lean_box(0);
v___x_2384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_sz_2385_ = lean_array_size(v_xs_2370_);
v___x_2386_ = ((size_t)0ULL);
v___x_2387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2368_, v_xs_2370_, v___x_2369_, v_xs_2370_, v_sz_2385_, v___x_2386_, v___x_2384_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2400_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2390_ = v___x_2387_;
v_isShared_2391_ = v_isSharedCheck_2400_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2387_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2400_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v_fst_2392_; 
v_fst_2392_ = lean_ctor_get(v_a_2388_, 0);
lean_inc(v_fst_2392_);
lean_dec(v_a_2388_);
if (lean_obj_tag(v_fst_2392_) == 0)
{
lean_object* v___x_2394_; 
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v___x_2383_);
v___x_2394_ = v___x_2390_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2383_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
else
{
lean_object* v_val_2396_; lean_object* v___x_2398_; 
v_val_2396_ = lean_ctor_get(v_fst_2392_, 0);
lean_inc(v_val_2396_);
lean_dec_ref_known(v_fst_2392_, 1);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v_val_2396_);
v___x_2398_ = v___x_2390_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_val_2396_);
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
v_a_2401_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2387_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2387_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed(lean_object* v_e_2409_, lean_object* v___x_2410_, lean_object* v_xs_2411_, lean_object* v_x_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
uint8_t v___x_21368__boxed_2424_; lean_object* v_res_2425_; 
v___x_21368__boxed_2424_ = lean_unbox(v___x_2410_);
v_res_2425_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(v_e_2409_, v___x_21368__boxed_2424_, v_xs_2411_, v_x_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec_ref(v_x_2412_);
lean_dec_ref(v_xs_2411_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(lean_object* v_e_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v___x_2441_; 
lean_inc_ref(v_e_2426_);
v___x_2441_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2426_, v_a_2434_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2443_; uint8_t v___x_2444_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_a_2442_);
lean_dec_ref_known(v___x_2441_, 1);
v___x_2443_ = l_Lean_Expr_cleanupAnnotations(v_a_2442_);
lean_dec(v_a_2442_);
v___x_2444_ = l_Lean_Expr_isApp(v___x_2443_);
if (v___x_2444_ == 0)
{
lean_dec_ref(v___x_2443_);
lean_dec_ref(v_e_2426_);
goto v___jp_2438_;
}
else
{
lean_object* v___x_2445_; lean_object* v___x_2446_; uint8_t v___x_2447_; 
v___x_2445_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2443_);
v___x_2446_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_2447_ = l_Lean_Expr_isConstOf(v___x_2445_, v___x_2446_);
lean_dec_ref(v___x_2445_);
if (v___x_2447_ == 0)
{
lean_dec_ref(v___x_2443_);
lean_dec_ref(v_e_2426_);
goto v___jp_2438_;
}
else
{
lean_object* v_arg_2448_; lean_object* v___x_2449_; lean_object* v___f_2450_; uint8_t v___x_2451_; lean_object* v___x_2452_; 
v_arg_2448_ = lean_ctor_get(v___x_2443_, 1);
lean_inc_ref(v_arg_2448_);
lean_dec_ref(v___x_2443_);
v___x_2449_ = lean_box(v___x_2447_);
v___f_2450_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed), 15, 2);
lean_closure_set(v___f_2450_, 0, v_e_2426_);
lean_closure_set(v___f_2450_, 1, v___x_2449_);
v___x_2451_ = 0;
v___x_2452_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_arg_2448_, v___f_2450_, v___x_2451_, v___x_2451_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
return v___x_2452_;
}
}
}
else
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_dec_ref(v_e_2426_);
v_a_2453_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2441_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2441_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
v___jp_2438_:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = lean_box(0);
v___x_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
return v___x_2440_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___boxed(lean_object* v_e_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
lean_dec(v_a_2465_);
lean_dec_ref(v_a_2464_);
lean_dec(v_a_2463_);
lean_dec(v_a_2462_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(lean_object* v_e_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_){
_start:
{
lean_object* v___x_2480_; uint8_t v___x_2481_; uint8_t v___x_2482_; 
v___x_2480_ = l_Lean_Expr_getAppFn(v_e_2474_);
v___x_2481_ = l_Lean_Expr_isMVar(v___x_2480_);
lean_dec_ref(v___x_2480_);
v___x_2482_ = 1;
if (v___x_2481_ == 0)
{
lean_object* v___x_2483_; 
lean_inc_ref(v_e_2474_);
v___x_2483_ = l_Lean_Meta_isConstructorApp_x3f(v_e_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2493_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2493_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2493_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
if (lean_obj_tag(v_a_2484_) == 0)
{
lean_object* v___x_2488_; 
lean_del_object(v___x_2486_);
v___x_2488_ = l_Lean_Meta_isLitValue(v_e_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_);
return v___x_2488_;
}
else
{
lean_object* v___x_2489_; lean_object* v___x_2491_; 
lean_dec_ref_known(v_a_2484_, 1);
lean_dec_ref(v_e_2474_);
v___x_2489_ = lean_box(v___x_2482_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 0, v___x_2489_);
v___x_2491_ = v___x_2486_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
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
else
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_dec_ref(v_e_2474_);
v_a_2494_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2483_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2483_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
else
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
lean_dec_ref(v_e_2474_);
v___x_2502_ = lean_box(v___x_2482_);
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
return v___x_2503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg___boxed(lean_object* v_e_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(v_e_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike(lean_object* v_e_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(v_e_2511_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___boxed(lean_object* v_e_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike(v_e_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
lean_dec(v_a_2534_);
lean_dec_ref(v_a_2533_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
lean_dec(v_a_2530_);
lean_dec_ref(v_a_2529_);
lean_dec(v_a_2528_);
lean_dec_ref(v_a_2527_);
lean_dec(v_a_2526_);
lean_dec(v_a_2525_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(lean_object* v_e_2537_, lean_object* v_pat_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_){
_start:
{
lean_object* v___x_2550_; uint8_t v_modified_2551_; 
v___x_2550_ = l_Lean_Expr_getAppFn(v_pat_2538_);
v_modified_2551_ = l_Lean_Expr_isMVar(v___x_2550_);
lean_dec_ref(v___x_2550_);
if (v_modified_2551_ == 0)
{
lean_object* v___x_2552_; 
lean_inc_ref(v_e_2537_);
v___x_2552_ = l_Lean_Meta_Grind_getRootENode___redArg(v_e_2537_, v_a_2539_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2653_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2555_ = v___x_2552_;
v_isShared_2556_ = v_isSharedCheck_2653_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2552_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2653_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
uint8_t v_ctor_2557_; 
v_ctor_2557_ = lean_ctor_get_uint8(v_a_2553_, sizeof(void*)*12 + 2);
if (v_ctor_2557_ == 0)
{
uint8_t v_interpreted_2558_; 
lean_dec_ref(v_pat_2538_);
v_interpreted_2558_ = lean_ctor_get_uint8(v_a_2553_, sizeof(void*)*12 + 1);
if (v_interpreted_2558_ == 0)
{
lean_object* v___x_2560_; 
lean_dec(v_a_2553_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v_e_2537_);
v___x_2560_ = v___x_2555_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_e_2537_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
else
{
lean_object* v_self_2562_; lean_object* v___x_2564_; 
lean_dec_ref(v_e_2537_);
v_self_2562_ = lean_ctor_get(v_a_2553_, 0);
lean_inc_ref(v_self_2562_);
lean_dec(v_a_2553_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v_self_2562_);
v___x_2564_ = v___x_2555_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_self_2562_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
else
{
lean_object* v_self_2566_; lean_object* v___x_2567_; 
lean_del_object(v___x_2555_);
lean_dec_ref(v_e_2537_);
v_self_2566_ = lean_ctor_get(v_a_2553_, 0);
lean_inc_ref_n(v_self_2566_, 2);
lean_dec(v_a_2553_);
v___x_2567_ = l_Lean_Meta_isConstructorApp_x3f(v_self_2566_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2644_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2570_ = v___x_2567_;
v_isShared_2571_ = v_isSharedCheck_2644_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2567_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2644_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
if (lean_obj_tag(v_a_2568_) == 1)
{
lean_object* v_val_2572_; lean_object* v___x_2573_; 
lean_del_object(v___x_2570_);
v_val_2572_ = lean_ctor_get(v_a_2568_, 0);
lean_inc(v_val_2572_);
lean_dec_ref_known(v_a_2568_, 1);
lean_inc_ref(v_pat_2538_);
v___x_2573_ = l_Lean_Meta_isConstructorApp_x3f(v_pat_2538_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2632_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2576_ = v___x_2573_;
v_isShared_2577_ = v_isSharedCheck_2632_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2573_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2632_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
if (lean_obj_tag(v_a_2574_) == 1)
{
lean_object* v_toConstantVal_2578_; lean_object* v_val_2579_; lean_object* v_toConstantVal_2580_; lean_object* v_numParams_2581_; lean_object* v_numFields_2582_; lean_object* v_name_2583_; lean_object* v_name_2584_; uint8_t v___x_2585_; 
v_toConstantVal_2578_ = lean_ctor_get(v_val_2572_, 0);
lean_inc_ref(v_toConstantVal_2578_);
v_val_2579_ = lean_ctor_get(v_a_2574_, 0);
lean_inc(v_val_2579_);
lean_dec_ref_known(v_a_2574_, 1);
v_toConstantVal_2580_ = lean_ctor_get(v_val_2579_, 0);
lean_inc_ref(v_toConstantVal_2580_);
lean_dec(v_val_2579_);
v_numParams_2581_ = lean_ctor_get(v_val_2572_, 3);
lean_inc(v_numParams_2581_);
v_numFields_2582_ = lean_ctor_get(v_val_2572_, 4);
lean_inc(v_numFields_2582_);
lean_dec(v_val_2572_);
v_name_2583_ = lean_ctor_get(v_toConstantVal_2578_, 0);
lean_inc(v_name_2583_);
lean_dec_ref(v_toConstantVal_2578_);
v_name_2584_ = lean_ctor_get(v_toConstantVal_2580_, 0);
lean_inc(v_name_2584_);
lean_dec_ref(v_toConstantVal_2580_);
v___x_2585_ = lean_name_eq(v_name_2583_, v_name_2584_);
lean_dec(v_name_2584_);
lean_dec(v_name_2583_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2587_; 
lean_dec(v_numFields_2582_);
lean_dec(v_numParams_2581_);
lean_dec_ref(v_pat_2538_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v_self_2566_);
v___x_2587_ = v___x_2576_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_self_2566_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
else
{
lean_object* v___x_2589_; lean_object* v___x_2590_; uint8_t v___x_2591_; 
v___x_2589_ = lean_nat_add(v_numParams_2581_, v_numFields_2582_);
lean_dec(v_numFields_2582_);
v___x_2590_ = l_Lean_Expr_getAppNumArgs(v_pat_2538_);
v___x_2591_ = lean_nat_dec_eq(v___x_2590_, v___x_2589_);
if (v___x_2591_ == 0)
{
lean_object* v___x_2593_; 
lean_dec(v___x_2590_);
lean_dec(v___x_2589_);
lean_dec(v_numParams_2581_);
lean_dec_ref(v_pat_2538_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v_self_2566_);
v___x_2593_ = v___x_2576_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_self_2566_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
else
{
lean_object* v_nargs_2595_; lean_object* v_dummy_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
lean_del_object(v___x_2576_);
v_nargs_2595_ = l_Lean_Expr_getAppNumArgs(v_self_2566_);
v_dummy_2596_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0);
lean_inc(v_nargs_2595_);
v___x_2597_ = lean_mk_array(v_nargs_2595_, v_dummy_2596_);
v___x_2598_ = lean_unsigned_to_nat(1u);
v___x_2599_ = lean_nat_sub(v_nargs_2595_, v___x_2598_);
lean_dec(v_nargs_2595_);
lean_inc_ref(v_self_2566_);
v___x_2600_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_2566_, v___x_2597_, v___x_2599_);
v___x_2601_ = lean_box(v_modified_2551_);
v___x_2602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2600_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
lean_inc(v___x_2590_);
v___x_2603_ = lean_mk_array(v___x_2590_, v_dummy_2596_);
v___x_2604_ = lean_nat_sub(v___x_2590_, v___x_2598_);
lean_dec(v___x_2590_);
v___x_2605_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_pat_2538_, v___x_2603_, v___x_2604_);
v___x_2606_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v___x_2589_, v___x_2605_, v_numParams_2581_, v___x_2602_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
lean_dec_ref(v___x_2605_);
lean_dec(v___x_2589_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2620_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2609_ = v___x_2606_;
v_isShared_2610_ = v_isSharedCheck_2620_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2606_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2620_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v_snd_2611_; uint8_t v___x_2612_; 
v_snd_2611_ = lean_ctor_get(v_a_2607_, 1);
v___x_2612_ = lean_unbox(v_snd_2611_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2614_; 
lean_dec(v_a_2607_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v_self_2566_);
v___x_2614_ = v___x_2609_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_self_2566_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
else
{
lean_object* v_fst_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
lean_del_object(v___x_2609_);
v_fst_2616_ = lean_ctor_get(v_a_2607_, 0);
lean_inc(v_fst_2616_);
lean_dec(v_a_2607_);
v___x_2617_ = l_Lean_Expr_getAppFn(v_self_2566_);
lean_dec_ref(v_self_2566_);
v___x_2618_ = l_Lean_mkAppN(v___x_2617_, v_fst_2616_);
lean_dec(v_fst_2616_);
v___x_2619_ = l_Lean_Meta_Sym_shareCommon(v___x_2618_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
return v___x_2619_;
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec_ref(v_self_2566_);
v_a_2621_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2606_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2606_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
}
else
{
lean_object* v___x_2630_; 
lean_dec(v_a_2574_);
lean_dec(v_val_2572_);
lean_dec_ref(v_pat_2538_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v_self_2566_);
v___x_2630_ = v___x_2576_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_self_2566_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec(v_val_2572_);
lean_dec_ref(v_self_2566_);
lean_dec_ref(v_pat_2538_);
v_a_2633_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2573_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2573_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
else
{
lean_object* v___x_2642_; 
lean_dec(v_a_2568_);
lean_dec_ref(v_pat_2538_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v_self_2566_);
v___x_2642_ = v___x_2570_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_self_2566_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec_ref(v_self_2566_);
lean_dec_ref(v_pat_2538_);
v_a_2645_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2567_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2567_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec_ref(v_pat_2538_);
lean_dec_ref(v_e_2537_);
v_a_2654_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2552_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2552_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
else
{
lean_object* v___x_2662_; 
lean_dec_ref(v_pat_2538_);
v___x_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2662_, 0, v_e_2537_);
return v___x_2662_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(lean_object* v_upperBound_2663_, lean_object* v___x_2664_, lean_object* v_a_2665_, lean_object* v_b_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v_a_2679_; uint8_t v_modified_2683_; 
v_modified_2683_ = lean_nat_dec_lt(v_a_2665_, v_upperBound_2663_);
if (v_modified_2683_ == 0)
{
lean_object* v___x_2684_; 
lean_dec(v_a_2665_);
v___x_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2684_, 0, v_b_2666_);
return v___x_2684_;
}
else
{
lean_object* v_fst_2685_; lean_object* v_snd_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2714_; 
v_fst_2685_ = lean_ctor_get(v_b_2666_, 0);
v_snd_2686_ = lean_ctor_get(v_b_2666_, 1);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_b_2666_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2688_ = v_b_2666_;
v_isShared_2689_ = v_isSharedCheck_2714_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_snd_2686_);
lean_inc(v_fst_2685_);
lean_dec(v_b_2666_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2714_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2690_ = l_Lean_instInhabitedExpr;
v___x_2691_ = lean_array_get_borrowed(v___x_2690_, v_fst_2685_, v_a_2665_);
v___x_2692_ = lean_array_get_borrowed(v___x_2690_, v___x_2664_, v_a_2665_);
lean_inc(v___x_2692_);
lean_inc(v___x_2691_);
v___x_2693_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v___x_2691_, v___x_2692_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; size_t v___x_2695_; size_t v___x_2696_; uint8_t v___x_2697_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref_known(v___x_2693_, 1);
v___x_2695_ = lean_ptr_addr(v___x_2691_);
v___x_2696_ = lean_ptr_addr(v_a_2694_);
v___x_2697_ = lean_usize_dec_eq(v___x_2695_, v___x_2696_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2701_; 
lean_dec(v_snd_2686_);
v___x_2698_ = lean_array_set(v_fst_2685_, v_a_2665_, v_a_2694_);
v___x_2699_ = lean_box(v_modified_2683_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 1, v___x_2699_);
lean_ctor_set(v___x_2688_, 0, v___x_2698_);
v___x_2701_ = v___x_2688_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2698_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
v_a_2679_ = v___x_2701_;
goto v___jp_2678_;
}
}
else
{
lean_object* v___x_2704_; 
lean_dec(v_a_2694_);
if (v_isShared_2689_ == 0)
{
v___x_2704_ = v___x_2688_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_fst_2685_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v_snd_2686_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
v_a_2679_ = v___x_2704_;
goto v___jp_2678_;
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_del_object(v___x_2688_);
lean_dec(v_snd_2686_);
lean_dec(v_fst_2685_);
lean_dec(v_a_2665_);
v_a_2706_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2693_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2693_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
}
v___jp_2678_:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2680_ = lean_unsigned_to_nat(1u);
v___x_2681_ = lean_nat_add(v_a_2665_, v___x_2680_);
lean_dec(v_a_2665_);
v_a_2665_ = v___x_2681_;
v_b_2666_ = v_a_2679_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg___boxed(lean_object* v_upperBound_2715_, lean_object* v___x_2716_, lean_object* v_a_2717_, lean_object* v_b_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2715_, v___x_2716_, v_a_2717_, v_b_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___x_2716_);
lean_dec(v_upperBound_2715_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go___boxed(lean_object* v_e_2731_, lean_object* v_pat_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_e_2731_, v_pat_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_);
lean_dec(v_a_2742_);
lean_dec_ref(v_a_2741_);
lean_dec(v_a_2740_);
lean_dec_ref(v_a_2739_);
lean_dec(v_a_2738_);
lean_dec_ref(v_a_2737_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
lean_dec(v_a_2734_);
lean_dec(v_a_2733_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(lean_object* v_upperBound_2745_, lean_object* v___x_2746_, lean_object* v_inst_2747_, lean_object* v_R_2748_, lean_object* v_a_2749_, lean_object* v_b_2750_, lean_object* v_c_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2745_, v___x_2746_, v_a_2749_, v_b_2750_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_2764_ = _args[0];
lean_object* v___x_2765_ = _args[1];
lean_object* v_inst_2766_ = _args[2];
lean_object* v_R_2767_ = _args[3];
lean_object* v_a_2768_ = _args[4];
lean_object* v_b_2769_ = _args[5];
lean_object* v_c_2770_ = _args[6];
lean_object* v___y_2771_ = _args[7];
lean_object* v___y_2772_ = _args[8];
lean_object* v___y_2773_ = _args[9];
lean_object* v___y_2774_ = _args[10];
lean_object* v___y_2775_ = _args[11];
lean_object* v___y_2776_ = _args[12];
lean_object* v___y_2777_ = _args[13];
lean_object* v___y_2778_ = _args[14];
lean_object* v___y_2779_ = _args[15];
lean_object* v___y_2780_ = _args[16];
lean_object* v___y_2781_ = _args[17];
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(v_upperBound_2764_, v___x_2765_, v_inst_2766_, v_R_2767_, v_a_2768_, v_b_2769_, v_c_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___x_2765_);
lean_dec(v_upperBound_2764_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(lean_object* v_e_2783_, lean_object* v___y_2784_){
_start:
{
uint8_t v___x_2786_; 
v___x_2786_ = l_Lean_Expr_hasMVar(v_e_2783_);
if (v___x_2786_ == 0)
{
lean_object* v___x_2787_; 
v___x_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2787_, 0, v_e_2783_);
return v___x_2787_;
}
else
{
lean_object* v___x_2788_; lean_object* v_mctx_2789_; lean_object* v___x_2790_; lean_object* v_fst_2791_; lean_object* v_snd_2792_; lean_object* v___x_2793_; lean_object* v_cache_2794_; lean_object* v_zetaDeltaFVarIds_2795_; lean_object* v_postponed_2796_; lean_object* v_diag_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2806_; 
v___x_2788_ = lean_st_ref_get(v___y_2784_);
v_mctx_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc_ref(v_mctx_2789_);
lean_dec(v___x_2788_);
v___x_2790_ = l_Lean_instantiateMVarsCore(v_mctx_2789_, v_e_2783_);
v_fst_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_fst_2791_);
v_snd_2792_ = lean_ctor_get(v___x_2790_, 1);
lean_inc(v_snd_2792_);
lean_dec_ref(v___x_2790_);
v___x_2793_ = lean_st_ref_take(v___y_2784_);
v_cache_2794_ = lean_ctor_get(v___x_2793_, 1);
v_zetaDeltaFVarIds_2795_ = lean_ctor_get(v___x_2793_, 2);
v_postponed_2796_ = lean_ctor_get(v___x_2793_, 3);
v_diag_2797_ = lean_ctor_get(v___x_2793_, 4);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2806_ == 0)
{
lean_object* v_unused_2807_; 
v_unused_2807_ = lean_ctor_get(v___x_2793_, 0);
lean_dec(v_unused_2807_);
v___x_2799_ = v___x_2793_;
v_isShared_2800_ = v_isSharedCheck_2806_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_diag_2797_);
lean_inc(v_postponed_2796_);
lean_inc(v_zetaDeltaFVarIds_2795_);
lean_inc(v_cache_2794_);
lean_dec(v___x_2793_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2806_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2802_; 
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v_snd_2792_);
v___x_2802_ = v___x_2799_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_snd_2792_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v_cache_2794_);
lean_ctor_set(v_reuseFailAlloc_2805_, 2, v_zetaDeltaFVarIds_2795_);
lean_ctor_set(v_reuseFailAlloc_2805_, 3, v_postponed_2796_);
lean_ctor_set(v_reuseFailAlloc_2805_, 4, v_diag_2797_);
v___x_2802_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = lean_st_ref_put(v___y_2784_, v___x_2802_);
v___x_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2804_, 0, v_fst_2791_);
return v___x_2804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg___boxed(lean_object* v_e_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v_e_2808_, v___y_2809_);
lean_dec(v___y_2809_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(lean_object* v_e_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v_e_2812_, v___y_2820_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___boxed(lean_object* v_e_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(v_e_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec(v___y_2826_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0(lean_object* v_k_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v___x_2850_; 
lean_inc(v___y_2844_);
lean_inc_ref(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc_ref(v___y_2841_);
lean_inc(v___y_2840_);
lean_inc(v___y_2839_);
v___x_2850_ = lean_apply_11(v_k_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, lean_box(0));
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0___boxed(lean_object* v_k_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0(v_k_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec(v___y_2852_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(lean_object* v_k_2864_, uint8_t v_allowLevelAssignments_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v___f_2877_; lean_object* v___x_2878_; 
lean_inc(v___y_2871_);
lean_inc_ref(v___y_2870_);
lean_inc(v___y_2869_);
lean_inc_ref(v___y_2868_);
lean_inc(v___y_2867_);
lean_inc(v___y_2866_);
v___f_2877_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_2877_, 0, v_k_2864_);
lean_closure_set(v___f_2877_, 1, v___y_2866_);
lean_closure_set(v___f_2877_, 2, v___y_2867_);
lean_closure_set(v___f_2877_, 3, v___y_2868_);
lean_closure_set(v___f_2877_, 4, v___y_2869_);
lean_closure_set(v___f_2877_, 5, v___y_2870_);
lean_closure_set(v___f_2877_, 6, v___y_2871_);
v___x_2878_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2865_, v___f_2877_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
if (lean_obj_tag(v___x_2878_) == 0)
{
return v___x_2878_;
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2878_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2878_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___boxed(lean_object* v_k_2887_, lean_object* v_allowLevelAssignments_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2900_; lean_object* v_res_2901_; 
v_allowLevelAssignments_boxed_2900_ = lean_unbox(v_allowLevelAssignments_2888_);
v_res_2901_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(v_k_2887_, v_allowLevelAssignments_boxed_2900_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2889_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(lean_object* v_00_u03b1_2902_, lean_object* v_k_2903_, uint8_t v_allowLevelAssignments_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(v_k_2903_, v_allowLevelAssignments_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___boxed(lean_object* v_00_u03b1_2917_, lean_object* v_k_2918_, lean_object* v_allowLevelAssignments_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2931_; lean_object* v_res_2932_; 
v_allowLevelAssignments_boxed_2931_ = lean_unbox(v_allowLevelAssignments_2919_);
v_res_2932_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_00_u03b1_2917_, v_k_2918_, v_allowLevelAssignments_boxed_2931_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec(v___y_2920_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0(lean_object* v_cls_2933_, lean_object* v_____do__lift_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v_toCold_2946_; lean_object* v_options_2947_; uint8_t v_hasTrace_2948_; 
v_toCold_2946_ = lean_ctor_get(v___y_2943_, 0);
v_options_2947_ = lean_ctor_get(v_toCold_2946_, 2);
v_hasTrace_2948_ = lean_ctor_get_uint8(v_options_2947_, sizeof(void*)*1);
if (v_hasTrace_2948_ == 0)
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
lean_dec(v_cls_2933_);
v___x_2949_ = lean_box(v_hasTrace_2948_);
v___x_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
return v___x_2950_;
}
else
{
lean_object* v___x_2951_; lean_object* v___x_2952_; uint8_t v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2951_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5));
v___x_2952_ = l_Lean_Name_append(v___x_2951_, v_cls_2933_);
v___x_2953_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2934_, v_options_2947_, v___x_2952_);
lean_dec(v___x_2952_);
v___x_2954_ = lean_box(v___x_2953_);
v___x_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
return v___x_2955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed(lean_object* v_cls_2956_, lean_object* v_____do__lift_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Lean_Meta_Grind_tryToProveFalse___lam__0(v_cls_2956_, v_____do__lift_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec_ref(v_____do__lift_2957_);
return v_res_2969_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3(void){
_start:
{
lean_object* v_cls_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v_cls_2978_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1));
v___x_2979_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5));
v___x_2980_ = l_Lean_Name_append(v___x_2979_, v_cls_2978_);
return v___x_2980_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5(void){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__4));
v___x_2983_ = l_Lean_stringToMessageData(v___x_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(lean_object* v_as_2984_, size_t v_sz_2985_, size_t v_i_2986_, lean_object* v_b_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v_a_3000_; uint8_t v___x_3004_; 
v___x_3004_ = lean_usize_dec_lt(v_i_2986_, v_sz_2985_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; 
v___x_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3005_, 0, v_b_2987_);
return v___x_3005_;
}
else
{
lean_object* v_snd_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3261_; 
v_snd_3006_ = lean_ctor_get(v_b_2987_, 1);
v_isSharedCheck_3261_ = !lean_is_exclusive(v_b_2987_);
if (v_isSharedCheck_3261_ == 0)
{
lean_object* v_unused_3262_; 
v_unused_3262_ = lean_ctor_get(v_b_2987_, 0);
lean_dec(v_unused_3262_);
v___x_3008_ = v_b_2987_;
v_isShared_3009_ = v_isSharedCheck_3261_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_snd_3006_);
lean_dec(v_b_2987_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3261_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v_array_3010_; lean_object* v_start_3011_; lean_object* v_stop_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v_array_3010_ = lean_ctor_get(v_snd_3006_, 0);
v_start_3011_ = lean_ctor_get(v_snd_3006_, 1);
v_stop_3012_ = lean_ctor_get(v_snd_3006_, 2);
v___x_3013_ = lean_box(0);
v___x_3014_ = lean_nat_dec_lt(v_start_3011_, v_stop_3012_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3016_; 
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 0, v___x_3013_);
v___x_3016_ = v___x_3008_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3013_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_snd_3006_);
v___x_3016_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
lean_object* v___x_3017_; 
v___x_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
return v___x_3017_;
}
}
else
{
lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3257_; 
lean_inc(v_stop_3012_);
lean_inc(v_start_3011_);
lean_inc_ref(v_array_3010_);
v_isSharedCheck_3257_ = !lean_is_exclusive(v_snd_3006_);
if (v_isSharedCheck_3257_ == 0)
{
lean_object* v_unused_3258_; lean_object* v_unused_3259_; lean_object* v_unused_3260_; 
v_unused_3258_ = lean_ctor_get(v_snd_3006_, 2);
lean_dec(v_unused_3258_);
v_unused_3259_ = lean_ctor_get(v_snd_3006_, 1);
lean_dec(v_unused_3259_);
v_unused_3260_ = lean_ctor_get(v_snd_3006_, 0);
lean_dec(v_unused_3260_);
v___x_3020_ = v_snd_3006_;
v_isShared_3021_ = v_isSharedCheck_3257_;
goto v_resetjp_3019_;
}
else
{
lean_dec(v_snd_3006_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3257_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3026_; 
v___x_3022_ = lean_array_fget(v_array_3010_, v_start_3011_);
v___x_3023_ = lean_unsigned_to_nat(1u);
v___x_3024_ = lean_nat_add(v_start_3011_, v___x_3023_);
lean_dec(v_start_3011_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 1, v___x_3024_);
v___x_3026_ = v___x_3020_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_array_3010_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v___x_3024_);
lean_ctor_set(v_reuseFailAlloc_3256_, 2, v_stop_3012_);
v___x_3026_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
uint8_t v___x_3027_; 
v___x_3027_ = lean_unbox(v___x_3022_);
if (v___x_3027_ == 0)
{
lean_object* v___x_3029_; 
lean_dec(v___x_3022_);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 1, v___x_3026_);
lean_ctor_set(v___x_3008_, 0, v___x_3013_);
v___x_3029_ = v___x_3008_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3013_);
lean_ctor_set(v_reuseFailAlloc_3030_, 1, v___x_3026_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
v_a_3000_ = v___x_3029_;
goto v___jp_2999_;
}
}
else
{
lean_object* v_cls_3031_; lean_object* v_a_3032_; lean_object* v_____x_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___x_3070_; 
v_cls_3031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1));
v_a_3032_ = lean_array_uget_borrowed(v_as_2984_, v_i_2986_);
lean_inc(v___y_2997_);
lean_inc_ref(v___y_2996_);
lean_inc(v___y_2995_);
lean_inc_ref(v___y_2994_);
lean_inc(v_a_3032_);
v___x_3070_ = lean_infer_type(v_a_3032_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3247_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3073_ = v___x_3070_;
v_isShared_3074_ = v_isSharedCheck_3247_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_3070_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3247_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3075_; 
v___x_3075_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_a_3071_);
lean_dec(v_a_3071_);
if (lean_obj_tag(v___x_3075_) == 1)
{
lean_object* v_val_3076_; lean_object* v_snd_3077_; lean_object* v_fst_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3241_; 
lean_del_object(v___x_3073_);
v_val_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc(v_val_3076_);
lean_dec_ref_known(v___x_3075_, 1);
v_snd_3077_ = lean_ctor_get(v_val_3076_, 1);
v_fst_3078_ = lean_ctor_get(v_val_3076_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v_val_3076_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3080_ = v_val_3076_;
v_isShared_3081_ = v_isSharedCheck_3241_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_snd_3077_);
lean_inc(v_fst_3078_);
lean_dec(v_val_3076_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3241_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v_fst_3082_; lean_object* v_snd_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3240_; 
v_fst_3082_ = lean_ctor_get(v_snd_3077_, 0);
v_snd_3083_ = lean_ctor_get(v_snd_3077_, 1);
v_isSharedCheck_3240_ = !lean_is_exclusive(v_snd_3077_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3085_ = v_snd_3077_;
v_isShared_3086_ = v_isSharedCheck_3240_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_snd_3083_);
lean_inc(v_fst_3082_);
lean_dec(v_snd_3077_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3240_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
uint8_t v___y_3088_; lean_object* v_lhs_x27_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; uint8_t v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; uint8_t v___y_3179_; lean_object* v___y_3180_; uint8_t v___y_3215_; 
if (lean_obj_tag(v_fst_3078_) == 0)
{
uint8_t v___x_3238_; 
lean_dec(v___x_3022_);
v___x_3238_ = 0;
v___y_3215_ = v___x_3238_;
goto v___jp_3214_;
}
else
{
uint8_t v___x_3239_; 
lean_dec_ref_known(v_fst_3078_, 1);
v___x_3239_ = lean_unbox(v___x_3022_);
lean_dec(v___x_3022_);
v___y_3215_ = v___x_3239_;
goto v___jp_3214_;
}
v___jp_3087_:
{
if (v___y_3088_ == 0)
{
lean_object* v___x_3100_; 
v___x_3100_ = l_Lean_Meta_Grind_proveEq_x3f(v_fst_3082_, v_lhs_x27_3089_, v___y_3088_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_a_3101_);
lean_dec_ref_known(v___x_3100_, 1);
v_____x_3034_ = v_a_3101_;
v___y_3035_ = v___y_3096_;
v___y_3036_ = v___y_3097_;
v___y_3037_ = v___y_3098_;
v___y_3038_ = v___y_3099_;
goto v___jp_3033_;
}
else
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3008_);
v_a_3102_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_3100_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3100_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3105_ == 0)
{
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
else
{
lean_object* v___x_3110_; 
v___x_3110_ = l_Lean_Meta_Grind_proveHEq_x3f(v_fst_3082_, v_lhs_x27_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_a_3111_);
lean_dec_ref_known(v___x_3110_, 1);
v_____x_3034_ = v_a_3111_;
v___y_3035_ = v___y_3096_;
v___y_3036_ = v___y_3097_;
v___y_3037_ = v___y_3098_;
v___y_3038_ = v___y_3099_;
goto v___jp_3033_;
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3008_);
v_a_3112_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3110_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3110_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
}
v___jp_3120_:
{
lean_object* v___x_3134_; 
lean_inc_ref(v___y_3122_);
v___x_3134_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(v___y_3122_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3169_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3137_ = v___x_3134_;
v_isShared_3138_ = v_isSharedCheck_3169_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3134_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3169_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
uint8_t v___x_3139_; 
v___x_3139_ = lean_unbox(v_a_3135_);
lean_dec(v_a_3135_);
if (v___x_3139_ == 0)
{
lean_object* v___x_3140_; lean_object* v___x_3142_; 
lean_dec_ref(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v_fst_3082_);
lean_del_object(v___x_3008_);
v___x_3140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 1, v___x_3026_);
lean_ctor_set(v___x_3085_, 0, v___x_3140_);
v___x_3142_ = v___x_3085_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3140_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v___x_3026_);
v___x_3142_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
lean_object* v___x_3144_; 
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 0, v___x_3142_);
v___x_3144_ = v___x_3137_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3142_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
else
{
lean_object* v___x_3147_; 
lean_del_object(v___x_3137_);
lean_inc_ref(v___y_3123_);
v___x_3147_ = l_Lean_Meta_isDefEqD(v___y_3123_, v___y_3122_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3160_; 
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3150_ = v___x_3147_;
v_isShared_3151_ = v_isSharedCheck_3160_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3147_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3160_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
uint8_t v___x_3152_; 
v___x_3152_ = lean_unbox(v_a_3148_);
lean_dec(v_a_3148_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3153_; lean_object* v___x_3155_; 
lean_dec_ref(v___y_3123_);
lean_dec(v_fst_3082_);
lean_del_object(v___x_3008_);
v___x_3153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 1, v___x_3026_);
lean_ctor_set(v___x_3085_, 0, v___x_3153_);
v___x_3155_ = v___x_3085_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3153_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v___x_3026_);
v___x_3155_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
lean_object* v___x_3157_; 
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 0, v___x_3155_);
v___x_3157_ = v___x_3150_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3155_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
else
{
lean_del_object(v___x_3150_);
lean_del_object(v___x_3085_);
v___y_3088_ = v___y_3121_;
v_lhs_x27_3089_ = v___y_3123_;
v___y_3090_ = v___y_3124_;
v___y_3091_ = v___y_3125_;
v___y_3092_ = v___y_3126_;
v___y_3093_ = v___y_3127_;
v___y_3094_ = v___y_3128_;
v___y_3095_ = v___y_3129_;
v___y_3096_ = v___y_3130_;
v___y_3097_ = v___y_3131_;
v___y_3098_ = v___y_3132_;
v___y_3099_ = v___y_3133_;
goto v___jp_3087_;
}
}
}
else
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
lean_dec_ref(v___y_3123_);
lean_del_object(v___x_3085_);
lean_dec(v_fst_3082_);
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3008_);
v_a_3161_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3147_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3147_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
}
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_dec_ref(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_del_object(v___x_3085_);
lean_dec(v_fst_3082_);
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3008_);
v_a_3170_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3134_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3134_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
v___jp_3178_:
{
lean_object* v___x_3181_; 
lean_inc_ref(v___y_3180_);
lean_inc(v_fst_3082_);
v___x_3181_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_fst_3082_, v___y_3180_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_toCold_3182_; lean_object* v_options_3183_; uint8_t v_hasTrace_3184_; 
v_toCold_3182_ = lean_ctor_get(v___y_2996_, 0);
v_options_3183_ = lean_ctor_get(v_toCold_3182_, 2);
v_hasTrace_3184_ = lean_ctor_get_uint8(v_options_3183_, sizeof(void*)*1);
if (v_hasTrace_3184_ == 0)
{
lean_object* v_a_3185_; 
lean_del_object(v___x_3080_);
v_a_3185_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_a_3185_);
lean_dec_ref_known(v___x_3181_, 1);
v___y_3121_ = v___y_3179_;
v___y_3122_ = v___y_3180_;
v___y_3123_ = v_a_3185_;
v___y_3124_ = v___y_2988_;
v___y_3125_ = v___y_2989_;
v___y_3126_ = v___y_2990_;
v___y_3127_ = v___y_2991_;
v___y_3128_ = v___y_2992_;
v___y_3129_ = v___y_2993_;
v___y_3130_ = v___y_2994_;
v___y_3131_ = v___y_2995_;
v___y_3132_ = v___y_2996_;
v___y_3133_ = v___y_2997_;
goto v___jp_3120_;
}
else
{
lean_object* v_a_3186_; lean_object* v_inheritedTraceOptions_3187_; lean_object* v___x_3188_; uint8_t v___x_3189_; 
v_a_3186_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_a_3186_);
lean_dec_ref_known(v___x_3181_, 1);
v_inheritedTraceOptions_3187_ = lean_ctor_get(v_toCold_3182_, 11);
v___x_3188_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3);
v___x_3189_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3187_, v_options_3183_, v___x_3188_);
if (v___x_3189_ == 0)
{
lean_del_object(v___x_3080_);
v___y_3121_ = v___y_3179_;
v___y_3122_ = v___y_3180_;
v___y_3123_ = v_a_3186_;
v___y_3124_ = v___y_2988_;
v___y_3125_ = v___y_2989_;
v___y_3126_ = v___y_2990_;
v___y_3127_ = v___y_2991_;
v___y_3128_ = v___y_2992_;
v___y_3129_ = v___y_2993_;
v___y_3130_ = v___y_2994_;
v___y_3131_ = v___y_2995_;
v___y_3132_ = v___y_2996_;
v___y_3133_ = v___y_2997_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3193_; 
lean_inc(v_a_3186_);
v___x_3190_ = l_Lean_MessageData_ofExpr(v_a_3186_);
v___x_3191_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5);
if (v_isShared_3081_ == 0)
{
lean_ctor_set_tag(v___x_3080_, 7);
lean_ctor_set(v___x_3080_, 1, v___x_3191_);
lean_ctor_set(v___x_3080_, 0, v___x_3190_);
v___x_3193_ = v___x_3080_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3190_);
lean_ctor_set(v_reuseFailAlloc_3205_, 1, v___x_3191_);
v___x_3193_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
lean_inc_ref(v___y_3180_);
v___x_3194_ = l_Lean_MessageData_ofExpr(v___y_3180_);
v___x_3195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3193_);
lean_ctor_set(v___x_3195_, 1, v___x_3194_);
v___x_3196_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3031_, v___x_3195_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_dec_ref_known(v___x_3196_, 1);
v___y_3121_ = v___y_3179_;
v___y_3122_ = v___y_3180_;
v___y_3123_ = v_a_3186_;
v___y_3124_ = v___y_2988_;
v___y_3125_ = v___y_2989_;
v___y_3126_ = v___y_2990_;
v___y_3127_ = v___y_2991_;
v___y_3128_ = v___y_2992_;
v___y_3129_ = v___y_2993_;
v___y_3130_ = v___y_2994_;
v___y_3131_ = v___y_2995_;
v___y_3132_ = v___y_2996_;
v___y_3133_ = v___y_2997_;
goto v___jp_3120_;
}
else
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
lean_dec(v_a_3186_);
lean_dec_ref(v___y_3180_);
lean_del_object(v___x_3085_);
lean_dec(v_fst_3082_);
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3008_);
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3196_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3196_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec_ref(v___y_3180_);
lean_del_object(v___x_3085_);
lean_dec(v_fst_3082_);
lean_del_object(v___x_3080_);
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3008_);
v_a_3206_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3181_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3181_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
v___jp_3214_:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v_snd_3083_, v___y_2995_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v_a_3217_; uint8_t v___x_3218_; 
v_a_3217_ = lean_ctor_get(v___x_3216_, 0);
lean_inc(v_a_3217_);
lean_dec_ref_known(v___x_3216_, 1);
v___x_3218_ = l_Lean_Expr_hasExprMVar(v_a_3217_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Lean_Meta_Grind_isEqv___redArg(v_fst_3082_, v_a_3217_, v___y_2988_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; uint8_t v___x_3221_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref_known(v___x_3219_, 1);
v___x_3221_ = lean_unbox(v_a_3220_);
lean_dec(v_a_3220_);
if (v___x_3221_ == 0)
{
v___y_3179_ = v___y_3215_;
v___y_3180_ = v_a_3217_;
goto v___jp_3178_;
}
else
{
lean_del_object(v___x_3085_);
lean_del_object(v___x_3080_);
v___y_3088_ = v___y_3215_;
v_lhs_x27_3089_ = v_a_3217_;
v___y_3090_ = v___y_2988_;
v___y_3091_ = v___y_2989_;
v___y_3092_ = v___y_2990_;
v___y_3093_ = v___y_2991_;
v___y_3094_ = v___y_2992_;
v___y_3095_ = v___y_2993_;
v___y_3096_ = v___y_2994_;
v___y_3097_ = v___y_2995_;
v___y_3098_ = v___y_2996_;
v___y_3099_ = v___y_2997_;
goto v___jp_3087_;
}
}
else
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
lean_dec(v_a_3217_);
lean_del_object(v___x_3085_);
lean_dec(v_fst_3082_);
lean_del_object(v___x_3080_);
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3008_);
v_a_3222_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3224_ = v___x_3219_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3219_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3227_; 
if (v_isShared_3225_ == 0)
{
v___x_3227_ = v___x_3224_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3222_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
else
{
v___y_3179_ = v___y_3215_;
v___y_3180_ = v_a_3217_;
goto v___jp_3178_;
}
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_del_object(v___x_3085_);
lean_dec(v_fst_3082_);
lean_del_object(v___x_3080_);
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3008_);
v_a_3230_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_3216_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3216_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3245_; 
lean_dec(v___x_3075_);
lean_dec(v___x_3022_);
lean_del_object(v___x_3008_);
v___x_3242_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
v___x_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3242_);
lean_ctor_set(v___x_3243_, 1, v___x_3026_);
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 0, v___x_3243_);
v___x_3245_ = v___x_3073_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3243_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec_ref(v___x_3026_);
lean_dec(v___x_3022_);
lean_del_object(v___x_3008_);
v_a_3248_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3070_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3070_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
v___jp_3033_:
{
if (lean_obj_tag(v_____x_3034_) == 1)
{
lean_object* v_val_3039_; lean_object* v___x_3040_; 
v_val_3039_ = lean_ctor_get(v_____x_3034_, 0);
lean_inc(v_val_3039_);
lean_dec_ref_known(v_____x_3034_, 1);
lean_inc(v_a_3032_);
v___x_3040_ = l_Lean_Meta_isExprDefEq(v_a_3032_, v_val_3039_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3056_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3043_ = v___x_3040_;
v_isShared_3044_ = v_isSharedCheck_3056_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3040_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3056_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
uint8_t v___x_3045_; 
v___x_3045_ = lean_unbox(v_a_3041_);
lean_dec(v_a_3041_);
if (v___x_3045_ == 0)
{
lean_object* v___x_3046_; lean_object* v___x_3048_; 
v___x_3046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 1, v___x_3026_);
lean_ctor_set(v___x_3008_, 0, v___x_3046_);
v___x_3048_ = v___x_3008_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3046_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v___x_3026_);
v___x_3048_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3050_; 
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v___x_3048_);
v___x_3050_ = v___x_3043_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
else
{
lean_object* v___x_3054_; 
lean_del_object(v___x_3043_);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 1, v___x_3026_);
lean_ctor_set(v___x_3008_, 0, v___x_3013_);
v___x_3054_ = v___x_3008_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3013_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v___x_3026_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
v_a_3000_ = v___x_3054_;
goto v___jp_2999_;
}
}
}
}
else
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3008_);
v_a_3057_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___x_3040_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3040_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3057_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
}
else
{
lean_object* v___x_3065_; lean_object* v___x_3067_; 
lean_dec(v_____x_3034_);
v___x_3065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 1, v___x_3026_);
lean_ctor_set(v___x_3008_, 0, v___x_3065_);
v___x_3067_ = v___x_3008_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3065_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v___x_3026_);
v___x_3067_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
lean_object* v___x_3068_; 
v___x_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
return v___x_3068_;
}
}
}
}
}
}
}
}
}
v___jp_2999_:
{
size_t v___x_3001_; size_t v___x_3002_; 
v___x_3001_ = ((size_t)1ULL);
v___x_3002_ = lean_usize_add(v_i_2986_, v___x_3001_);
v_i_2986_ = v___x_3002_;
v_b_2987_ = v_a_3000_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___boxed(lean_object* v_as_3263_, lean_object* v_sz_3264_, lean_object* v_i_3265_, lean_object* v_b_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
size_t v_sz_boxed_3278_; size_t v_i_boxed_3279_; lean_object* v_res_3280_; 
v_sz_boxed_3278_ = lean_unbox_usize(v_sz_3264_);
lean_dec(v_sz_3264_);
v_i_boxed_3279_ = lean_unbox_usize(v_i_3265_);
lean_dec(v_i_3265_);
v_res_3280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(v_as_3263_, v_sz_boxed_3278_, v_i_boxed_3279_, v_b_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec_ref(v_as_3263_);
return v_res_3280_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3282_ = ((lean_object*)(l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__0));
v___x_3283_ = l_Lean_stringToMessageData(v___x_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1(lean_object* v_arg_3284_, uint8_t v___x_3285_, lean_object* v_e_3286_, lean_object* v___f_3287_, lean_object* v_cls_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v___x_3300_; 
lean_inc_ref(v_arg_3284_);
v___x_3300_ = l_Lean_Meta_forallMetaTelescope(v_arg_3284_, v___x_3285_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_a_3301_; lean_object* v_fst_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3420_; 
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc(v_a_3301_);
lean_dec_ref_known(v___x_3300_, 1);
v_fst_3302_ = lean_ctor_get(v_a_3301_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v_a_3301_);
if (v_isSharedCheck_3420_ == 0)
{
lean_object* v_unused_3421_; 
v_unused_3421_ = lean_ctor_get(v_a_3301_, 1);
lean_dec(v_unused_3421_);
v___x_3304_ = v_a_3301_;
v_isShared_3305_ = v_isSharedCheck_3420_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_fst_3302_);
lean_dec(v_a_3301_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3420_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3312_; 
v___x_3306_ = l_Lean_Meta_mkGenDiseqMask(v_arg_3284_);
lean_dec_ref(v_arg_3284_);
v___x_3307_ = lean_unsigned_to_nat(0u);
v___x_3308_ = lean_array_get_size(v___x_3306_);
v___x_3309_ = l_Array_toSubarray___redArg(v___x_3306_, v___x_3307_, v___x_3308_);
v___x_3310_ = lean_box(0);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 1, v___x_3309_);
lean_ctor_set(v___x_3304_, 0, v___x_3310_);
v___x_3312_ = v___x_3304_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3310_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v___x_3309_);
v___x_3312_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
size_t v_sz_3313_; size_t v___x_3314_; lean_object* v___x_3315_; 
v_sz_3313_ = lean_array_size(v_fst_3302_);
v___x_3314_ = ((size_t)0ULL);
v___x_3315_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(v_fst_3302_, v_sz_3313_, v___x_3314_, v___x_3312_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3410_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3318_ = v___x_3315_;
v_isShared_3319_ = v_isSharedCheck_3410_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3315_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3410_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v_fst_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3408_; 
v_fst_3320_ = lean_ctor_get(v_a_3316_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v_a_3316_);
if (v_isSharedCheck_3408_ == 0)
{
lean_object* v_unused_3409_; 
v_unused_3409_ = lean_ctor_get(v_a_3316_, 1);
lean_dec(v_unused_3409_);
v___x_3322_ = v_a_3316_;
v_isShared_3323_ = v_isSharedCheck_3408_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_fst_3320_);
lean_dec(v_a_3316_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3408_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
if (lean_obj_tag(v_fst_3320_) == 0)
{
lean_object* v___x_3324_; 
lean_del_object(v___x_3318_);
lean_inc_ref(v_e_3286_);
v___x_3324_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_3286_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3395_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3325_);
lean_dec_ref_known(v___x_3324_, 1);
v___x_3326_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3286_, v_a_3325_);
v___x_3327_ = l_Lean_mkAppN(v___x_3326_, v_fst_3302_);
lean_dec(v_fst_3302_);
v___x_3328_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v___x_3327_, v___y_3296_);
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3331_ = v___x_3328_;
v_isShared_3332_ = v_isSharedCheck_3395_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3328_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3395_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3338_; 
lean_inc(v_a_3329_);
v___x_3338_ = l_Lean_Meta_hasAssignableMVar(v_a_3329_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3386_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3341_ = v___x_3338_;
v_isShared_3342_ = v_isSharedCheck_3386_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3338_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3386_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
uint8_t v___x_3343_; 
v___x_3343_ = lean_unbox(v_a_3339_);
lean_dec(v_a_3339_);
if (v___x_3343_ == 0)
{
lean_object* v_toCold_3344_; lean_object* v_inheritedTraceOptions_3345_; lean_object* v___x_3346_; 
lean_del_object(v___x_3341_);
v_toCold_3344_ = lean_ctor_get(v___y_3297_, 0);
v_inheritedTraceOptions_3345_ = lean_ctor_get(v_toCold_3344_, 11);
lean_inc(v___y_3298_);
lean_inc_ref(v___y_3297_);
lean_inc(v___y_3296_);
lean_inc_ref(v___y_3295_);
lean_inc(v___y_3294_);
lean_inc_ref(v___y_3293_);
lean_inc(v___y_3292_);
lean_inc_ref(v___y_3291_);
lean_inc(v___y_3290_);
lean_inc(v___y_3289_);
lean_inc_ref(v_inheritedTraceOptions_3345_);
v___x_3346_ = lean_apply_12(v___f_3287_, v_inheritedTraceOptions_3345_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, lean_box(0));
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; uint8_t v___x_3348_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3347_);
lean_dec_ref_known(v___x_3346_, 1);
v___x_3348_ = lean_unbox(v_a_3347_);
lean_dec(v_a_3347_);
if (v___x_3348_ == 0)
{
lean_del_object(v___x_3322_);
lean_dec(v_cls_3288_);
goto v___jp_3333_;
}
else
{
lean_object* v___x_3349_; 
lean_inc(v___y_3298_);
lean_inc_ref(v___y_3297_);
lean_inc(v___y_3296_);
lean_inc_ref(v___y_3295_);
lean_inc(v_a_3329_);
v___x_3349_ = lean_infer_type(v_a_3329_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3354_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3350_);
lean_dec_ref_known(v___x_3349_, 1);
lean_inc(v_a_3329_);
v___x_3351_ = l_Lean_MessageData_ofExpr(v_a_3329_);
v___x_3352_ = lean_obj_once(&l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1, &l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1_once, _init_l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1);
if (v_isShared_3323_ == 0)
{
lean_ctor_set_tag(v___x_3322_, 7);
lean_ctor_set(v___x_3322_, 1, v___x_3352_);
lean_ctor_set(v___x_3322_, 0, v___x_3351_);
v___x_3354_ = v___x_3322_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3351_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v___x_3352_);
v___x_3354_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3355_ = l_Lean_MessageData_ofExpr(v_a_3350_);
v___x_3356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3354_);
lean_ctor_set(v___x_3356_, 1, v___x_3355_);
v___x_3357_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3288_, v___x_3356_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_dec_ref_known(v___x_3357_, 1);
goto v___jp_3333_;
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
lean_del_object(v___x_3331_);
lean_dec(v_a_3329_);
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3357_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3357_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
}
else
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
lean_del_object(v___x_3331_);
lean_dec(v_a_3329_);
lean_del_object(v___x_3322_);
lean_dec(v_cls_3288_);
v_a_3367_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3349_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3349_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_del_object(v___x_3331_);
lean_dec(v_a_3329_);
lean_del_object(v___x_3322_);
lean_dec(v_cls_3288_);
v_a_3375_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3346_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3346_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
else
{
lean_object* v___x_3384_; 
lean_del_object(v___x_3331_);
lean_dec(v_a_3329_);
lean_del_object(v___x_3322_);
lean_dec(v_cls_3288_);
lean_dec_ref(v___f_3287_);
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 0, v___x_3310_);
v___x_3384_ = v___x_3341_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3310_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_del_object(v___x_3331_);
lean_dec(v_a_3329_);
lean_del_object(v___x_3322_);
lean_dec(v_cls_3288_);
lean_dec_ref(v___f_3287_);
v_a_3387_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3338_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3338_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
v___jp_3333_:
{
lean_object* v___x_3334_; lean_object* v___x_3336_; 
v___x_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3334_, 0, v_a_3329_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v___x_3334_);
v___x_3336_ = v___x_3331_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3334_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_del_object(v___x_3322_);
lean_dec(v_fst_3302_);
lean_dec(v_cls_3288_);
lean_dec_ref(v___f_3287_);
lean_dec_ref(v_e_3286_);
v_a_3396_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3324_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3324_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
else
{
lean_object* v_val_3404_; lean_object* v___x_3406_; 
lean_del_object(v___x_3322_);
lean_dec(v_fst_3302_);
lean_dec(v_cls_3288_);
lean_dec_ref(v___f_3287_);
lean_dec_ref(v_e_3286_);
v_val_3404_ = lean_ctor_get(v_fst_3320_, 0);
lean_inc(v_val_3404_);
lean_dec_ref_known(v_fst_3320_, 1);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 0, v_val_3404_);
v___x_3406_ = v___x_3318_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_val_3404_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec(v_fst_3302_);
lean_dec(v_cls_3288_);
lean_dec_ref(v___f_3287_);
lean_dec_ref(v_e_3286_);
v_a_3411_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3315_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3315_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
}
}
else
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3429_; 
lean_dec(v_cls_3288_);
lean_dec_ref(v___f_3287_);
lean_dec_ref(v_e_3286_);
lean_dec_ref(v_arg_3284_);
v_a_3422_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___x_3300_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3300_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3427_; 
if (v_isShared_3425_ == 0)
{
v___x_3427_ = v___x_3424_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3422_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1___boxed(lean_object* v_arg_3430_, lean_object* v___x_3431_, lean_object* v_e_3432_, lean_object* v___f_3433_, lean_object* v_cls_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
uint8_t v___x_77358__boxed_3446_; lean_object* v_res_3447_; 
v___x_77358__boxed_3446_ = lean_unbox(v___x_3431_);
v_res_3447_ = l_Lean_Meta_Grind_tryToProveFalse___lam__1(v_arg_3430_, v___x_77358__boxed_3446_, v_e_3432_, v___f_3433_, v_cls_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec(v___y_3435_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse(lean_object* v_e_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_){
_start:
{
lean_object* v_toCold_3465_; lean_object* v_inheritedTraceOptions_3466_; lean_object* v_cls_3467_; lean_object* v___f_3468_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___x_3520_; lean_object* v_a_3521_; uint8_t v___x_3522_; 
v_toCold_3465_ = lean_ctor_get(v_a_3459_, 0);
v_inheritedTraceOptions_3466_ = lean_ctor_get(v_toCold_3465_, 11);
v_cls_3467_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1));
v___f_3468_ = ((lean_object*)(l_Lean_Meta_Grind_tryToProveFalse___closed__0));
v___x_3520_ = l_Lean_Meta_Grind_tryToProveFalse___lam__0(v_cls_3467_, v_inheritedTraceOptions_3466_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref(v___x_3520_);
v___x_3522_ = lean_unbox(v_a_3521_);
lean_dec(v_a_3521_);
if (v___x_3522_ == 0)
{
v___y_3470_ = v_a_3451_;
v___y_3471_ = v_a_3452_;
v___y_3472_ = v_a_3453_;
v___y_3473_ = v_a_3454_;
v___y_3474_ = v_a_3455_;
v___y_3475_ = v_a_3456_;
v___y_3476_ = v_a_3457_;
v___y_3477_ = v_a_3458_;
v___y_3478_ = v_a_3459_;
v___y_3479_ = v_a_3460_;
goto v___jp_3469_;
}
else
{
lean_object* v___x_3523_; 
v___x_3523_ = l_Lean_Meta_Grind_updateLastTag(v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
lean_dec_ref_known(v___x_3523_, 1);
lean_inc_ref(v_e_3450_);
v___x_3524_ = l_Lean_MessageData_ofExpr(v_e_3450_);
v___x_3525_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3467_, v___x_3524_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_dec_ref_known(v___x_3525_, 1);
v___y_3470_ = v_a_3451_;
v___y_3471_ = v_a_3452_;
v___y_3472_ = v_a_3453_;
v___y_3473_ = v_a_3454_;
v___y_3474_ = v_a_3455_;
v___y_3475_ = v_a_3456_;
v___y_3476_ = v_a_3457_;
v___y_3477_ = v_a_3458_;
v___y_3478_ = v_a_3459_;
v___y_3479_ = v_a_3460_;
goto v___jp_3469_;
}
else
{
lean_dec_ref(v_e_3450_);
return v___x_3525_;
}
}
else
{
lean_dec_ref(v_e_3450_);
return v___x_3523_;
}
}
v___jp_3462_:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3463_ = lean_box(0);
v___x_3464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
return v___x_3464_;
}
v___jp_3469_:
{
lean_object* v___x_3480_; 
lean_inc_ref(v_e_3450_);
v___x_3480_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3450_, v___y_3477_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3482_; uint8_t v___x_3483_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_a_3481_);
lean_dec_ref_known(v___x_3480_, 1);
v___x_3482_ = l_Lean_Expr_cleanupAnnotations(v_a_3481_);
lean_dec(v_a_3481_);
v___x_3483_ = l_Lean_Expr_isApp(v___x_3482_);
if (v___x_3483_ == 0)
{
lean_dec_ref(v___x_3482_);
lean_dec_ref(v_e_3450_);
goto v___jp_3462_;
}
else
{
lean_object* v___x_3484_; lean_object* v___x_3485_; uint8_t v___x_3486_; 
v___x_3484_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3482_);
v___x_3485_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3486_ = l_Lean_Expr_isConstOf(v___x_3484_, v___x_3485_);
lean_dec_ref(v___x_3484_);
if (v___x_3486_ == 0)
{
lean_dec_ref(v___x_3482_);
lean_dec_ref(v_e_3450_);
goto v___jp_3462_;
}
else
{
lean_object* v_arg_3487_; uint8_t v___x_3488_; lean_object* v___x_3489_; lean_object* v___f_3490_; uint8_t v___x_3491_; lean_object* v___x_3492_; 
v_arg_3487_ = lean_ctor_get(v___x_3482_, 1);
lean_inc_ref(v_arg_3487_);
lean_dec_ref(v___x_3482_);
v___x_3488_ = 0;
v___x_3489_ = lean_box(v___x_3488_);
v___f_3490_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_tryToProveFalse___lam__1___boxed), 16, 5);
lean_closure_set(v___f_3490_, 0, v_arg_3487_);
lean_closure_set(v___f_3490_, 1, v___x_3489_);
lean_closure_set(v___f_3490_, 2, v_e_3450_);
lean_closure_set(v___f_3490_, 3, v___f_3468_);
lean_closure_set(v___f_3490_, 4, v_cls_3467_);
v___x_3491_ = 0;
v___x_3492_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(v___f_3490_, v___x_3491_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3503_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3495_ = v___x_3492_;
v_isShared_3496_ = v_isSharedCheck_3503_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3492_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3503_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
if (lean_obj_tag(v_a_3493_) == 1)
{
lean_object* v_val_3497_; lean_object* v___x_3498_; 
lean_del_object(v___x_3495_);
v_val_3497_ = lean_ctor_get(v_a_3493_, 0);
lean_inc(v_val_3497_);
lean_dec_ref_known(v_a_3493_, 1);
v___x_3498_ = l_Lean_Meta_Grind_closeGoal(v_val_3497_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
return v___x_3498_;
}
else
{
lean_object* v___x_3499_; lean_object* v___x_3501_; 
lean_dec(v_a_3493_);
v___x_3499_ = lean_box(0);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 0, v___x_3499_);
v___x_3501_ = v___x_3495_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3499_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
v_a_3504_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3492_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3492_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
}
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
lean_dec_ref(v_e_3450_);
v_a_3512_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3480_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3480_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___boxed(lean_object* v_e_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_);
lean_dec(v_a_3536_);
lean_dec_ref(v_a_3535_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec_ref(v_a_3529_);
lean_dec(v_a_3528_);
lean_dec(v_a_3527_);
return v_res_3538_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1(void){
_start:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3540_ = ((lean_object*)(l_Lean_Meta_Grind_propagateMatchCondUp___closed__0));
v___x_3541_ = l_Lean_stringToMessageData(v___x_3540_);
return v___x_3541_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3(void){
_start:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = ((lean_object*)(l_Lean_Meta_Grind_propagateMatchCondUp___closed__2));
v___x_3544_ = l_Lean_stringToMessageData(v___x_3543_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp(lean_object* v_e_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_){
_start:
{
lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v_toCold_3571_; lean_object* v_options_3572_; lean_object* v_inheritedTraceOptions_3573_; uint8_t v_hasTrace_3574_; lean_object* v_cls_3575_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; 
v_toCold_3571_ = lean_ctor_get(v_a_3554_, 0);
v_options_3572_ = lean_ctor_get(v_toCold_3571_, 2);
v_inheritedTraceOptions_3573_ = lean_ctor_get(v_toCold_3571_, 11);
v_hasTrace_3574_ = lean_ctor_get_uint8(v_options_3572_, sizeof(void*)*1);
v_cls_3575_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
if (v_hasTrace_3574_ == 0)
{
v___y_3577_ = v_a_3546_;
v___y_3578_ = v_a_3547_;
v___y_3579_ = v_a_3548_;
v___y_3580_ = v_a_3549_;
v___y_3581_ = v_a_3550_;
v___y_3582_ = v_a_3551_;
v___y_3583_ = v_a_3552_;
v___y_3584_ = v_a_3553_;
v___y_3585_ = v_a_3554_;
v___y_3586_ = v_a_3555_;
goto v___jp_3576_;
}
else
{
lean_object* v___x_3683_; uint8_t v___x_3684_; 
v___x_3683_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_3684_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3573_, v_options_3572_, v___x_3683_);
if (v___x_3684_ == 0)
{
v___y_3577_ = v_a_3546_;
v___y_3578_ = v_a_3547_;
v___y_3579_ = v_a_3548_;
v___y_3580_ = v_a_3549_;
v___y_3581_ = v_a_3550_;
v___y_3582_ = v_a_3551_;
v___y_3583_ = v_a_3552_;
v___y_3584_ = v_a_3553_;
v___y_3585_ = v_a_3554_;
v___y_3586_ = v_a_3555_;
goto v___jp_3576_;
}
else
{
lean_object* v___x_3685_; 
v___x_3685_ = l_Lean_Meta_Grind_updateLastTag(v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
lean_dec_ref_known(v___x_3685_, 1);
v___x_3686_ = lean_obj_once(&l_Lean_Meta_Grind_propagateMatchCondUp___closed__3, &l_Lean_Meta_Grind_propagateMatchCondUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3);
lean_inc_ref(v_e_3545_);
v___x_3687_ = l_Lean_indentExpr(v_e_3545_);
v___x_3688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3686_);
lean_ctor_set(v___x_3688_, 1, v___x_3687_);
v___x_3689_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3575_, v___x_3688_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_);
if (lean_obj_tag(v___x_3689_) == 0)
{
lean_dec_ref_known(v___x_3689_, 1);
v___y_3577_ = v_a_3546_;
v___y_3578_ = v_a_3547_;
v___y_3579_ = v_a_3548_;
v___y_3580_ = v_a_3549_;
v___y_3581_ = v_a_3550_;
v___y_3582_ = v_a_3551_;
v___y_3583_ = v_a_3552_;
v___y_3584_ = v_a_3553_;
v___y_3585_ = v_a_3554_;
v___y_3586_ = v_a_3555_;
goto v___jp_3576_;
}
else
{
lean_dec_ref(v_e_3545_);
return v___x_3689_;
}
}
else
{
lean_dec_ref(v_e_3545_);
return v___x_3685_;
}
}
}
v___jp_3557_:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3558_ = lean_box(0);
v___x_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3558_);
return v___x_3559_;
}
v___jp_3560_:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
lean_inc_ref(v_e_3545_);
v___x_3569_ = l_Lean_Meta_mkEqTrueCore(v_e_3545_, v___y_3561_);
v___x_3570_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_3545_, v___x_3569_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
return v___x_3570_;
}
v___jp_3576_:
{
lean_object* v___x_3587_; 
lean_inc_ref(v_e_3545_);
v___x_3587_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3545_, v___y_3577_, v___y_3581_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v_a_3588_; uint8_t v___x_3589_; 
v_a_3588_ = lean_ctor_get(v___x_3587_, 0);
lean_inc(v_a_3588_);
lean_dec_ref_known(v___x_3587_, 1);
v___x_3589_ = lean_unbox(v_a_3588_);
lean_dec(v_a_3588_);
if (v___x_3589_ == 0)
{
lean_object* v___x_3590_; 
lean_inc_ref(v_e_3545_);
v___x_3590_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3545_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3646_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3593_ = v___x_3590_;
v_isShared_3594_ = v_isSharedCheck_3646_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3590_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3646_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
uint8_t v___x_3595_; 
v___x_3595_ = lean_unbox(v_a_3591_);
lean_dec(v_a_3591_);
if (v___x_3595_ == 0)
{
lean_object* v___x_3596_; lean_object* v___x_3598_; 
lean_dec_ref(v_e_3545_);
v___x_3596_ = lean_box(0);
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 0, v___x_3596_);
v___x_3598_ = v___x_3593_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3596_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
else
{
lean_object* v___x_3600_; 
lean_del_object(v___x_3593_);
lean_inc_ref(v_e_3545_);
v___x_3600_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_3545_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref_known(v___x_3600_, 1);
if (lean_obj_tag(v_a_3601_) == 1)
{
lean_object* v_toCold_3602_; lean_object* v_options_3603_; uint8_t v_hasTrace_3604_; 
v_toCold_3602_ = lean_ctor_get(v___y_3585_, 0);
v_options_3603_ = lean_ctor_get(v_toCold_3602_, 2);
v_hasTrace_3604_ = lean_ctor_get_uint8(v_options_3603_, sizeof(void*)*1);
if (v_hasTrace_3604_ == 0)
{
lean_object* v_val_3605_; 
v_val_3605_ = lean_ctor_get(v_a_3601_, 0);
lean_inc(v_val_3605_);
lean_dec_ref_known(v_a_3601_, 1);
v___y_3561_ = v_val_3605_;
v___y_3562_ = v___y_3577_;
v___y_3563_ = v___y_3579_;
v___y_3564_ = v___y_3581_;
v___y_3565_ = v___y_3583_;
v___y_3566_ = v___y_3584_;
v___y_3567_ = v___y_3585_;
v___y_3568_ = v___y_3586_;
goto v___jp_3560_;
}
else
{
lean_object* v_val_3606_; lean_object* v_inheritedTraceOptions_3607_; lean_object* v___x_3608_; uint8_t v___x_3609_; 
v_val_3606_ = lean_ctor_get(v_a_3601_, 0);
lean_inc(v_val_3606_);
lean_dec_ref_known(v_a_3601_, 1);
v_inheritedTraceOptions_3607_ = lean_ctor_get(v_toCold_3602_, 11);
v___x_3608_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_3609_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3607_, v_options_3603_, v___x_3608_);
if (v___x_3609_ == 0)
{
v___y_3561_ = v_val_3606_;
v___y_3562_ = v___y_3577_;
v___y_3563_ = v___y_3579_;
v___y_3564_ = v___y_3581_;
v___y_3565_ = v___y_3583_;
v___y_3566_ = v___y_3584_;
v___y_3567_ = v___y_3585_;
v___y_3568_ = v___y_3586_;
goto v___jp_3560_;
}
else
{
lean_object* v___x_3610_; 
v___x_3610_ = l_Lean_Meta_Grind_updateLastTag(v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v___x_3611_; 
lean_dec_ref_known(v___x_3610_, 1);
lean_inc(v___y_3586_);
lean_inc_ref(v___y_3585_);
lean_inc(v___y_3584_);
lean_inc_ref(v___y_3583_);
lean_inc(v_val_3606_);
v___x_3611_ = lean_infer_type(v_val_3606_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_a_3612_);
lean_dec_ref_known(v___x_3611_, 1);
v___x_3613_ = l_Lean_MessageData_ofExpr(v_a_3612_);
v___x_3614_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3575_, v___x_3613_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_dec_ref_known(v___x_3614_, 1);
v___y_3561_ = v_val_3606_;
v___y_3562_ = v___y_3577_;
v___y_3563_ = v___y_3579_;
v___y_3564_ = v___y_3581_;
v___y_3565_ = v___y_3583_;
v___y_3566_ = v___y_3584_;
v___y_3567_ = v___y_3585_;
v___y_3568_ = v___y_3586_;
goto v___jp_3560_;
}
else
{
lean_dec(v_val_3606_);
lean_dec_ref(v_e_3545_);
return v___x_3614_;
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_dec(v_val_3606_);
lean_dec_ref(v_e_3545_);
v_a_3615_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3611_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3611_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
else
{
lean_dec(v_val_3606_);
lean_dec_ref(v_e_3545_);
return v___x_3610_;
}
}
}
}
else
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
lean_dec(v_a_3601_);
v___x_3623_ = lean_obj_once(&l_Lean_Meta_Grind_propagateMatchCondUp___closed__1, &l_Lean_Meta_Grind_propagateMatchCondUp___closed__1_once, _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1);
v___x_3624_ = l_Lean_indentExpr(v_e_3545_);
v___x_3625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3623_);
lean_ctor_set(v___x_3625_, 1, v___x_3624_);
v___x_3626_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_3581_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; uint8_t v_verbose_3628_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_a_3627_);
lean_dec_ref_known(v___x_3626_, 1);
v_verbose_3628_ = lean_ctor_get_uint8(v_a_3627_, 0);
lean_dec(v_a_3627_);
if (v_verbose_3628_ == 0)
{
lean_dec_ref_known(v___x_3625_, 2);
goto v___jp_3557_;
}
else
{
lean_object* v___x_3629_; 
v___x_3629_ = l_Lean_Meta_Sym_reportIssue(v___x_3625_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_dec_ref_known(v___x_3629_, 1);
goto v___jp_3557_;
}
else
{
return v___x_3629_;
}
}
}
else
{
lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3637_; 
lean_dec_ref_known(v___x_3625_, 2);
v_a_3630_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3632_ = v___x_3626_;
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_dec(v___x_3626_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3635_; 
if (v_isShared_3633_ == 0)
{
v___x_3635_ = v___x_3632_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3630_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
}
else
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
lean_dec_ref(v_e_3545_);
v_a_3638_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3640_ = v___x_3600_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3600_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3638_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
}
}
else
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3654_; 
lean_dec_ref(v_e_3545_);
v_a_3647_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3649_ = v___x_3590_;
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v___x_3590_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3652_; 
if (v_isShared_3650_ == 0)
{
v___x_3652_ = v___x_3649_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_a_3647_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
}
}
else
{
lean_object* v___x_3655_; 
lean_inc_ref(v_e_3545_);
v___x_3655_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3545_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3666_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3658_ = v___x_3655_;
v_isShared_3659_ = v_isSharedCheck_3666_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3655_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3666_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
uint8_t v___x_3660_; 
v___x_3660_ = lean_unbox(v_a_3656_);
lean_dec(v_a_3656_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; 
lean_del_object(v___x_3658_);
v___x_3661_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3545_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
return v___x_3661_;
}
else
{
lean_object* v___x_3662_; lean_object* v___x_3664_; 
lean_dec_ref(v_e_3545_);
v___x_3662_ = lean_box(0);
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 0, v___x_3662_);
v___x_3664_ = v___x_3658_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3662_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
else
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
lean_dec_ref(v_e_3545_);
v_a_3667_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3669_ = v___x_3655_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3655_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3670_ == 0)
{
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3667_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
lean_dec_ref(v_e_3545_);
v_a_3675_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3587_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3587_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___boxed(lean_object* v_e_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l_Lean_Meta_Grind_propagateMatchCondUp(v_e_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_);
lean_dec(v_a_3700_);
lean_dec_ref(v_a_3699_);
lean_dec(v_a_3698_);
lean_dec_ref(v_a_3697_);
lean_dec(v_a_3696_);
lean_dec_ref(v_a_3695_);
lean_dec(v_a_3694_);
lean_dec_ref(v_a_3693_);
lean_dec(v_a_3692_);
lean_dec(v_a_3691_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3704_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3705_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondUp___boxed), 12, 0);
v___x_3706_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3704_, v___x_3705_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_9____boxed(lean_object* v_a_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_9_();
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown(lean_object* v_e_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_){
_start:
{
lean_object* v___x_3721_; 
lean_inc_ref(v_e_3709_);
v___x_3721_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3709_, v_a_3710_, v_a_3714_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3751_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3724_ = v___x_3721_;
v_isShared_3725_ = v_isSharedCheck_3751_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3721_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3751_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
uint8_t v___x_3726_; 
v___x_3726_ = lean_unbox(v_a_3722_);
lean_dec(v_a_3722_);
if (v___x_3726_ == 0)
{
lean_object* v___x_3727_; lean_object* v___x_3729_; 
lean_dec_ref(v_e_3709_);
v___x_3727_ = lean_box(0);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 0, v___x_3727_);
v___x_3729_ = v___x_3724_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3727_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
else
{
lean_object* v___x_3731_; 
lean_del_object(v___x_3724_);
lean_inc_ref(v_e_3709_);
v___x_3731_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3742_; 
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3734_ = v___x_3731_;
v_isShared_3735_ = v_isSharedCheck_3742_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3731_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3742_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
uint8_t v___x_3736_; 
v___x_3736_ = lean_unbox(v_a_3732_);
lean_dec(v_a_3732_);
if (v___x_3736_ == 0)
{
lean_object* v___x_3737_; 
lean_del_object(v___x_3734_);
v___x_3737_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_);
return v___x_3737_;
}
else
{
lean_object* v___x_3738_; lean_object* v___x_3740_; 
lean_dec_ref(v_e_3709_);
v___x_3738_ = lean_box(0);
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 0, v___x_3738_);
v___x_3740_ = v___x_3734_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3738_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_dec_ref(v_e_3709_);
v_a_3743_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3731_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3731_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
}
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
lean_dec_ref(v_e_3709_);
v_a_3752_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3721_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3721_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___boxed(lean_object* v_e_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_Lean_Meta_Grind_propagateMatchCondDown(v_e_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_);
lean_dec(v_a_3770_);
lean_dec_ref(v_a_3769_);
lean_dec(v_a_3768_);
lean_dec_ref(v_a_3767_);
lean_dec(v_a_3766_);
lean_dec_ref(v_a_3765_);
lean_dec(v_a_3764_);
lean_dec_ref(v_a_3763_);
lean_dec(v_a_3762_);
lean_dec(v_a_3761_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
v___x_3774_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3775_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondDown___boxed), 12, 0);
v___x_3776_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3774_, v___x_3775_);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_9____boxed(lean_object* v_a_3777_){
_start:
{
lean_object* v_res_3778_; 
v_res_3778_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_9_();
return v_res_3778_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ProveEq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MatchCond(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Contradiction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_MatchCond(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_ProveEq(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_MatchCond(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Contradiction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_MatchCond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_MatchCond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_MatchCond(builtin);
}
#ifdef __cplusplus
}
#endif
