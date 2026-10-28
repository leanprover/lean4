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
uint8_t v___x_23472__boxed_1106_; lean_object* v_res_1107_; 
v___x_23472__boxed_1106_ = lean_unbox(v___x_1092_);
v_res_1107_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_23472__boxed_1106_, v_snd_1093_, v_____r_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
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
uint8_t v___x_23687__boxed_1335_; lean_object* v_res_1336_; 
v___x_23687__boxed_1335_ = lean_unbox(v___x_1321_);
v_res_1336_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_23687__boxed_1335_, v_e_1322_, v_a_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
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
uint8_t v___x_24048__boxed_1467_; lean_object* v_res_1468_; 
v___x_24048__boxed_1467_ = lean_unbox(v___x_1452_);
v_res_1468_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(v___x_24048__boxed_1467_, v_e_1453_, v_inst_1454_, v_a_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
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
uint8_t v_a_80064__boxed_1599_; lean_object* v_res_1600_; 
v_a_80064__boxed_1599_ = lean_unbox(v_a_1584_);
v_res_1600_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(v_e_1581_, v_name_1582_, v_name_1583_, v_a_80064__boxed_1599_, v_a_1585_, v_xs_1586_, v_x_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
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
uint8_t v___y_1627_; lean_object* v___y_1628_; uint8_t v___y_1629_; uint8_t v___y_1630_; lean_object* v___y_1631_; lean_object* v_h_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; uint8_t v___y_1828_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v_toCold_2002_; lean_object* v_options_2003_; uint8_t v_hasTrace_2004_; 
v_toCold_2002_ = lean_ctor_get(v_a_1620_, 0);
v_options_2003_ = lean_ctor_get(v_toCold_2002_, 2);
v_hasTrace_2004_ = lean_ctor_get_uint8(v_options_2003_, sizeof(void*)*1);
if (v_hasTrace_2004_ == 0)
{
v___y_1905_ = v_a_1612_;
v___y_1906_ = v_a_1613_;
v___y_1907_ = v_a_1614_;
v___y_1908_ = v_a_1615_;
v___y_1909_ = v_a_1616_;
v___y_1910_ = v_a_1617_;
v___y_1911_ = v_a_1618_;
v___y_1912_ = v_a_1619_;
v___y_1913_ = v_a_1620_;
v___y_1914_ = v_a_1621_;
goto v___jp_1904_;
}
else
{
lean_object* v_inheritedTraceOptions_2005_; lean_object* v_cls_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v_inheritedTraceOptions_2005_ = lean_ctor_get(v_toCold_2002_, 11);
v_cls_2006_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_2007_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_2008_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2005_, v_options_2003_, v___x_2007_);
if (v___x_2008_ == 0)
{
v___y_1905_ = v_a_1612_;
v___y_1906_ = v_a_1613_;
v___y_1907_ = v_a_1614_;
v___y_1908_ = v_a_1615_;
v___y_1909_ = v_a_1616_;
v___y_1910_ = v_a_1617_;
v___y_1911_ = v_a_1618_;
v___y_1912_ = v_a_1619_;
v___y_1913_ = v_a_1620_;
v___y_1914_ = v_a_1621_;
goto v___jp_1904_;
}
else
{
lean_object* v___x_2009_; 
v___x_2009_ = l_Lean_Meta_Grind_updateLastTag(v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v___x_2010_; 
lean_dec_ref_known(v___x_2009_, 1);
lean_inc(v_a_1621_);
lean_inc_ref(v_a_1620_);
lean_inc(v_a_1619_);
lean_inc_ref(v_a_1618_);
lean_inc_ref(v_h_1611_);
v___x_2010_ = lean_infer_type(v_h_1611_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
v___x_2012_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5);
v___x_2013_ = l_Lean_MessageData_ofExpr(v_a_2011_);
v___x_2014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2012_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
v___x_2015_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_2006_, v___x_2014_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_dec_ref_known(v___x_2015_, 1);
v___y_1905_ = v_a_1612_;
v___y_1906_ = v_a_1613_;
v___y_1907_ = v_a_1614_;
v___y_1908_ = v_a_1615_;
v___y_1909_ = v_a_1616_;
v___y_1910_ = v_a_1617_;
v___y_1911_ = v_a_1618_;
v___y_1912_ = v_a_1619_;
v___y_1913_ = v_a_1620_;
v___y_1914_ = v_a_1621_;
goto v___jp_1904_;
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v_a_2024_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_2010_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2010_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v_a_2032_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2009_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2009_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
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
if (v___y_1630_ == 0)
{
lean_dec_ref(v_e_1610_);
if (v___y_1629_ == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_dec_ref(v_h_1632_);
lean_dec_ref(v___y_1631_);
lean_dec_ref(v___y_1628_);
v___x_1643_ = lean_box(0);
v___x_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
return v___x_1644_;
}
else
{
lean_object* v___x_1645_; 
lean_inc_ref(v___y_1631_);
v___x_1645_ = l_Lean_Meta_normLitValue(v___y_1631_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
lean_inc_ref(v___y_1628_);
v___x_1647_ = l_Lean_Meta_normLitValue(v___y_1628_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1687_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1687_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1687_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
uint8_t v___x_1652_; 
v___x_1652_ = lean_expr_eqv(v_a_1646_, v_a_1648_);
lean_dec(v_a_1648_);
lean_dec(v_a_1646_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; 
lean_del_object(v___x_1650_);
v___x_1653_ = l_Lean_Meta_mkEq(v___y_1631_, v___y_1628_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v___x_1653_, 1);
v___x_1655_ = l_Lean_mkNot(v_a_1654_);
v___x_1656_ = l_Lean_Meta_mkDecideProof(v___x_1655_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1666_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1666_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1666_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1661_ = l_Lean_Expr_app___override(v_a_1657_, v_h_1632_);
v___x_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v___x_1662_);
v___x_1664_ = v___x_1659_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec_ref(v_h_1632_);
v_a_1667_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1656_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1656_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
lean_dec_ref(v_h_1632_);
v_a_1675_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1653_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1653_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1685_; 
lean_dec_ref(v_h_1632_);
lean_dec_ref(v___y_1631_);
lean_dec_ref(v___y_1628_);
v___x_1683_ = lean_box(0);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1683_);
v___x_1685_ = v___x_1650_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_dec(v_a_1646_);
lean_dec_ref(v_h_1632_);
lean_dec_ref(v___y_1631_);
lean_dec_ref(v___y_1628_);
v_a_1688_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1647_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1647_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec_ref(v_h_1632_);
lean_dec_ref(v___y_1631_);
lean_dec_ref(v___y_1628_);
v_a_1696_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1645_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1645_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
else
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_Meta_isConstructorApp_x3f(v___y_1631_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1805_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1805_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1805_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
if (lean_obj_tag(v_a_1705_) == 1)
{
lean_object* v_val_1709_; lean_object* v___x_1710_; 
lean_del_object(v___x_1707_);
v_val_1709_ = lean_ctor_get(v_a_1705_, 0);
lean_inc(v_val_1709_);
lean_dec_ref_known(v_a_1705_, 1);
v___x_1710_ = l_Lean_Meta_isConstructorApp_x3f(v___y_1628_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1792_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1792_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1792_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
if (lean_obj_tag(v_a_1711_) == 1)
{
lean_object* v_val_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1787_; 
lean_del_object(v___x_1713_);
v_val_1715_ = lean_ctor_get(v_a_1711_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_a_1711_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1717_ = v_a_1711_;
v_isShared_1718_ = v_isSharedCheck_1787_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_val_1715_);
lean_dec(v_a_1711_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1787_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_1637_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1721_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 1);
v___x_1721_ = l_Lean_Meta_mkNoConfusion(v_a_1720_, v_h_1632_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_toConstantVal_1722_; lean_object* v_toConstantVal_1723_; lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1770_; 
v_toConstantVal_1722_ = lean_ctor_get(v_val_1709_, 0);
lean_inc_ref(v_toConstantVal_1722_);
lean_dec(v_val_1709_);
v_toConstantVal_1723_ = lean_ctor_get(v_val_1715_, 0);
lean_inc_ref(v_toConstantVal_1723_);
lean_dec(v_val_1715_);
v_a_1724_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1726_ = v___x_1721_;
v_isShared_1727_ = v_isSharedCheck_1770_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1721_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1770_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v_name_1728_; lean_object* v_name_1729_; uint8_t v___x_1730_; 
v_name_1728_ = lean_ctor_get(v_toConstantVal_1722_, 0);
lean_inc(v_name_1728_);
lean_dec_ref(v_toConstantVal_1722_);
v_name_1729_ = lean_ctor_get(v_toConstantVal_1723_, 0);
lean_inc(v_name_1729_);
lean_dec_ref(v_toConstantVal_1723_);
v___x_1730_ = lean_name_eq(v_name_1728_, v_name_1729_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1732_; 
lean_dec(v_name_1729_);
lean_dec(v_name_1728_);
lean_dec_ref(v_e_1610_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v_a_1724_);
v___x_1732_ = v___x_1717_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1724_);
v___x_1732_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1734_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1732_);
v___x_1734_ = v___x_1726_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
else
{
lean_object* v___x_1737_; lean_object* v___f_1738_; uint8_t v___x_1739_; lean_object* v___x_1740_; 
lean_del_object(v___x_1726_);
lean_del_object(v___x_1717_);
v___x_1737_ = lean_box(v___y_1627_);
lean_inc(v_a_1724_);
v___f_1738_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed), 18, 5);
lean_closure_set(v___f_1738_, 0, v_e_1610_);
lean_closure_set(v___f_1738_, 1, v_name_1728_);
lean_closure_set(v___f_1738_, 2, v_name_1729_);
lean_closure_set(v___f_1738_, 3, v___x_1737_);
lean_closure_set(v___f_1738_, 4, v_a_1724_);
v___x_1739_ = 0;
lean_inc(v___y_1642_);
lean_inc_ref(v___y_1641_);
lean_inc(v___y_1640_);
lean_inc_ref(v___y_1639_);
v___x_1740_ = lean_infer_type(v_a_1724_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1742_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref_known(v___x_1740_, 1);
v___x_1742_ = l_Lean_Meta_whnfD(v_a_1741_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1753_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1745_ = v___x_1742_;
v_isShared_1746_ = v_isSharedCheck_1753_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1742_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1753_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
if (lean_obj_tag(v_a_1743_) == 7)
{
lean_object* v_binderType_1747_; lean_object* v___x_1748_; 
lean_del_object(v___x_1745_);
v_binderType_1747_ = lean_ctor_get(v_a_1743_, 1);
lean_inc_ref(v_binderType_1747_);
lean_dec_ref_known(v_a_1743_, 3);
v___x_1748_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_binderType_1747_, v___f_1738_, v___x_1739_, v___x_1739_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
return v___x_1748_;
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1751_; 
lean_dec(v_a_1743_);
lean_dec_ref(v___f_1738_);
v___x_1749_ = lean_box(0);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1749_);
v___x_1751_ = v___x_1745_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec_ref(v___f_1738_);
v_a_1754_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1742_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1742_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec_ref(v___f_1738_);
v_a_1762_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1740_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1740_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_del_object(v___x_1717_);
lean_dec(v_val_1715_);
lean_dec(v_val_1709_);
lean_dec_ref(v_e_1610_);
v_a_1771_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1721_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1721_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_del_object(v___x_1717_);
lean_dec(v_val_1715_);
lean_dec(v_val_1709_);
lean_dec_ref(v_h_1632_);
lean_dec_ref(v_e_1610_);
v_a_1779_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1719_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1719_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
else
{
lean_object* v___x_1788_; lean_object* v___x_1790_; 
lean_dec(v_a_1711_);
lean_dec(v_val_1709_);
lean_dec_ref(v_h_1632_);
lean_dec_ref(v_e_1610_);
v___x_1788_ = lean_box(0);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1788_);
v___x_1790_ = v___x_1713_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v_val_1709_);
lean_dec_ref(v_h_1632_);
lean_dec_ref(v_e_1610_);
v_a_1793_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1710_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1710_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1803_; 
lean_dec(v_a_1705_);
lean_dec_ref(v_h_1632_);
lean_dec_ref(v___y_1628_);
lean_dec_ref(v_e_1610_);
v___x_1801_ = lean_box(0);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1801_);
v___x_1803_ = v___x_1707_;
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
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_dec_ref(v_h_1632_);
lean_dec_ref(v___y_1628_);
lean_dec_ref(v_e_1610_);
v_a_1806_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1704_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1704_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
}
v___jp_1814_:
{
lean_object* v_self_1829_; uint8_t v_interpreted_1830_; uint8_t v_ctor_1831_; lean_object* v___x_1832_; 
v_self_1829_ = lean_ctor_get(v___y_1827_, 0);
lean_inc_ref_n(v_self_1829_, 2);
v_interpreted_1830_ = lean_ctor_get_uint8(v___y_1827_, sizeof(void*)*12 + 1);
v_ctor_1831_ = lean_ctor_get_uint8(v___y_1827_, sizeof(void*)*12 + 2);
lean_dec_ref(v___y_1827_);
lean_inc_ref(v___y_1815_);
v___x_1832_ = l_Lean_Meta_Grind_hasSameType(v_self_1829_, v___y_1815_, v___y_1820_, v___y_1825_, v___y_1821_, v___y_1826_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1895_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1895_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1895_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
uint8_t v___x_1837_; 
v___x_1837_ = lean_unbox(v_a_1833_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; lean_object* v___x_1840_; 
lean_dec(v_a_1833_);
lean_dec_ref(v_self_1829_);
lean_dec_ref(v___y_1824_);
lean_dec_ref(v___y_1815_);
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v___x_1838_ = lean_box(0);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v___x_1838_);
v___x_1840_ = v___x_1835_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
else
{
lean_del_object(v___x_1835_);
if (v___y_1828_ == 0)
{
lean_object* v___x_1842_; 
lean_inc(v___y_1826_);
lean_inc_ref(v___y_1821_);
lean_inc(v___y_1825_);
lean_inc_ref(v___y_1820_);
lean_inc(v___y_1817_);
lean_inc_ref(v___y_1822_);
lean_inc(v___y_1819_);
lean_inc_ref(v___y_1816_);
lean_inc(v___y_1823_);
lean_inc(v___y_1818_);
lean_inc_ref(v_self_1829_);
v___x_1842_ = lean_grind_mk_eq_proof(v_self_1829_, v___y_1824_, v___y_1818_, v___y_1823_, v___y_1816_, v___y_1819_, v___y_1822_, v___y_1817_, v___y_1820_, v___y_1825_, v___y_1821_, v___y_1826_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1844_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_a_1843_);
lean_dec_ref_known(v___x_1842_, 1);
v___x_1844_ = l_Lean_Meta_mkEqTrans(v_a_1843_, v_h_1611_, v___y_1820_, v___y_1825_, v___y_1821_, v___y_1826_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; uint8_t v___x_1846_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref_known(v___x_1844_, 1);
v___x_1846_ = lean_unbox(v_a_1833_);
lean_dec(v_a_1833_);
v___y_1627_ = v___x_1846_;
v___y_1628_ = v___y_1815_;
v___y_1629_ = v_interpreted_1830_;
v___y_1630_ = v_ctor_1831_;
v___y_1631_ = v_self_1829_;
v_h_1632_ = v_a_1845_;
v___y_1633_ = v___y_1818_;
v___y_1634_ = v___y_1823_;
v___y_1635_ = v___y_1816_;
v___y_1636_ = v___y_1819_;
v___y_1637_ = v___y_1822_;
v___y_1638_ = v___y_1817_;
v___y_1639_ = v___y_1820_;
v___y_1640_ = v___y_1825_;
v___y_1641_ = v___y_1821_;
v___y_1642_ = v___y_1826_;
goto v___jp_1626_;
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v_a_1833_);
lean_dec_ref(v_self_1829_);
lean_dec_ref(v___y_1815_);
lean_dec_ref(v_e_1610_);
v_a_1847_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1844_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1844_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec(v_a_1833_);
lean_dec_ref(v_self_1829_);
lean_dec_ref(v___y_1815_);
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v_a_1855_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1842_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1842_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
else
{
lean_object* v___x_1863_; 
lean_inc(v___y_1826_);
lean_inc_ref(v___y_1821_);
lean_inc(v___y_1825_);
lean_inc_ref(v___y_1820_);
lean_inc(v___y_1817_);
lean_inc_ref(v___y_1822_);
lean_inc(v___y_1819_);
lean_inc_ref(v___y_1816_);
lean_inc(v___y_1823_);
lean_inc(v___y_1818_);
lean_inc_ref(v_self_1829_);
v___x_1863_ = lean_grind_mk_heq_proof(v_self_1829_, v___y_1824_, v___y_1818_, v___y_1823_, v___y_1816_, v___y_1819_, v___y_1822_, v___y_1817_, v___y_1820_, v___y_1825_, v___y_1821_, v___y_1826_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1865_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref_known(v___x_1863_, 1);
v___x_1865_ = l_Lean_Meta_mkHEqTrans(v_a_1864_, v_h_1611_, v___y_1820_, v___y_1825_, v___y_1821_, v___y_1826_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; uint8_t v___x_1867_; lean_object* v___x_1868_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v___x_1865_, 1);
v___x_1867_ = 0;
v___x_1868_ = l_Lean_Meta_mkEqOfHEq(v_a_1866_, v___x_1867_, v___y_1820_, v___y_1825_, v___y_1821_, v___y_1826_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; uint8_t v___x_1870_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref_known(v___x_1868_, 1);
v___x_1870_ = lean_unbox(v_a_1833_);
lean_dec(v_a_1833_);
v___y_1627_ = v___x_1870_;
v___y_1628_ = v___y_1815_;
v___y_1629_ = v_interpreted_1830_;
v___y_1630_ = v_ctor_1831_;
v___y_1631_ = v_self_1829_;
v_h_1632_ = v_a_1869_;
v___y_1633_ = v___y_1818_;
v___y_1634_ = v___y_1823_;
v___y_1635_ = v___y_1816_;
v___y_1636_ = v___y_1819_;
v___y_1637_ = v___y_1822_;
v___y_1638_ = v___y_1817_;
v___y_1639_ = v___y_1820_;
v___y_1640_ = v___y_1825_;
v___y_1641_ = v___y_1821_;
v___y_1642_ = v___y_1826_;
goto v___jp_1626_;
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec(v_a_1833_);
lean_dec_ref(v_self_1829_);
lean_dec_ref(v___y_1815_);
lean_dec_ref(v_e_1610_);
v_a_1871_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1868_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1868_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec(v_a_1833_);
lean_dec_ref(v_self_1829_);
lean_dec_ref(v___y_1815_);
lean_dec_ref(v_e_1610_);
v_a_1879_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1865_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1865_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
lean_dec(v_a_1833_);
lean_dec_ref(v_self_1829_);
lean_dec_ref(v___y_1815_);
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v_a_1887_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1889_ = v___x_1863_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1863_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
lean_dec_ref(v_self_1829_);
lean_dec_ref(v___y_1824_);
lean_dec_ref(v___y_1815_);
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v_a_1896_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1832_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1832_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
v___jp_1904_:
{
lean_object* v___x_1915_; 
lean_inc(v___y_1914_);
lean_inc_ref(v___y_1913_);
lean_inc(v___y_1912_);
lean_inc_ref(v___y_1911_);
lean_inc_ref(v_h_1611_);
v___x_1915_ = lean_infer_type(v_h_1611_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1993_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1918_ = v___x_1915_;
v_isShared_1919_ = v_isSharedCheck_1993_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1915_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1993_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; 
v___x_1920_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_a_1916_);
lean_dec(v_a_1916_);
if (lean_obj_tag(v___x_1920_) == 1)
{
lean_object* v_val_1921_; lean_object* v_snd_1922_; lean_object* v_fst_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1988_; 
lean_del_object(v___x_1918_);
v_val_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_val_1921_);
lean_dec_ref_known(v___x_1920_, 1);
v_snd_1922_ = lean_ctor_get(v_val_1921_, 1);
v_fst_1923_ = lean_ctor_get(v_val_1921_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v_val_1921_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1925_ = v_val_1921_;
v_isShared_1926_ = v_isSharedCheck_1988_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_snd_1922_);
lean_inc(v_fst_1923_);
lean_dec(v_val_1921_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1988_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v_fst_1927_; lean_object* v_snd_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1987_; 
v_fst_1927_ = lean_ctor_get(v_snd_1922_, 0);
v_snd_1928_ = lean_ctor_get(v_snd_1922_, 1);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_snd_1922_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1930_ = v_snd_1922_;
v_isShared_1931_ = v_isSharedCheck_1987_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_snd_1928_);
lean_inc(v_fst_1927_);
lean_dec(v_snd_1922_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1987_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; 
v___x_1932_ = l_Lean_Meta_Sym_shareCommon(v_fst_1927_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1934_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
v___x_1934_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_a_1933_, v___y_1905_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v___x_1934_, 1);
if (lean_obj_tag(v_a_1935_) == 1)
{
lean_del_object(v___x_1930_);
lean_del_object(v___x_1925_);
if (lean_obj_tag(v_fst_1923_) == 0)
{
lean_object* v_val_1936_; uint8_t v___x_1937_; 
v_val_1936_ = lean_ctor_get(v_a_1935_, 0);
lean_inc(v_val_1936_);
lean_dec_ref_known(v_a_1935_, 1);
v___x_1937_ = 0;
v___y_1815_ = v_snd_1928_;
v___y_1816_ = v___y_1907_;
v___y_1817_ = v___y_1910_;
v___y_1818_ = v___y_1905_;
v___y_1819_ = v___y_1908_;
v___y_1820_ = v___y_1911_;
v___y_1821_ = v___y_1913_;
v___y_1822_ = v___y_1909_;
v___y_1823_ = v___y_1906_;
v___y_1824_ = v_a_1933_;
v___y_1825_ = v___y_1912_;
v___y_1826_ = v___y_1914_;
v___y_1827_ = v_val_1936_;
v___y_1828_ = v___x_1937_;
goto v___jp_1814_;
}
else
{
lean_object* v_val_1938_; uint8_t v___x_1939_; 
lean_dec_ref_known(v_fst_1923_, 1);
v_val_1938_ = lean_ctor_get(v_a_1935_, 0);
lean_inc(v_val_1938_);
lean_dec_ref_known(v_a_1935_, 1);
v___x_1939_ = 1;
v___y_1815_ = v_snd_1928_;
v___y_1816_ = v___y_1907_;
v___y_1817_ = v___y_1910_;
v___y_1818_ = v___y_1905_;
v___y_1819_ = v___y_1908_;
v___y_1820_ = v___y_1911_;
v___y_1821_ = v___y_1913_;
v___y_1822_ = v___y_1909_;
v___y_1823_ = v___y_1906_;
v___y_1824_ = v_a_1933_;
v___y_1825_ = v___y_1912_;
v___y_1826_ = v___y_1914_;
v___y_1827_ = v_val_1938_;
v___y_1828_ = v___x_1939_;
goto v___jp_1814_;
}
}
else
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1943_; 
lean_dec(v_a_1935_);
lean_dec(v_snd_1928_);
lean_dec(v_fst_1923_);
lean_dec_ref(v_h_1611_);
v___x_1940_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1);
v___x_1941_ = l_Lean_indentExpr(v_a_1933_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set_tag(v___x_1930_, 7);
lean_ctor_set(v___x_1930_, 1, v___x_1941_);
lean_ctor_set(v___x_1930_, 0, v___x_1940_);
v___x_1943_ = v___x_1930_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v___x_1941_);
v___x_1943_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
lean_object* v___x_1944_; lean_object* v___x_1946_; 
v___x_1944_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3);
if (v_isShared_1926_ == 0)
{
lean_ctor_set_tag(v___x_1925_, 7);
lean_ctor_set(v___x_1925_, 1, v___x_1944_);
lean_ctor_set(v___x_1925_, 0, v___x_1943_);
v___x_1946_ = v___x_1925_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1947_ = l_Lean_indentExpr(v_e_1610_);
v___x_1948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1946_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1909_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; uint8_t v_verbose_1951_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref_known(v___x_1949_, 1);
v_verbose_1951_ = lean_ctor_get_uint8(v_a_1950_, 0);
lean_dec(v_a_1950_);
if (v_verbose_1951_ == 0)
{
lean_dec_ref_known(v___x_1948_, 2);
goto v___jp_1623_;
}
else
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Lean_Meta_Sym_reportIssue(v___x_1948_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_dec_ref_known(v___x_1952_, 1);
goto v___jp_1623_;
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1952_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1952_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec_ref_known(v___x_1948_, 2);
v_a_1961_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1949_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1949_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec(v_a_1933_);
lean_del_object(v___x_1930_);
lean_dec(v_snd_1928_);
lean_del_object(v___x_1925_);
lean_dec(v_fst_1923_);
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v_a_1971_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1934_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1934_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
lean_del_object(v___x_1930_);
lean_dec(v_snd_1928_);
lean_del_object(v___x_1925_);
lean_dec(v_fst_1923_);
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v_a_1979_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1932_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1932_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
}
}
else
{
lean_object* v___x_1989_; lean_object* v___x_1991_; 
lean_dec(v___x_1920_);
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v___x_1989_ = lean_box(0);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v___x_1989_);
v___x_1991_ = v___x_1918_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1989_);
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
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec_ref(v_h_1611_);
lean_dec_ref(v_e_1610_);
v_a_1994_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1915_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1915_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(lean_object* v_e_2040_, lean_object* v_xs_2041_, lean_object* v___x_2042_, lean_object* v___x_2043_, uint8_t v_a_2044_, lean_object* v_a_2045_, lean_object* v_as_2046_, size_t v_sz_2047_, size_t v_i_2048_, lean_object* v_b_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
uint8_t v___y_2062_; uint8_t v___x_2110_; 
v___x_2110_ = lean_name_eq(v___x_2042_, v___x_2043_);
if (v___x_2110_ == 0)
{
uint8_t v___x_2111_; 
v___x_2111_ = 1;
v___y_2062_ = v___x_2111_;
goto v___jp_2061_;
}
else
{
uint8_t v___x_2112_; 
v___x_2112_ = 0;
v___y_2062_ = v___x_2112_;
goto v___jp_2061_;
}
v___jp_2061_:
{
uint8_t v___x_2063_; 
v___x_2063_ = lean_usize_dec_lt(v_i_2048_, v_sz_2047_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; 
lean_dec_ref(v_a_2045_);
lean_dec_ref(v_e_2040_);
v___x_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2064_, 0, v_b_2049_);
return v___x_2064_;
}
else
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v_a_2067_; lean_object* v___x_2068_; 
lean_dec_ref(v_b_2049_);
v___x_2065_ = lean_box(0);
v___x_2066_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_a_2067_ = lean_array_uget_borrowed(v_as_2046_, v_i_2048_);
lean_inc(v_a_2067_);
lean_inc_ref(v_e_2040_);
v___x_2068_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2040_, v_a_2067_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_a_2069_);
lean_dec_ref_known(v___x_2068_, 1);
if (lean_obj_tag(v_a_2069_) == 1)
{
lean_object* v_val_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2098_; 
lean_dec_ref(v_e_2040_);
v_val_2070_ = lean_ctor_get(v_a_2069_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_a_2069_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2072_ = v_a_2069_;
v_isShared_2073_ = v_isSharedCheck_2098_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_val_2070_);
lean_dec(v_a_2069_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2098_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
uint8_t v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = 1;
v___x_2075_ = l_Lean_Meta_mkLambdaFVars(v_xs_2041_, v_val_2070_, v___y_2062_, v_a_2044_, v___y_2062_, v_a_2044_, v___x_2074_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2089_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2089_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2089_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2080_ = l_Lean_Expr_app___override(v_a_2045_, v_a_2076_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 0, v___x_2080_);
v___x_2082_ = v___x_2072_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
v___x_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
lean_ctor_set(v___x_2084_, 1, v___x_2065_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2084_);
v___x_2086_ = v___x_2078_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
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
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_del_object(v___x_2072_);
lean_dec_ref(v_a_2045_);
v_a_2090_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2075_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2075_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
else
{
size_t v___x_2099_; size_t v___x_2100_; 
lean_dec(v_a_2069_);
v___x_2099_ = ((size_t)1ULL);
v___x_2100_ = lean_usize_add(v_i_2048_, v___x_2099_);
v_i_2048_ = v___x_2100_;
v_b_2049_ = v___x_2066_;
goto _start;
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec_ref(v_a_2045_);
lean_dec_ref(v_e_2040_);
v_a_2102_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2068_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2068_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(lean_object* v_e_2113_, lean_object* v_name_2114_, lean_object* v_name_2115_, uint8_t v_a_2116_, lean_object* v_a_2117_, lean_object* v_xs_2118_, lean_object* v_x_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; size_t v_sz_2133_; size_t v___x_2134_; lean_object* v___x_2135_; 
v___x_2131_ = lean_box(0);
v___x_2132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_sz_2133_ = lean_array_size(v_xs_2118_);
v___x_2134_ = ((size_t)0ULL);
v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_2113_, v_xs_2118_, v_name_2114_, v_name_2115_, v_a_2116_, v_a_2117_, v_xs_2118_, v_sz_2133_, v___x_2134_, v___x_2132_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2148_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2148_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2148_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v_fst_2140_; 
v_fst_2140_ = lean_ctor_get(v_a_2136_, 0);
lean_inc(v_fst_2140_);
lean_dec(v_a_2136_);
if (lean_obj_tag(v_fst_2140_) == 0)
{
lean_object* v___x_2142_; 
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2131_);
v___x_2142_ = v___x_2138_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2131_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
else
{
lean_object* v_val_2144_; lean_object* v___x_2146_; 
v_val_2144_ = lean_ctor_get(v_fst_2140_, 0);
lean_inc(v_val_2144_);
lean_dec_ref_known(v_fst_2140_, 1);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v_val_2144_);
v___x_2146_ = v___x_2138_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_val_2144_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
v_a_2149_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2135_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2135_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_e_2157_ = _args[0];
lean_object* v_xs_2158_ = _args[1];
lean_object* v___x_2159_ = _args[2];
lean_object* v___x_2160_ = _args[3];
lean_object* v_a_2161_ = _args[4];
lean_object* v_a_2162_ = _args[5];
lean_object* v_as_2163_ = _args[6];
lean_object* v_sz_2164_ = _args[7];
lean_object* v_i_2165_ = _args[8];
lean_object* v_b_2166_ = _args[9];
lean_object* v___y_2167_ = _args[10];
lean_object* v___y_2168_ = _args[11];
lean_object* v___y_2169_ = _args[12];
lean_object* v___y_2170_ = _args[13];
lean_object* v___y_2171_ = _args[14];
lean_object* v___y_2172_ = _args[15];
lean_object* v___y_2173_ = _args[16];
lean_object* v___y_2174_ = _args[17];
lean_object* v___y_2175_ = _args[18];
lean_object* v___y_2176_ = _args[19];
lean_object* v___y_2177_ = _args[20];
_start:
{
uint8_t v_a_80090__boxed_2178_; size_t v_sz_boxed_2179_; size_t v_i_boxed_2180_; lean_object* v_res_2181_; 
v_a_80090__boxed_2178_ = lean_unbox(v_a_2161_);
v_sz_boxed_2179_ = lean_unbox_usize(v_sz_2164_);
lean_dec(v_sz_2164_);
v_i_boxed_2180_ = lean_unbox_usize(v_i_2165_);
lean_dec(v_i_2165_);
v_res_2181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_2157_, v_xs_2158_, v___x_2159_, v___x_2160_, v_a_80090__boxed_2178_, v_a_2162_, v_as_2163_, v_sz_boxed_2179_, v_i_boxed_2180_, v_b_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v_as_2163_);
lean_dec(v___x_2160_);
lean_dec(v___x_2159_);
lean_dec_ref(v_xs_2158_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___boxed(lean_object* v_e_2182_, lean_object* v_h_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2182_, v_h_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
lean_dec(v_a_2193_);
lean_dec_ref(v_a_2192_);
lean_dec(v_a_2191_);
lean_dec_ref(v_a_2190_);
lean_dec(v_a_2189_);
lean_dec_ref(v_a_2188_);
lean_dec(v_a_2187_);
lean_dec_ref(v_a_2186_);
lean_dec(v_a_2185_);
lean_dec(v_a_2184_);
return v_res_2195_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__0));
v___x_2198_ = l_Lean_stringToMessageData(v___x_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(lean_object* v_e_2199_, lean_object* v_xs_2200_, uint8_t v___x_2201_, lean_object* v_as_2202_, size_t v_sz_2203_, size_t v_i_2204_, lean_object* v_b_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_a_2218_; uint8_t v___x_2222_; 
v___x_2222_ = lean_usize_dec_lt(v_i_2204_, v_sz_2203_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; 
lean_dec_ref(v_e_2199_);
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v_b_2205_);
return v___x_2223_;
}
else
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v_a_2227_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___x_2278_; 
lean_dec_ref(v_b_2205_);
v___x_2224_ = lean_box(0);
v___x_2225_ = lean_box(0);
v___x_2226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_a_2227_ = lean_array_uget_borrowed(v_as_2202_, v_i_2204_);
lean_inc(v___y_2215_);
lean_inc_ref(v___y_2214_);
lean_inc(v___y_2213_);
lean_inc_ref(v___y_2212_);
lean_inc(v_a_2227_);
v___x_2278_ = lean_infer_type(v_a_2227_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2280_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2278_, 1);
v___x_2280_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_a_2279_, v___x_2225_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; uint8_t v___x_2282_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref_known(v___x_2280_, 1);
v___x_2282_ = lean_unbox(v_a_2281_);
lean_dec(v_a_2281_);
if (v___x_2282_ == 0)
{
lean_dec(v_a_2279_);
v_a_2218_ = v___x_2226_;
goto v___jp_2217_;
}
else
{
lean_object* v_toCold_2283_; lean_object* v_options_2284_; uint8_t v_hasTrace_2285_; 
v_toCold_2283_ = lean_ctor_get(v___y_2214_, 0);
v_options_2284_ = lean_ctor_get(v_toCold_2283_, 2);
v_hasTrace_2285_ = lean_ctor_get_uint8(v_options_2284_, sizeof(void*)*1);
if (v_hasTrace_2285_ == 0)
{
lean_dec(v_a_2279_);
v___y_2229_ = v___y_2206_;
v___y_2230_ = v___y_2207_;
v___y_2231_ = v___y_2208_;
v___y_2232_ = v___y_2209_;
v___y_2233_ = v___y_2210_;
v___y_2234_ = v___y_2211_;
v___y_2235_ = v___y_2212_;
v___y_2236_ = v___y_2213_;
v___y_2237_ = v___y_2214_;
v___y_2238_ = v___y_2215_;
goto v___jp_2228_;
}
else
{
lean_object* v_inheritedTraceOptions_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v_inheritedTraceOptions_2286_ = lean_ctor_get(v_toCold_2283_, 11);
v___x_2287_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_2288_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_2289_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2286_, v_options_2284_, v___x_2288_);
if (v___x_2289_ == 0)
{
lean_dec(v_a_2279_);
v___y_2229_ = v___y_2206_;
v___y_2230_ = v___y_2207_;
v___y_2231_ = v___y_2208_;
v___y_2232_ = v___y_2209_;
v___y_2233_ = v___y_2210_;
v___y_2234_ = v___y_2211_;
v___y_2235_ = v___y_2212_;
v___y_2236_ = v___y_2213_;
v___y_2237_ = v___y_2214_;
v___y_2238_ = v___y_2215_;
goto v___jp_2228_;
}
else
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Lean_Meta_Grind_updateLastTag(v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
lean_dec_ref_known(v___x_2290_, 1);
v___x_2291_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1);
v___x_2292_ = l_Lean_MessageData_ofExpr(v_a_2279_);
v___x_2293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_2287_, v___x_2293_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_dec_ref_known(v___x_2294_, 1);
v___y_2229_ = v___y_2206_;
v___y_2230_ = v___y_2207_;
v___y_2231_ = v___y_2208_;
v___y_2232_ = v___y_2209_;
v___y_2233_ = v___y_2210_;
v___y_2234_ = v___y_2211_;
v___y_2235_ = v___y_2212_;
v___y_2236_ = v___y_2213_;
v___y_2237_ = v___y_2214_;
v___y_2238_ = v___y_2215_;
goto v___jp_2228_;
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec_ref(v_e_2199_);
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2294_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec(v_a_2279_);
lean_dec_ref(v_e_2199_);
v_a_2303_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2290_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2290_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_dec(v_a_2279_);
lean_dec_ref(v_e_2199_);
v_a_2311_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2280_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2280_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec_ref(v_e_2199_);
v_a_2319_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2278_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2278_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
v___jp_2228_:
{
lean_object* v___x_2239_; 
lean_inc(v_a_2227_);
lean_inc_ref(v_e_2199_);
v___x_2239_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2199_, v_a_2227_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v___x_2239_, 1);
if (lean_obj_tag(v_a_2240_) == 1)
{
lean_object* v_val_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2269_; 
lean_dec_ref(v_e_2199_);
v_val_2241_ = lean_ctor_get(v_a_2240_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_a_2240_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2243_ = v_a_2240_;
v_isShared_2244_ = v_isSharedCheck_2269_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_val_2241_);
lean_dec(v_a_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2269_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
uint8_t v___x_2245_; uint8_t v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = 0;
v___x_2246_ = 1;
v___x_2247_ = l_Lean_Meta_mkLambdaFVars(v_xs_2200_, v_val_2241_, v___x_2245_, v___x_2201_, v___x_2245_, v___x_2201_, v___x_2246_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2260_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2250_ = v___x_2247_;
v_isShared_2251_ = v_isSharedCheck_2260_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2247_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2260_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v_a_2248_);
v___x_2253_ = v___x_2243_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2257_; 
v___x_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
v___x_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
lean_ctor_set(v___x_2255_, 1, v___x_2224_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 0, v___x_2255_);
v___x_2257_ = v___x_2250_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2255_);
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
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
lean_del_object(v___x_2243_);
v_a_2261_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2247_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2247_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
}
else
{
lean_dec(v_a_2240_);
v_a_2218_ = v___x_2226_;
goto v___jp_2217_;
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec_ref(v_e_2199_);
v_a_2270_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2239_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2239_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
v___jp_2217_:
{
size_t v___x_2219_; size_t v___x_2220_; 
v___x_2219_ = ((size_t)1ULL);
v___x_2220_ = lean_usize_add(v_i_2204_, v___x_2219_);
lean_inc_ref(v_a_2218_);
v_i_2204_ = v___x_2220_;
v_b_2205_ = v_a_2218_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_e_2327_ = _args[0];
lean_object* v_xs_2328_ = _args[1];
lean_object* v___x_2329_ = _args[2];
lean_object* v_as_2330_ = _args[3];
lean_object* v_sz_2331_ = _args[4];
lean_object* v_i_2332_ = _args[5];
lean_object* v_b_2333_ = _args[6];
lean_object* v___y_2334_ = _args[7];
lean_object* v___y_2335_ = _args[8];
lean_object* v___y_2336_ = _args[9];
lean_object* v___y_2337_ = _args[10];
lean_object* v___y_2338_ = _args[11];
lean_object* v___y_2339_ = _args[12];
lean_object* v___y_2340_ = _args[13];
lean_object* v___y_2341_ = _args[14];
lean_object* v___y_2342_ = _args[15];
lean_object* v___y_2343_ = _args[16];
lean_object* v___y_2344_ = _args[17];
_start:
{
uint8_t v___x_21114__boxed_2345_; size_t v_sz_boxed_2346_; size_t v_i_boxed_2347_; lean_object* v_res_2348_; 
v___x_21114__boxed_2345_ = lean_unbox(v___x_2329_);
v_sz_boxed_2346_ = lean_unbox_usize(v_sz_2331_);
lean_dec(v_sz_2331_);
v_i_boxed_2347_ = lean_unbox_usize(v_i_2332_);
lean_dec(v_i_2332_);
v_res_2348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2327_, v_xs_2328_, v___x_21114__boxed_2345_, v_as_2330_, v_sz_boxed_2346_, v_i_boxed_2347_, v_b_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v_as_2330_);
lean_dec_ref(v_xs_2328_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(lean_object* v_e_2349_, uint8_t v___x_2350_, lean_object* v_xs_2351_, lean_object* v_x_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; size_t v_sz_2366_; size_t v___x_2367_; lean_object* v___x_2368_; 
v___x_2364_ = lean_box(0);
v___x_2365_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_sz_2366_ = lean_array_size(v_xs_2351_);
v___x_2367_ = ((size_t)0ULL);
v___x_2368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2349_, v_xs_2351_, v___x_2350_, v_xs_2351_, v_sz_2366_, v___x_2367_, v___x_2365_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2381_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2371_ = v___x_2368_;
v_isShared_2372_ = v_isSharedCheck_2381_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2368_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2381_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v_fst_2373_; 
v_fst_2373_ = lean_ctor_get(v_a_2369_, 0);
lean_inc(v_fst_2373_);
lean_dec(v_a_2369_);
if (lean_obj_tag(v_fst_2373_) == 0)
{
lean_object* v___x_2375_; 
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v___x_2364_);
v___x_2375_ = v___x_2371_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2364_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
else
{
lean_object* v_val_2377_; lean_object* v___x_2379_; 
v_val_2377_ = lean_ctor_get(v_fst_2373_, 0);
lean_inc(v_val_2377_);
lean_dec_ref_known(v_fst_2373_, 1);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v_val_2377_);
v___x_2379_ = v___x_2371_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_val_2377_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
v_a_2382_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2368_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2368_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed(lean_object* v_e_2390_, lean_object* v___x_2391_, lean_object* v_xs_2392_, lean_object* v_x_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
uint8_t v___x_21368__boxed_2405_; lean_object* v_res_2406_; 
v___x_21368__boxed_2405_ = lean_unbox(v___x_2391_);
v_res_2406_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(v_e_2390_, v___x_21368__boxed_2405_, v_xs_2392_, v_x_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v_x_2393_);
lean_dec_ref(v_xs_2392_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(lean_object* v_e_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v___x_2422_; 
lean_inc_ref(v_e_2407_);
v___x_2422_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2407_, v_a_2415_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2424_; uint8_t v___x_2425_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2423_);
lean_dec_ref_known(v___x_2422_, 1);
v___x_2424_ = l_Lean_Expr_cleanupAnnotations(v_a_2423_);
lean_dec(v_a_2423_);
v___x_2425_ = l_Lean_Expr_isApp(v___x_2424_);
if (v___x_2425_ == 0)
{
lean_dec_ref(v___x_2424_);
lean_dec_ref(v_e_2407_);
goto v___jp_2419_;
}
else
{
lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; 
v___x_2426_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2424_);
v___x_2427_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_2428_ = l_Lean_Expr_isConstOf(v___x_2426_, v___x_2427_);
lean_dec_ref(v___x_2426_);
if (v___x_2428_ == 0)
{
lean_dec_ref(v___x_2424_);
lean_dec_ref(v_e_2407_);
goto v___jp_2419_;
}
else
{
lean_object* v_arg_2429_; lean_object* v___x_2430_; lean_object* v___f_2431_; uint8_t v___x_2432_; lean_object* v___x_2433_; 
v_arg_2429_ = lean_ctor_get(v___x_2424_, 1);
lean_inc_ref(v_arg_2429_);
lean_dec_ref(v___x_2424_);
v___x_2430_ = lean_box(v___x_2428_);
v___f_2431_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed), 15, 2);
lean_closure_set(v___f_2431_, 0, v_e_2407_);
lean_closure_set(v___f_2431_, 1, v___x_2430_);
v___x_2432_ = 0;
v___x_2433_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_arg_2429_, v___f_2431_, v___x_2432_, v___x_2432_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
return v___x_2433_;
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_dec_ref(v_e_2407_);
v_a_2434_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2422_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2422_);
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
v___jp_2419_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = lean_box(0);
v___x_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2420_);
return v___x_2421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___boxed(lean_object* v_e_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
lean_dec(v_a_2450_);
lean_dec_ref(v_a_2449_);
lean_dec(v_a_2448_);
lean_dec_ref(v_a_2447_);
lean_dec(v_a_2446_);
lean_dec_ref(v_a_2445_);
lean_dec(v_a_2444_);
lean_dec(v_a_2443_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(lean_object* v_e_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_){
_start:
{
lean_object* v___x_2461_; uint8_t v___x_2462_; uint8_t v___x_2463_; 
v___x_2461_ = l_Lean_Expr_getAppFn(v_e_2455_);
v___x_2462_ = l_Lean_Expr_isMVar(v___x_2461_);
lean_dec_ref(v___x_2461_);
v___x_2463_ = 1;
if (v___x_2462_ == 0)
{
lean_object* v___x_2464_; 
lean_inc_ref(v_e_2455_);
v___x_2464_ = l_Lean_Meta_isConstructorApp_x3f(v_e_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2474_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2467_ = v___x_2464_;
v_isShared_2468_ = v_isSharedCheck_2474_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2464_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2474_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
if (lean_obj_tag(v_a_2465_) == 0)
{
lean_object* v___x_2469_; 
lean_del_object(v___x_2467_);
v___x_2469_ = l_Lean_Meta_isLitValue(v_e_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
return v___x_2469_;
}
else
{
lean_object* v___x_2470_; lean_object* v___x_2472_; 
lean_dec_ref_known(v_a_2465_, 1);
lean_dec_ref(v_e_2455_);
v___x_2470_ = lean_box(v___x_2463_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 0, v___x_2470_);
v___x_2472_ = v___x_2467_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec_ref(v_e_2455_);
v_a_2475_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2464_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2464_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
else
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
lean_dec_ref(v_e_2455_);
v___x_2483_ = lean_box(v___x_2463_);
v___x_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2483_);
return v___x_2484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg___boxed(lean_object* v_e_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(v_e_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike(lean_object* v_e_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(v_e_2492_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___boxed(lean_object* v_e_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike(v_e_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
lean_dec(v_a_2513_);
lean_dec_ref(v_a_2512_);
lean_dec(v_a_2511_);
lean_dec_ref(v_a_2510_);
lean_dec(v_a_2509_);
lean_dec_ref(v_a_2508_);
lean_dec(v_a_2507_);
lean_dec(v_a_2506_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(lean_object* v_e_2518_, lean_object* v_pat_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_){
_start:
{
lean_object* v___x_2531_; uint8_t v_modified_2532_; 
v___x_2531_ = l_Lean_Expr_getAppFn(v_pat_2519_);
v_modified_2532_ = l_Lean_Expr_isMVar(v___x_2531_);
lean_dec_ref(v___x_2531_);
if (v_modified_2532_ == 0)
{
lean_object* v___x_2533_; 
lean_inc_ref(v_e_2518_);
v___x_2533_ = l_Lean_Meta_Grind_getRootENode___redArg(v_e_2518_, v_a_2520_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2634_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2536_ = v___x_2533_;
v_isShared_2537_ = v_isSharedCheck_2634_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2533_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2634_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
uint8_t v_ctor_2538_; 
v_ctor_2538_ = lean_ctor_get_uint8(v_a_2534_, sizeof(void*)*12 + 2);
if (v_ctor_2538_ == 0)
{
uint8_t v_interpreted_2539_; 
lean_dec_ref(v_pat_2519_);
v_interpreted_2539_ = lean_ctor_get_uint8(v_a_2534_, sizeof(void*)*12 + 1);
if (v_interpreted_2539_ == 0)
{
lean_object* v___x_2541_; 
lean_dec(v_a_2534_);
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 0, v_e_2518_);
v___x_2541_ = v___x_2536_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_e_2518_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
else
{
lean_object* v_self_2543_; lean_object* v___x_2545_; 
lean_dec_ref(v_e_2518_);
v_self_2543_ = lean_ctor_get(v_a_2534_, 0);
lean_inc_ref(v_self_2543_);
lean_dec(v_a_2534_);
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 0, v_self_2543_);
v___x_2545_ = v___x_2536_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_self_2543_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
else
{
lean_object* v_self_2547_; lean_object* v___x_2548_; 
lean_del_object(v___x_2536_);
lean_dec_ref(v_e_2518_);
v_self_2547_ = lean_ctor_get(v_a_2534_, 0);
lean_inc_ref_n(v_self_2547_, 2);
lean_dec(v_a_2534_);
v___x_2548_ = l_Lean_Meta_isConstructorApp_x3f(v_self_2547_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2625_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2551_ = v___x_2548_;
v_isShared_2552_ = v_isSharedCheck_2625_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2548_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2625_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
if (lean_obj_tag(v_a_2549_) == 1)
{
lean_object* v_val_2553_; lean_object* v___x_2554_; 
lean_del_object(v___x_2551_);
v_val_2553_ = lean_ctor_get(v_a_2549_, 0);
lean_inc(v_val_2553_);
lean_dec_ref_known(v_a_2549_, 1);
lean_inc_ref(v_pat_2519_);
v___x_2554_ = l_Lean_Meta_isConstructorApp_x3f(v_pat_2519_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2613_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2613_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2613_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
if (lean_obj_tag(v_a_2555_) == 1)
{
lean_object* v_toConstantVal_2559_; lean_object* v_val_2560_; lean_object* v_toConstantVal_2561_; lean_object* v_numParams_2562_; lean_object* v_numFields_2563_; lean_object* v_name_2564_; lean_object* v_name_2565_; uint8_t v___x_2566_; 
v_toConstantVal_2559_ = lean_ctor_get(v_val_2553_, 0);
lean_inc_ref(v_toConstantVal_2559_);
v_val_2560_ = lean_ctor_get(v_a_2555_, 0);
lean_inc(v_val_2560_);
lean_dec_ref_known(v_a_2555_, 1);
v_toConstantVal_2561_ = lean_ctor_get(v_val_2560_, 0);
lean_inc_ref(v_toConstantVal_2561_);
lean_dec(v_val_2560_);
v_numParams_2562_ = lean_ctor_get(v_val_2553_, 3);
lean_inc(v_numParams_2562_);
v_numFields_2563_ = lean_ctor_get(v_val_2553_, 4);
lean_inc(v_numFields_2563_);
lean_dec(v_val_2553_);
v_name_2564_ = lean_ctor_get(v_toConstantVal_2559_, 0);
lean_inc(v_name_2564_);
lean_dec_ref(v_toConstantVal_2559_);
v_name_2565_ = lean_ctor_get(v_toConstantVal_2561_, 0);
lean_inc(v_name_2565_);
lean_dec_ref(v_toConstantVal_2561_);
v___x_2566_ = lean_name_eq(v_name_2564_, v_name_2565_);
lean_dec(v_name_2565_);
lean_dec(v_name_2564_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2568_; 
lean_dec(v_numFields_2563_);
lean_dec(v_numParams_2562_);
lean_dec_ref(v_pat_2519_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v_self_2547_);
v___x_2568_ = v___x_2557_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_self_2547_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
else
{
lean_object* v___x_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2570_ = lean_nat_add(v_numParams_2562_, v_numFields_2563_);
lean_dec(v_numFields_2563_);
v___x_2571_ = l_Lean_Expr_getAppNumArgs(v_pat_2519_);
v___x_2572_ = lean_nat_dec_eq(v___x_2571_, v___x_2570_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2574_; 
lean_dec(v___x_2571_);
lean_dec(v___x_2570_);
lean_dec(v_numParams_2562_);
lean_dec_ref(v_pat_2519_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v_self_2547_);
v___x_2574_ = v___x_2557_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_self_2547_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
else
{
lean_object* v_nargs_2576_; lean_object* v_dummy_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
lean_del_object(v___x_2557_);
v_nargs_2576_ = l_Lean_Expr_getAppNumArgs(v_self_2547_);
v_dummy_2577_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0);
lean_inc(v_nargs_2576_);
v___x_2578_ = lean_mk_array(v_nargs_2576_, v_dummy_2577_);
v___x_2579_ = lean_unsigned_to_nat(1u);
v___x_2580_ = lean_nat_sub(v_nargs_2576_, v___x_2579_);
lean_dec(v_nargs_2576_);
lean_inc_ref(v_self_2547_);
v___x_2581_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_2547_, v___x_2578_, v___x_2580_);
v___x_2582_ = lean_box(v_modified_2532_);
v___x_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2581_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
lean_inc(v___x_2571_);
v___x_2584_ = lean_mk_array(v___x_2571_, v_dummy_2577_);
v___x_2585_ = lean_nat_sub(v___x_2571_, v___x_2579_);
lean_dec(v___x_2571_);
v___x_2586_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_pat_2519_, v___x_2584_, v___x_2585_);
v___x_2587_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v___x_2570_, v___x_2586_, v_numParams_2562_, v___x_2583_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
lean_dec_ref(v___x_2586_);
lean_dec(v___x_2570_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2601_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2601_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2601_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v_snd_2592_; uint8_t v___x_2593_; 
v_snd_2592_ = lean_ctor_get(v_a_2588_, 1);
v___x_2593_ = lean_unbox(v_snd_2592_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2595_; 
lean_dec(v_a_2588_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v_self_2547_);
v___x_2595_ = v___x_2590_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_self_2547_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
else
{
lean_object* v_fst_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
lean_del_object(v___x_2590_);
v_fst_2597_ = lean_ctor_get(v_a_2588_, 0);
lean_inc(v_fst_2597_);
lean_dec(v_a_2588_);
v___x_2598_ = l_Lean_Expr_getAppFn(v_self_2547_);
lean_dec_ref(v_self_2547_);
v___x_2599_ = l_Lean_mkAppN(v___x_2598_, v_fst_2597_);
lean_dec(v_fst_2597_);
v___x_2600_ = l_Lean_Meta_Sym_shareCommon(v___x_2599_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
return v___x_2600_;
}
}
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_dec_ref(v_self_2547_);
v_a_2602_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2587_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2587_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
}
}
else
{
lean_object* v___x_2611_; 
lean_dec(v_a_2555_);
lean_dec(v_val_2553_);
lean_dec_ref(v_pat_2519_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v_self_2547_);
v___x_2611_ = v___x_2557_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_self_2547_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec(v_val_2553_);
lean_dec_ref(v_self_2547_);
lean_dec_ref(v_pat_2519_);
v_a_2614_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2554_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2554_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
else
{
lean_object* v___x_2623_; 
lean_dec(v_a_2549_);
lean_dec_ref(v_pat_2519_);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v_self_2547_);
v___x_2623_ = v___x_2551_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_self_2547_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
lean_dec_ref(v_self_2547_);
lean_dec_ref(v_pat_2519_);
v_a_2626_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2548_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2548_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
lean_dec_ref(v_pat_2519_);
lean_dec_ref(v_e_2518_);
v_a_2635_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2533_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2533_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
else
{
lean_object* v___x_2643_; 
lean_dec_ref(v_pat_2519_);
v___x_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2643_, 0, v_e_2518_);
return v___x_2643_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(lean_object* v_upperBound_2644_, lean_object* v___x_2645_, lean_object* v_a_2646_, lean_object* v_b_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v_a_2660_; uint8_t v_modified_2664_; 
v_modified_2664_ = lean_nat_dec_lt(v_a_2646_, v_upperBound_2644_);
if (v_modified_2664_ == 0)
{
lean_object* v___x_2665_; 
lean_dec(v_a_2646_);
v___x_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2665_, 0, v_b_2647_);
return v___x_2665_;
}
else
{
lean_object* v_fst_2666_; lean_object* v_snd_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2695_; 
v_fst_2666_ = lean_ctor_get(v_b_2647_, 0);
v_snd_2667_ = lean_ctor_get(v_b_2647_, 1);
v_isSharedCheck_2695_ = !lean_is_exclusive(v_b_2647_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2669_ = v_b_2647_;
v_isShared_2670_ = v_isSharedCheck_2695_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_snd_2667_);
lean_inc(v_fst_2666_);
lean_dec(v_b_2647_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2695_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2671_ = l_Lean_instInhabitedExpr;
v___x_2672_ = lean_array_get_borrowed(v___x_2671_, v_fst_2666_, v_a_2646_);
v___x_2673_ = lean_array_get_borrowed(v___x_2671_, v___x_2645_, v_a_2646_);
lean_inc(v___x_2673_);
lean_inc(v___x_2672_);
v___x_2674_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v___x_2672_, v___x_2673_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; size_t v___x_2676_; size_t v___x_2677_; uint8_t v___x_2678_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_a_2675_);
lean_dec_ref_known(v___x_2674_, 1);
v___x_2676_ = lean_ptr_addr(v___x_2672_);
v___x_2677_ = lean_ptr_addr(v_a_2675_);
v___x_2678_ = lean_usize_dec_eq(v___x_2676_, v___x_2677_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2682_; 
lean_dec(v_snd_2667_);
v___x_2679_ = lean_array_set(v_fst_2666_, v_a_2646_, v_a_2675_);
v___x_2680_ = lean_box(v_modified_2664_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 1, v___x_2680_);
lean_ctor_set(v___x_2669_, 0, v___x_2679_);
v___x_2682_ = v___x_2669_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2679_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
v_a_2660_ = v___x_2682_;
goto v___jp_2659_;
}
}
else
{
lean_object* v___x_2685_; 
lean_dec(v_a_2675_);
if (v_isShared_2670_ == 0)
{
v___x_2685_ = v___x_2669_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_fst_2666_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v_snd_2667_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
v_a_2660_ = v___x_2685_;
goto v___jp_2659_;
}
}
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
lean_del_object(v___x_2669_);
lean_dec(v_snd_2667_);
lean_dec(v_fst_2666_);
lean_dec(v_a_2646_);
v_a_2687_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2674_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2674_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
}
v___jp_2659_:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = lean_unsigned_to_nat(1u);
v___x_2662_ = lean_nat_add(v_a_2646_, v___x_2661_);
lean_dec(v_a_2646_);
v_a_2646_ = v___x_2662_;
v_b_2647_ = v_a_2660_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg___boxed(lean_object* v_upperBound_2696_, lean_object* v___x_2697_, lean_object* v_a_2698_, lean_object* v_b_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2696_, v___x_2697_, v_a_2698_, v_b_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec_ref(v___x_2697_);
lean_dec(v_upperBound_2696_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go___boxed(lean_object* v_e_2712_, lean_object* v_pat_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_e_2712_, v_pat_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec(v_a_2714_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(lean_object* v_upperBound_2726_, lean_object* v___x_2727_, lean_object* v_inst_2728_, lean_object* v_R_2729_, lean_object* v_a_2730_, lean_object* v_b_2731_, lean_object* v_c_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2726_, v___x_2727_, v_a_2730_, v_b_2731_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_2745_ = _args[0];
lean_object* v___x_2746_ = _args[1];
lean_object* v_inst_2747_ = _args[2];
lean_object* v_R_2748_ = _args[3];
lean_object* v_a_2749_ = _args[4];
lean_object* v_b_2750_ = _args[5];
lean_object* v_c_2751_ = _args[6];
lean_object* v___y_2752_ = _args[7];
lean_object* v___y_2753_ = _args[8];
lean_object* v___y_2754_ = _args[9];
lean_object* v___y_2755_ = _args[10];
lean_object* v___y_2756_ = _args[11];
lean_object* v___y_2757_ = _args[12];
lean_object* v___y_2758_ = _args[13];
lean_object* v___y_2759_ = _args[14];
lean_object* v___y_2760_ = _args[15];
lean_object* v___y_2761_ = _args[16];
lean_object* v___y_2762_ = _args[17];
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(v_upperBound_2745_, v___x_2746_, v_inst_2747_, v_R_2748_, v_a_2749_, v_b_2750_, v_c_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___x_2746_);
lean_dec(v_upperBound_2745_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(lean_object* v_e_2764_, lean_object* v___y_2765_){
_start:
{
uint8_t v___x_2767_; 
v___x_2767_ = l_Lean_Expr_hasMVar(v_e_2764_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2768_; 
v___x_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2768_, 0, v_e_2764_);
return v___x_2768_;
}
else
{
lean_object* v___x_2769_; lean_object* v_mctx_2770_; lean_object* v___x_2771_; lean_object* v_fst_2772_; lean_object* v_snd_2773_; lean_object* v___x_2774_; lean_object* v_cache_2775_; lean_object* v_zetaDeltaFVarIds_2776_; lean_object* v_postponed_2777_; lean_object* v_diag_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2787_; 
v___x_2769_ = lean_st_ref_get(v___y_2765_);
v_mctx_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc_ref(v_mctx_2770_);
lean_dec(v___x_2769_);
v___x_2771_ = l_Lean_instantiateMVarsCore(v_mctx_2770_, v_e_2764_);
v_fst_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_fst_2772_);
v_snd_2773_ = lean_ctor_get(v___x_2771_, 1);
lean_inc(v_snd_2773_);
lean_dec_ref(v___x_2771_);
v___x_2774_ = lean_st_ref_take(v___y_2765_);
v_cache_2775_ = lean_ctor_get(v___x_2774_, 1);
v_zetaDeltaFVarIds_2776_ = lean_ctor_get(v___x_2774_, 2);
v_postponed_2777_ = lean_ctor_get(v___x_2774_, 3);
v_diag_2778_ = lean_ctor_get(v___x_2774_, 4);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2787_ == 0)
{
lean_object* v_unused_2788_; 
v_unused_2788_ = lean_ctor_get(v___x_2774_, 0);
lean_dec(v_unused_2788_);
v___x_2780_ = v___x_2774_;
v_isShared_2781_ = v_isSharedCheck_2787_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_diag_2778_);
lean_inc(v_postponed_2777_);
lean_inc(v_zetaDeltaFVarIds_2776_);
lean_inc(v_cache_2775_);
lean_dec(v___x_2774_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2787_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v_snd_2773_);
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_snd_2773_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_cache_2775_);
lean_ctor_set(v_reuseFailAlloc_2786_, 2, v_zetaDeltaFVarIds_2776_);
lean_ctor_set(v_reuseFailAlloc_2786_, 3, v_postponed_2777_);
lean_ctor_set(v_reuseFailAlloc_2786_, 4, v_diag_2778_);
v___x_2783_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = lean_st_ref_put(v___y_2765_, v___x_2783_);
v___x_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2785_, 0, v_fst_2772_);
return v___x_2785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg___boxed(lean_object* v_e_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v_e_2789_, v___y_2790_);
lean_dec(v___y_2790_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(lean_object* v_e_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v_e_2793_, v___y_2801_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___boxed(lean_object* v_e_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(v_e_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec(v___y_2807_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0(lean_object* v_k_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v___x_2831_; 
lean_inc(v___y_2825_);
lean_inc_ref(v___y_2824_);
lean_inc(v___y_2823_);
lean_inc_ref(v___y_2822_);
lean_inc(v___y_2821_);
lean_inc(v___y_2820_);
v___x_2831_ = lean_apply_11(v_k_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, lean_box(0));
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0___boxed(lean_object* v_k_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0(v_k_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(lean_object* v_k_2845_, uint8_t v_allowLevelAssignments_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v___f_2858_; lean_object* v___x_2859_; 
lean_inc(v___y_2852_);
lean_inc_ref(v___y_2851_);
lean_inc(v___y_2850_);
lean_inc_ref(v___y_2849_);
lean_inc(v___y_2848_);
lean_inc(v___y_2847_);
v___f_2858_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_2858_, 0, v_k_2845_);
lean_closure_set(v___f_2858_, 1, v___y_2847_);
lean_closure_set(v___f_2858_, 2, v___y_2848_);
lean_closure_set(v___f_2858_, 3, v___y_2849_);
lean_closure_set(v___f_2858_, 4, v___y_2850_);
lean_closure_set(v___f_2858_, 5, v___y_2851_);
lean_closure_set(v___f_2858_, 6, v___y_2852_);
v___x_2859_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2846_, v___f_2858_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
if (lean_obj_tag(v___x_2859_) == 0)
{
return v___x_2859_;
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2859_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2859_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___boxed(lean_object* v_k_2868_, lean_object* v_allowLevelAssignments_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2881_; lean_object* v_res_2882_; 
v_allowLevelAssignments_boxed_2881_ = lean_unbox(v_allowLevelAssignments_2869_);
v_res_2882_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(v_k_2868_, v_allowLevelAssignments_boxed_2881_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec(v___y_2870_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(lean_object* v_00_u03b1_2883_, lean_object* v_k_2884_, uint8_t v_allowLevelAssignments_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(v_k_2884_, v_allowLevelAssignments_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___boxed(lean_object* v_00_u03b1_2898_, lean_object* v_k_2899_, lean_object* v_allowLevelAssignments_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2912_; lean_object* v_res_2913_; 
v_allowLevelAssignments_boxed_2912_ = lean_unbox(v_allowLevelAssignments_2900_);
v_res_2913_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_00_u03b1_2898_, v_k_2899_, v_allowLevelAssignments_boxed_2912_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
lean_dec(v___y_2902_);
lean_dec(v___y_2901_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0(lean_object* v_cls_2914_, lean_object* v_____do__lift_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v_toCold_2927_; lean_object* v_options_2928_; uint8_t v_hasTrace_2929_; 
v_toCold_2927_ = lean_ctor_get(v___y_2924_, 0);
v_options_2928_ = lean_ctor_get(v_toCold_2927_, 2);
v_hasTrace_2929_ = lean_ctor_get_uint8(v_options_2928_, sizeof(void*)*1);
if (v_hasTrace_2929_ == 0)
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
lean_dec(v_cls_2914_);
v___x_2930_ = lean_box(v_hasTrace_2929_);
v___x_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
return v___x_2931_;
}
else
{
lean_object* v___x_2932_; lean_object* v___x_2933_; uint8_t v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2932_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5));
v___x_2933_ = l_Lean_Name_append(v___x_2932_, v_cls_2914_);
v___x_2934_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2915_, v_options_2928_, v___x_2933_);
lean_dec(v___x_2933_);
v___x_2935_ = lean_box(v___x_2934_);
v___x_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2935_);
return v___x_2936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed(lean_object* v_cls_2937_, lean_object* v_____do__lift_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l_Lean_Meta_Grind_tryToProveFalse___lam__0(v_cls_2937_, v_____do__lift_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v_____do__lift_2938_);
return v_res_2950_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3(void){
_start:
{
lean_object* v_cls_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v_cls_2959_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1));
v___x_2960_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5));
v___x_2961_ = l_Lean_Name_append(v___x_2960_, v_cls_2959_);
return v___x_2961_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5(void){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__4));
v___x_2964_ = l_Lean_stringToMessageData(v___x_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(lean_object* v_as_2965_, size_t v_sz_2966_, size_t v_i_2967_, lean_object* v_b_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
lean_object* v_a_2981_; uint8_t v___x_2985_; 
v___x_2985_ = lean_usize_dec_lt(v_i_2967_, v_sz_2966_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; 
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v_b_2968_);
return v___x_2986_;
}
else
{
lean_object* v_snd_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3242_; 
v_snd_2987_ = lean_ctor_get(v_b_2968_, 1);
v_isSharedCheck_3242_ = !lean_is_exclusive(v_b_2968_);
if (v_isSharedCheck_3242_ == 0)
{
lean_object* v_unused_3243_; 
v_unused_3243_ = lean_ctor_get(v_b_2968_, 0);
lean_dec(v_unused_3243_);
v___x_2989_ = v_b_2968_;
v_isShared_2990_ = v_isSharedCheck_3242_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_snd_2987_);
lean_dec(v_b_2968_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3242_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v_array_2991_; lean_object* v_start_2992_; lean_object* v_stop_2993_; lean_object* v___x_2994_; uint8_t v___x_2995_; 
v_array_2991_ = lean_ctor_get(v_snd_2987_, 0);
v_start_2992_ = lean_ctor_get(v_snd_2987_, 1);
v_stop_2993_ = lean_ctor_get(v_snd_2987_, 2);
v___x_2994_ = lean_box(0);
v___x_2995_ = lean_nat_dec_lt(v_start_2992_, v_stop_2993_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2997_; 
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v___x_2994_);
v___x_2997_ = v___x_2989_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2994_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v_snd_2987_);
v___x_2997_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v___x_2998_; 
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
return v___x_2998_;
}
}
else
{
lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3238_; 
lean_inc(v_stop_2993_);
lean_inc(v_start_2992_);
lean_inc_ref(v_array_2991_);
v_isSharedCheck_3238_ = !lean_is_exclusive(v_snd_2987_);
if (v_isSharedCheck_3238_ == 0)
{
lean_object* v_unused_3239_; lean_object* v_unused_3240_; lean_object* v_unused_3241_; 
v_unused_3239_ = lean_ctor_get(v_snd_2987_, 2);
lean_dec(v_unused_3239_);
v_unused_3240_ = lean_ctor_get(v_snd_2987_, 1);
lean_dec(v_unused_3240_);
v_unused_3241_ = lean_ctor_get(v_snd_2987_, 0);
lean_dec(v_unused_3241_);
v___x_3001_ = v_snd_2987_;
v_isShared_3002_ = v_isSharedCheck_3238_;
goto v_resetjp_3000_;
}
else
{
lean_dec(v_snd_2987_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3238_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3007_; 
v___x_3003_ = lean_array_fget(v_array_2991_, v_start_2992_);
v___x_3004_ = lean_unsigned_to_nat(1u);
v___x_3005_ = lean_nat_add(v_start_2992_, v___x_3004_);
lean_dec(v_start_2992_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 1, v___x_3005_);
v___x_3007_ = v___x_3001_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_array_2991_);
lean_ctor_set(v_reuseFailAlloc_3237_, 1, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3237_, 2, v_stop_2993_);
v___x_3007_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
uint8_t v___x_3008_; 
v___x_3008_ = lean_unbox(v___x_3003_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3010_; 
lean_dec(v___x_3003_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 1, v___x_3007_);
lean_ctor_set(v___x_2989_, 0, v___x_2994_);
v___x_3010_ = v___x_2989_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_2994_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v___x_3007_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
v_a_2981_ = v___x_3010_;
goto v___jp_2980_;
}
}
else
{
lean_object* v_cls_3012_; lean_object* v_a_3013_; lean_object* v_____x_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___x_3051_; 
v_cls_3012_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1));
v_a_3013_ = lean_array_uget_borrowed(v_as_2965_, v_i_2967_);
lean_inc(v___y_2978_);
lean_inc_ref(v___y_2977_);
lean_inc(v___y_2976_);
lean_inc_ref(v___y_2975_);
lean_inc(v_a_3013_);
v___x_3051_ = lean_infer_type(v_a_3013_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3228_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3054_ = v___x_3051_;
v_isShared_3055_ = v_isSharedCheck_3228_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3051_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3228_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3056_; 
v___x_3056_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_a_3052_);
lean_dec(v_a_3052_);
if (lean_obj_tag(v___x_3056_) == 1)
{
lean_object* v_val_3057_; lean_object* v_snd_3058_; lean_object* v_fst_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3222_; 
lean_del_object(v___x_3054_);
v_val_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_val_3057_);
lean_dec_ref_known(v___x_3056_, 1);
v_snd_3058_ = lean_ctor_get(v_val_3057_, 1);
v_fst_3059_ = lean_ctor_get(v_val_3057_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v_val_3057_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3061_ = v_val_3057_;
v_isShared_3062_ = v_isSharedCheck_3222_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_snd_3058_);
lean_inc(v_fst_3059_);
lean_dec(v_val_3057_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3222_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v_fst_3063_; lean_object* v_snd_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3221_; 
v_fst_3063_ = lean_ctor_get(v_snd_3058_, 0);
v_snd_3064_ = lean_ctor_get(v_snd_3058_, 1);
v_isSharedCheck_3221_ = !lean_is_exclusive(v_snd_3058_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3066_ = v_snd_3058_;
v_isShared_3067_ = v_isSharedCheck_3221_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_snd_3064_);
lean_inc(v_fst_3063_);
lean_dec(v_snd_3058_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3221_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
uint8_t v___y_3069_; lean_object* v_lhs_x27_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3102_; uint8_t v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; uint8_t v___y_3160_; lean_object* v___y_3161_; uint8_t v___y_3196_; 
if (lean_obj_tag(v_fst_3059_) == 0)
{
uint8_t v___x_3219_; 
lean_dec(v___x_3003_);
v___x_3219_ = 0;
v___y_3196_ = v___x_3219_;
goto v___jp_3195_;
}
else
{
uint8_t v___x_3220_; 
lean_dec_ref_known(v_fst_3059_, 1);
v___x_3220_ = lean_unbox(v___x_3003_);
lean_dec(v___x_3003_);
v___y_3196_ = v___x_3220_;
goto v___jp_3195_;
}
v___jp_3068_:
{
if (v___y_3069_ == 0)
{
lean_object* v___x_3081_; 
v___x_3081_ = l_Lean_Meta_Grind_proveEq_x3f(v_fst_3063_, v_lhs_x27_3070_, v___y_3069_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_a_3082_);
lean_dec_ref_known(v___x_3081_, 1);
v_____x_3015_ = v_a_3082_;
v___y_3016_ = v___y_3077_;
v___y_3017_ = v___y_3078_;
v___y_3018_ = v___y_3079_;
v___y_3019_ = v___y_3080_;
goto v___jp_3014_;
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_dec_ref(v___x_3007_);
lean_del_object(v___x_2989_);
v_a_3083_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3081_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3081_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
else
{
lean_object* v___x_3091_; 
v___x_3091_ = l_Lean_Meta_Grind_proveHEq_x3f(v_fst_3063_, v_lhs_x27_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc(v_a_3092_);
lean_dec_ref_known(v___x_3091_, 1);
v_____x_3015_ = v_a_3092_;
v___y_3016_ = v___y_3077_;
v___y_3017_ = v___y_3078_;
v___y_3018_ = v___y_3079_;
v___y_3019_ = v___y_3080_;
goto v___jp_3014_;
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_dec_ref(v___x_3007_);
lean_del_object(v___x_2989_);
v_a_3093_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3091_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3091_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
}
v___jp_3101_:
{
lean_object* v___x_3115_; 
lean_inc_ref(v___y_3104_);
v___x_3115_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(v___y_3104_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3150_; 
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3118_ = v___x_3115_;
v_isShared_3119_ = v_isSharedCheck_3150_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3115_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3150_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
uint8_t v___x_3120_; 
v___x_3120_ = lean_unbox(v_a_3116_);
lean_dec(v_a_3116_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; lean_object* v___x_3123_; 
lean_dec_ref(v___y_3104_);
lean_dec_ref(v___y_3102_);
lean_dec(v_fst_3063_);
lean_del_object(v___x_2989_);
v___x_3121_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 1, v___x_3007_);
lean_ctor_set(v___x_3066_, 0, v___x_3121_);
v___x_3123_ = v___x_3066_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3121_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v___x_3007_);
v___x_3123_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
lean_object* v___x_3125_; 
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v___x_3123_);
v___x_3125_ = v___x_3118_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3123_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
else
{
lean_object* v___x_3128_; 
lean_del_object(v___x_3118_);
lean_inc_ref(v___y_3102_);
v___x_3128_ = l_Lean_Meta_isDefEqD(v___y_3102_, v___y_3104_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3141_; 
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3131_ = v___x_3128_;
v_isShared_3132_ = v_isSharedCheck_3141_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3128_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3141_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
uint8_t v___x_3133_; 
v___x_3133_ = lean_unbox(v_a_3129_);
lean_dec(v_a_3129_);
if (v___x_3133_ == 0)
{
lean_object* v___x_3134_; lean_object* v___x_3136_; 
lean_dec_ref(v___y_3102_);
lean_dec(v_fst_3063_);
lean_del_object(v___x_2989_);
v___x_3134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 1, v___x_3007_);
lean_ctor_set(v___x_3066_, 0, v___x_3134_);
v___x_3136_ = v___x_3066_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3134_);
lean_ctor_set(v_reuseFailAlloc_3140_, 1, v___x_3007_);
v___x_3136_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3138_; 
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 0, v___x_3136_);
v___x_3138_ = v___x_3131_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_3136_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
else
{
lean_del_object(v___x_3131_);
lean_del_object(v___x_3066_);
v___y_3069_ = v___y_3103_;
v_lhs_x27_3070_ = v___y_3102_;
v___y_3071_ = v___y_3105_;
v___y_3072_ = v___y_3106_;
v___y_3073_ = v___y_3107_;
v___y_3074_ = v___y_3108_;
v___y_3075_ = v___y_3109_;
v___y_3076_ = v___y_3110_;
v___y_3077_ = v___y_3111_;
v___y_3078_ = v___y_3112_;
v___y_3079_ = v___y_3113_;
v___y_3080_ = v___y_3114_;
goto v___jp_3068_;
}
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_dec_ref(v___y_3102_);
lean_del_object(v___x_3066_);
lean_dec(v_fst_3063_);
lean_dec_ref(v___x_3007_);
lean_del_object(v___x_2989_);
v_a_3142_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3128_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3128_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
}
}
else
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3158_; 
lean_dec_ref(v___y_3104_);
lean_dec_ref(v___y_3102_);
lean_del_object(v___x_3066_);
lean_dec(v_fst_3063_);
lean_dec_ref(v___x_3007_);
lean_del_object(v___x_2989_);
v_a_3151_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3153_ = v___x_3115_;
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3115_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3154_ == 0)
{
v___x_3156_ = v___x_3153_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_a_3151_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
}
v___jp_3159_:
{
lean_object* v___x_3162_; 
lean_inc_ref(v___y_3161_);
lean_inc(v_fst_3063_);
v___x_3162_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_fst_3063_, v___y_3161_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_toCold_3163_; lean_object* v_options_3164_; uint8_t v_hasTrace_3165_; 
v_toCold_3163_ = lean_ctor_get(v___y_2977_, 0);
v_options_3164_ = lean_ctor_get(v_toCold_3163_, 2);
v_hasTrace_3165_ = lean_ctor_get_uint8(v_options_3164_, sizeof(void*)*1);
if (v_hasTrace_3165_ == 0)
{
lean_object* v_a_3166_; 
lean_del_object(v___x_3061_);
v_a_3166_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3166_);
lean_dec_ref_known(v___x_3162_, 1);
v___y_3102_ = v_a_3166_;
v___y_3103_ = v___y_3160_;
v___y_3104_ = v___y_3161_;
v___y_3105_ = v___y_2969_;
v___y_3106_ = v___y_2970_;
v___y_3107_ = v___y_2971_;
v___y_3108_ = v___y_2972_;
v___y_3109_ = v___y_2973_;
v___y_3110_ = v___y_2974_;
v___y_3111_ = v___y_2975_;
v___y_3112_ = v___y_2976_;
v___y_3113_ = v___y_2977_;
v___y_3114_ = v___y_2978_;
goto v___jp_3101_;
}
else
{
lean_object* v_a_3167_; lean_object* v_inheritedTraceOptions_3168_; lean_object* v___x_3169_; uint8_t v___x_3170_; 
v_a_3167_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3167_);
lean_dec_ref_known(v___x_3162_, 1);
v_inheritedTraceOptions_3168_ = lean_ctor_get(v_toCold_3163_, 11);
v___x_3169_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3);
v___x_3170_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3168_, v_options_3164_, v___x_3169_);
if (v___x_3170_ == 0)
{
lean_del_object(v___x_3061_);
v___y_3102_ = v_a_3167_;
v___y_3103_ = v___y_3160_;
v___y_3104_ = v___y_3161_;
v___y_3105_ = v___y_2969_;
v___y_3106_ = v___y_2970_;
v___y_3107_ = v___y_2971_;
v___y_3108_ = v___y_2972_;
v___y_3109_ = v___y_2973_;
v___y_3110_ = v___y_2974_;
v___y_3111_ = v___y_2975_;
v___y_3112_ = v___y_2976_;
v___y_3113_ = v___y_2977_;
v___y_3114_ = v___y_2978_;
goto v___jp_3101_;
}
else
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3174_; 
lean_inc(v_a_3167_);
v___x_3171_ = l_Lean_MessageData_ofExpr(v_a_3167_);
v___x_3172_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5);
if (v_isShared_3062_ == 0)
{
lean_ctor_set_tag(v___x_3061_, 7);
lean_ctor_set(v___x_3061_, 1, v___x_3172_);
lean_ctor_set(v___x_3061_, 0, v___x_3171_);
v___x_3174_ = v___x_3061_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v___x_3171_);
lean_ctor_set(v_reuseFailAlloc_3186_, 1, v___x_3172_);
v___x_3174_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
lean_inc_ref(v___y_3161_);
v___x_3175_ = l_Lean_MessageData_ofExpr(v___y_3161_);
v___x_3176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3174_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3012_, v___x_3176_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_dec_ref_known(v___x_3177_, 1);
v___y_3102_ = v_a_3167_;
v___y_3103_ = v___y_3160_;
v___y_3104_ = v___y_3161_;
v___y_3105_ = v___y_2969_;
v___y_3106_ = v___y_2970_;
v___y_3107_ = v___y_2971_;
v___y_3108_ = v___y_2972_;
v___y_3109_ = v___y_2973_;
v___y_3110_ = v___y_2974_;
v___y_3111_ = v___y_2975_;
v___y_3112_ = v___y_2976_;
v___y_3113_ = v___y_2977_;
v___y_3114_ = v___y_2978_;
goto v___jp_3101_;
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_dec(v_a_3167_);
lean_dec_ref(v___y_3161_);
lean_del_object(v___x_3066_);
lean_dec(v_fst_3063_);
lean_dec_ref(v___x_3007_);
lean_del_object(v___x_2989_);
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3177_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3177_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
if (v_isShared_3181_ == 0)
{
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_dec_ref(v___y_3161_);
lean_del_object(v___x_3066_);
lean_dec(v_fst_3063_);
lean_del_object(v___x_3061_);
lean_dec_ref(v___x_3007_);
lean_del_object(v___x_2989_);
v_a_3187_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3162_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3162_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
v___jp_3195_:
{
lean_object* v___x_3197_; 
v___x_3197_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v_snd_3064_, v___y_2976_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_a_3198_; uint8_t v___x_3199_; 
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_a_3198_);
lean_dec_ref_known(v___x_3197_, 1);
v___x_3199_ = l_Lean_Expr_hasExprMVar(v_a_3198_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_Meta_Grind_isEqv___redArg(v_fst_3063_, v_a_3198_, v___y_2969_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; uint8_t v___x_3202_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_a_3201_);
lean_dec_ref_known(v___x_3200_, 1);
v___x_3202_ = lean_unbox(v_a_3201_);
lean_dec(v_a_3201_);
if (v___x_3202_ == 0)
{
v___y_3160_ = v___y_3196_;
v___y_3161_ = v_a_3198_;
goto v___jp_3159_;
}
else
{
lean_del_object(v___x_3066_);
lean_del_object(v___x_3061_);
v___y_3069_ = v___y_3196_;
v_lhs_x27_3070_ = v_a_3198_;
v___y_3071_ = v___y_2969_;
v___y_3072_ = v___y_2970_;
v___y_3073_ = v___y_2971_;
v___y_3074_ = v___y_2972_;
v___y_3075_ = v___y_2973_;
v___y_3076_ = v___y_2974_;
v___y_3077_ = v___y_2975_;
v___y_3078_ = v___y_2976_;
v___y_3079_ = v___y_2977_;
v___y_3080_ = v___y_2978_;
goto v___jp_3068_;
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
lean_dec(v_a_3198_);
lean_del_object(v___x_3066_);
lean_dec(v_fst_3063_);
lean_del_object(v___x_3061_);
lean_dec_ref(v___x_3007_);
lean_del_object(v___x_2989_);
v_a_3203_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3200_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3200_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
else
{
v___y_3160_ = v___y_3196_;
v___y_3161_ = v_a_3198_;
goto v___jp_3159_;
}
}
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_del_object(v___x_3066_);
lean_dec(v_fst_3063_);
lean_del_object(v___x_3061_);
lean_dec_ref(v___x_3007_);
lean_del_object(v___x_2989_);
v_a_3211_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3197_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3197_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3226_; 
lean_dec(v___x_3056_);
lean_dec(v___x_3003_);
lean_del_object(v___x_2989_);
v___x_3223_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
v___x_3224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
lean_ctor_set(v___x_3224_, 1, v___x_3007_);
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 0, v___x_3224_);
v___x_3226_ = v___x_3054_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3224_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
else
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
lean_dec_ref(v___x_3007_);
lean_dec(v___x_3003_);
lean_del_object(v___x_2989_);
v_a_3229_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___x_3051_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3051_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3234_; 
if (v_isShared_3232_ == 0)
{
v___x_3234_ = v___x_3231_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3229_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
v___jp_3014_:
{
if (lean_obj_tag(v_____x_3015_) == 1)
{
lean_object* v_val_3020_; lean_object* v___x_3021_; 
v_val_3020_ = lean_ctor_get(v_____x_3015_, 0);
lean_inc(v_val_3020_);
lean_dec_ref_known(v_____x_3015_, 1);
lean_inc(v_a_3013_);
v___x_3021_ = l_Lean_Meta_isExprDefEq(v_a_3013_, v_val_3020_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3037_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3024_ = v___x_3021_;
v_isShared_3025_ = v_isSharedCheck_3037_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3021_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3037_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
uint8_t v___x_3026_; 
v___x_3026_ = lean_unbox(v_a_3022_);
lean_dec(v_a_3022_);
if (v___x_3026_ == 0)
{
lean_object* v___x_3027_; lean_object* v___x_3029_; 
v___x_3027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 1, v___x_3007_);
lean_ctor_set(v___x_2989_, 0, v___x_3027_);
v___x_3029_ = v___x_2989_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v___x_3027_);
lean_ctor_set(v_reuseFailAlloc_3033_, 1, v___x_3007_);
v___x_3029_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
lean_object* v___x_3031_; 
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v___x_3029_);
v___x_3031_ = v___x_3024_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3029_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
else
{
lean_object* v___x_3035_; 
lean_del_object(v___x_3024_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 1, v___x_3007_);
lean_ctor_set(v___x_2989_, 0, v___x_2994_);
v___x_3035_ = v___x_2989_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_2994_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v___x_3007_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
v_a_2981_ = v___x_3035_;
goto v___jp_2980_;
}
}
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec_ref(v___x_3007_);
lean_del_object(v___x_2989_);
v_a_3038_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3021_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3021_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
else
{
lean_object* v___x_3046_; lean_object* v___x_3048_; 
lean_dec(v_____x_3015_);
v___x_3046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 1, v___x_3007_);
lean_ctor_set(v___x_2989_, 0, v___x_3046_);
v___x_3048_ = v___x_2989_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3046_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v___x_3007_);
v___x_3048_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3049_; 
v___x_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
return v___x_3049_;
}
}
}
}
}
}
}
}
}
v___jp_2980_:
{
size_t v___x_2982_; size_t v___x_2983_; 
v___x_2982_ = ((size_t)1ULL);
v___x_2983_ = lean_usize_add(v_i_2967_, v___x_2982_);
v_i_2967_ = v___x_2983_;
v_b_2968_ = v_a_2981_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___boxed(lean_object* v_as_3244_, lean_object* v_sz_3245_, lean_object* v_i_3246_, lean_object* v_b_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
size_t v_sz_boxed_3259_; size_t v_i_boxed_3260_; lean_object* v_res_3261_; 
v_sz_boxed_3259_ = lean_unbox_usize(v_sz_3245_);
lean_dec(v_sz_3245_);
v_i_boxed_3260_ = lean_unbox_usize(v_i_3246_);
lean_dec(v_i_3246_);
v_res_3261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(v_as_3244_, v_sz_boxed_3259_, v_i_boxed_3260_, v_b_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v_as_3244_);
return v_res_3261_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3263_ = ((lean_object*)(l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__0));
v___x_3264_ = l_Lean_stringToMessageData(v___x_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1(lean_object* v_arg_3265_, uint8_t v___x_3266_, lean_object* v_e_3267_, lean_object* v___f_3268_, lean_object* v_cls_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v___x_3281_; 
lean_inc_ref(v_arg_3265_);
v___x_3281_ = l_Lean_Meta_forallMetaTelescope(v_arg_3265_, v___x_3266_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3282_; lean_object* v_fst_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3401_; 
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_a_3282_);
lean_dec_ref_known(v___x_3281_, 1);
v_fst_3283_ = lean_ctor_get(v_a_3282_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v_a_3282_);
if (v_isSharedCheck_3401_ == 0)
{
lean_object* v_unused_3402_; 
v_unused_3402_ = lean_ctor_get(v_a_3282_, 1);
lean_dec(v_unused_3402_);
v___x_3285_ = v_a_3282_;
v_isShared_3286_ = v_isSharedCheck_3401_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_fst_3283_);
lean_dec(v_a_3282_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3401_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3293_; 
v___x_3287_ = l_Lean_Meta_mkGenDiseqMask(v_arg_3265_);
lean_dec_ref(v_arg_3265_);
v___x_3288_ = lean_unsigned_to_nat(0u);
v___x_3289_ = lean_array_get_size(v___x_3287_);
v___x_3290_ = l_Array_toSubarray___redArg(v___x_3287_, v___x_3288_, v___x_3289_);
v___x_3291_ = lean_box(0);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 1, v___x_3290_);
lean_ctor_set(v___x_3285_, 0, v___x_3291_);
v___x_3293_ = v___x_3285_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3291_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v___x_3290_);
v___x_3293_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
size_t v_sz_3294_; size_t v___x_3295_; lean_object* v___x_3296_; 
v_sz_3294_ = lean_array_size(v_fst_3283_);
v___x_3295_ = ((size_t)0ULL);
v___x_3296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(v_fst_3283_, v_sz_3294_, v___x_3295_, v___x_3293_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3391_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3299_ = v___x_3296_;
v_isShared_3300_ = v_isSharedCheck_3391_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3296_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3391_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v_fst_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3389_; 
v_fst_3301_ = lean_ctor_get(v_a_3297_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v_a_3297_);
if (v_isSharedCheck_3389_ == 0)
{
lean_object* v_unused_3390_; 
v_unused_3390_ = lean_ctor_get(v_a_3297_, 1);
lean_dec(v_unused_3390_);
v___x_3303_ = v_a_3297_;
v_isShared_3304_ = v_isSharedCheck_3389_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_fst_3301_);
lean_dec(v_a_3297_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3389_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
if (lean_obj_tag(v_fst_3301_) == 0)
{
lean_object* v___x_3305_; 
lean_del_object(v___x_3299_);
lean_inc_ref(v_e_3267_);
v___x_3305_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_3267_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3376_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_a_3306_);
lean_dec_ref_known(v___x_3305_, 1);
v___x_3307_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3267_, v_a_3306_);
v___x_3308_ = l_Lean_mkAppN(v___x_3307_, v_fst_3283_);
lean_dec(v_fst_3283_);
v___x_3309_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v___x_3308_, v___y_3277_);
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3312_ = v___x_3309_;
v_isShared_3313_ = v_isSharedCheck_3376_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3309_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3376_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3319_; 
lean_inc(v_a_3310_);
v___x_3319_ = l_Lean_Meta_hasAssignableMVar(v_a_3310_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3367_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3322_ = v___x_3319_;
v_isShared_3323_ = v_isSharedCheck_3367_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3319_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3367_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
uint8_t v___x_3324_; 
v___x_3324_ = lean_unbox(v_a_3320_);
lean_dec(v_a_3320_);
if (v___x_3324_ == 0)
{
lean_object* v_toCold_3325_; lean_object* v_inheritedTraceOptions_3326_; lean_object* v___x_3327_; 
lean_del_object(v___x_3322_);
v_toCold_3325_ = lean_ctor_get(v___y_3278_, 0);
v_inheritedTraceOptions_3326_ = lean_ctor_get(v_toCold_3325_, 11);
lean_inc(v___y_3279_);
lean_inc_ref(v___y_3278_);
lean_inc(v___y_3277_);
lean_inc_ref(v___y_3276_);
lean_inc(v___y_3275_);
lean_inc_ref(v___y_3274_);
lean_inc(v___y_3273_);
lean_inc_ref(v___y_3272_);
lean_inc(v___y_3271_);
lean_inc(v___y_3270_);
lean_inc_ref(v_inheritedTraceOptions_3326_);
v___x_3327_ = lean_apply_12(v___f_3268_, v_inheritedTraceOptions_3326_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, lean_box(0));
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; uint8_t v___x_3329_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_a_3328_);
lean_dec_ref_known(v___x_3327_, 1);
v___x_3329_ = lean_unbox(v_a_3328_);
lean_dec(v_a_3328_);
if (v___x_3329_ == 0)
{
lean_del_object(v___x_3303_);
lean_dec(v_cls_3269_);
goto v___jp_3314_;
}
else
{
lean_object* v___x_3330_; 
lean_inc(v___y_3279_);
lean_inc_ref(v___y_3278_);
lean_inc(v___y_3277_);
lean_inc_ref(v___y_3276_);
lean_inc(v_a_3310_);
v___x_3330_ = lean_infer_type(v_a_3310_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3335_; 
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_a_3331_);
lean_dec_ref_known(v___x_3330_, 1);
lean_inc(v_a_3310_);
v___x_3332_ = l_Lean_MessageData_ofExpr(v_a_3310_);
v___x_3333_ = lean_obj_once(&l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1, &l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1_once, _init_l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1);
if (v_isShared_3304_ == 0)
{
lean_ctor_set_tag(v___x_3303_, 7);
lean_ctor_set(v___x_3303_, 1, v___x_3333_);
lean_ctor_set(v___x_3303_, 0, v___x_3332_);
v___x_3335_ = v___x_3303_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3332_);
lean_ctor_set(v_reuseFailAlloc_3347_, 1, v___x_3333_);
v___x_3335_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3336_ = l_Lean_MessageData_ofExpr(v_a_3331_);
v___x_3337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3335_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
v___x_3338_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3269_, v___x_3337_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_dec_ref_known(v___x_3338_, 1);
goto v___jp_3314_;
}
else
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3346_; 
lean_del_object(v___x_3312_);
lean_dec(v_a_3310_);
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___x_3338_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3338_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3344_; 
if (v_isShared_3342_ == 0)
{
v___x_3344_ = v___x_3341_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3339_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
lean_del_object(v___x_3312_);
lean_dec(v_a_3310_);
lean_del_object(v___x_3303_);
lean_dec(v_cls_3269_);
v_a_3348_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3330_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3330_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
}
else
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3363_; 
lean_del_object(v___x_3312_);
lean_dec(v_a_3310_);
lean_del_object(v___x_3303_);
lean_dec(v_cls_3269_);
v_a_3356_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3358_ = v___x_3327_;
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3327_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3361_; 
if (v_isShared_3359_ == 0)
{
v___x_3361_ = v___x_3358_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
else
{
lean_object* v___x_3365_; 
lean_del_object(v___x_3312_);
lean_dec(v_a_3310_);
lean_del_object(v___x_3303_);
lean_dec(v_cls_3269_);
lean_dec_ref(v___f_3268_);
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 0, v___x_3291_);
v___x_3365_ = v___x_3322_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3291_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
}
else
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
lean_del_object(v___x_3312_);
lean_dec(v_a_3310_);
lean_del_object(v___x_3303_);
lean_dec(v_cls_3269_);
lean_dec_ref(v___f_3268_);
v_a_3368_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3370_ = v___x_3319_;
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3319_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3368_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
v___jp_3314_:
{
lean_object* v___x_3315_; lean_object* v___x_3317_; 
v___x_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3315_, 0, v_a_3310_);
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 0, v___x_3315_);
v___x_3317_ = v___x_3312_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3315_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_del_object(v___x_3303_);
lean_dec(v_fst_3283_);
lean_dec(v_cls_3269_);
lean_dec_ref(v___f_3268_);
lean_dec_ref(v_e_3267_);
v_a_3377_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3305_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3305_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
else
{
lean_object* v_val_3385_; lean_object* v___x_3387_; 
lean_del_object(v___x_3303_);
lean_dec(v_fst_3283_);
lean_dec(v_cls_3269_);
lean_dec_ref(v___f_3268_);
lean_dec_ref(v_e_3267_);
v_val_3385_ = lean_ctor_get(v_fst_3301_, 0);
lean_inc(v_val_3385_);
lean_dec_ref_known(v_fst_3301_, 1);
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 0, v_val_3385_);
v___x_3387_ = v___x_3299_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_val_3385_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
}
else
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
lean_dec(v_fst_3283_);
lean_dec(v_cls_3269_);
lean_dec_ref(v___f_3268_);
lean_dec_ref(v_e_3267_);
v_a_3392_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3394_ = v___x_3296_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3296_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
}
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_dec(v_cls_3269_);
lean_dec_ref(v___f_3268_);
lean_dec_ref(v_e_3267_);
lean_dec_ref(v_arg_3265_);
v_a_3403_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3281_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3281_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1___boxed(lean_object* v_arg_3411_, lean_object* v___x_3412_, lean_object* v_e_3413_, lean_object* v___f_3414_, lean_object* v_cls_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
uint8_t v___x_77358__boxed_3427_; lean_object* v_res_3428_; 
v___x_77358__boxed_3427_ = lean_unbox(v___x_3412_);
v_res_3428_ = l_Lean_Meta_Grind_tryToProveFalse___lam__1(v_arg_3411_, v___x_77358__boxed_3427_, v_e_3413_, v___f_3414_, v_cls_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec(v___y_3416_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse(lean_object* v_e_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_){
_start:
{
lean_object* v_toCold_3446_; lean_object* v_inheritedTraceOptions_3447_; lean_object* v_cls_3448_; lean_object* v___f_3449_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___x_3501_; lean_object* v_a_3502_; uint8_t v___x_3503_; 
v_toCold_3446_ = lean_ctor_get(v_a_3440_, 0);
v_inheritedTraceOptions_3447_ = lean_ctor_get(v_toCold_3446_, 11);
v_cls_3448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1));
v___f_3449_ = ((lean_object*)(l_Lean_Meta_Grind_tryToProveFalse___closed__0));
v___x_3501_ = l_Lean_Meta_Grind_tryToProveFalse___lam__0(v_cls_3448_, v_inheritedTraceOptions_3447_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_);
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref(v___x_3501_);
v___x_3503_ = lean_unbox(v_a_3502_);
lean_dec(v_a_3502_);
if (v___x_3503_ == 0)
{
v___y_3451_ = v_a_3432_;
v___y_3452_ = v_a_3433_;
v___y_3453_ = v_a_3434_;
v___y_3454_ = v_a_3435_;
v___y_3455_ = v_a_3436_;
v___y_3456_ = v_a_3437_;
v___y_3457_ = v_a_3438_;
v___y_3458_ = v_a_3439_;
v___y_3459_ = v_a_3440_;
v___y_3460_ = v_a_3441_;
goto v___jp_3450_;
}
else
{
lean_object* v___x_3504_; 
v___x_3504_ = l_Lean_Meta_Grind_updateLastTag(v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
lean_dec_ref_known(v___x_3504_, 1);
lean_inc_ref(v_e_3431_);
v___x_3505_ = l_Lean_MessageData_ofExpr(v_e_3431_);
v___x_3506_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3448_, v___x_3505_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_dec_ref_known(v___x_3506_, 1);
v___y_3451_ = v_a_3432_;
v___y_3452_ = v_a_3433_;
v___y_3453_ = v_a_3434_;
v___y_3454_ = v_a_3435_;
v___y_3455_ = v_a_3436_;
v___y_3456_ = v_a_3437_;
v___y_3457_ = v_a_3438_;
v___y_3458_ = v_a_3439_;
v___y_3459_ = v_a_3440_;
v___y_3460_ = v_a_3441_;
goto v___jp_3450_;
}
else
{
lean_dec_ref(v_e_3431_);
return v___x_3506_;
}
}
else
{
lean_dec_ref(v_e_3431_);
return v___x_3504_;
}
}
v___jp_3443_:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3444_ = lean_box(0);
v___x_3445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3444_);
return v___x_3445_;
}
v___jp_3450_:
{
lean_object* v___x_3461_; 
lean_inc_ref(v_e_3431_);
v___x_3461_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3431_, v___y_3458_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; lean_object* v___x_3463_; uint8_t v___x_3464_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref_known(v___x_3461_, 1);
v___x_3463_ = l_Lean_Expr_cleanupAnnotations(v_a_3462_);
lean_dec(v_a_3462_);
v___x_3464_ = l_Lean_Expr_isApp(v___x_3463_);
if (v___x_3464_ == 0)
{
lean_dec_ref(v___x_3463_);
lean_dec_ref(v_e_3431_);
goto v___jp_3443_;
}
else
{
lean_object* v___x_3465_; lean_object* v___x_3466_; uint8_t v___x_3467_; 
v___x_3465_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3463_);
v___x_3466_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3467_ = l_Lean_Expr_isConstOf(v___x_3465_, v___x_3466_);
lean_dec_ref(v___x_3465_);
if (v___x_3467_ == 0)
{
lean_dec_ref(v___x_3463_);
lean_dec_ref(v_e_3431_);
goto v___jp_3443_;
}
else
{
lean_object* v_arg_3468_; uint8_t v___x_3469_; lean_object* v___x_3470_; lean_object* v___f_3471_; uint8_t v___x_3472_; lean_object* v___x_3473_; 
v_arg_3468_ = lean_ctor_get(v___x_3463_, 1);
lean_inc_ref(v_arg_3468_);
lean_dec_ref(v___x_3463_);
v___x_3469_ = 0;
v___x_3470_ = lean_box(v___x_3469_);
v___f_3471_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_tryToProveFalse___lam__1___boxed), 16, 5);
lean_closure_set(v___f_3471_, 0, v_arg_3468_);
lean_closure_set(v___f_3471_, 1, v___x_3470_);
lean_closure_set(v___f_3471_, 2, v_e_3431_);
lean_closure_set(v___f_3471_, 3, v___f_3449_);
lean_closure_set(v___f_3471_, 4, v_cls_3448_);
v___x_3472_ = 0;
v___x_3473_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(v___f_3471_, v___x_3472_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3484_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3476_ = v___x_3473_;
v_isShared_3477_ = v_isSharedCheck_3484_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3473_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3484_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
if (lean_obj_tag(v_a_3474_) == 1)
{
lean_object* v_val_3478_; lean_object* v___x_3479_; 
lean_del_object(v___x_3476_);
v_val_3478_ = lean_ctor_get(v_a_3474_, 0);
lean_inc(v_val_3478_);
lean_dec_ref_known(v_a_3474_, 1);
v___x_3479_ = l_Lean_Meta_Grind_closeGoal(v_val_3478_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
return v___x_3479_;
}
else
{
lean_object* v___x_3480_; lean_object* v___x_3482_; 
lean_dec(v_a_3474_);
v___x_3480_ = lean_box(0);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v___x_3480_);
v___x_3482_ = v___x_3476_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3480_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
v_a_3485_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3473_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3473_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
}
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_dec_ref(v_e_3431_);
v_a_3493_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3461_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3461_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___boxed(lean_object* v_e_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_){
_start:
{
lean_object* v_res_3519_; 
v_res_3519_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_);
lean_dec(v_a_3517_);
lean_dec_ref(v_a_3516_);
lean_dec(v_a_3515_);
lean_dec_ref(v_a_3514_);
lean_dec(v_a_3513_);
lean_dec_ref(v_a_3512_);
lean_dec(v_a_3511_);
lean_dec_ref(v_a_3510_);
lean_dec(v_a_3509_);
lean_dec(v_a_3508_);
return v_res_3519_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1(void){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = ((lean_object*)(l_Lean_Meta_Grind_propagateMatchCondUp___closed__0));
v___x_3522_ = l_Lean_stringToMessageData(v___x_3521_);
return v___x_3522_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3(void){
_start:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3524_ = ((lean_object*)(l_Lean_Meta_Grind_propagateMatchCondUp___closed__2));
v___x_3525_ = l_Lean_stringToMessageData(v___x_3524_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp(lean_object* v_e_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v_toCold_3552_; lean_object* v_options_3553_; lean_object* v_inheritedTraceOptions_3554_; uint8_t v_hasTrace_3555_; lean_object* v_cls_3556_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; 
v_toCold_3552_ = lean_ctor_get(v_a_3535_, 0);
v_options_3553_ = lean_ctor_get(v_toCold_3552_, 2);
v_inheritedTraceOptions_3554_ = lean_ctor_get(v_toCold_3552_, 11);
v_hasTrace_3555_ = lean_ctor_get_uint8(v_options_3553_, sizeof(void*)*1);
v_cls_3556_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
if (v_hasTrace_3555_ == 0)
{
v___y_3558_ = v_a_3527_;
v___y_3559_ = v_a_3528_;
v___y_3560_ = v_a_3529_;
v___y_3561_ = v_a_3530_;
v___y_3562_ = v_a_3531_;
v___y_3563_ = v_a_3532_;
v___y_3564_ = v_a_3533_;
v___y_3565_ = v_a_3534_;
v___y_3566_ = v_a_3535_;
v___y_3567_ = v_a_3536_;
goto v___jp_3557_;
}
else
{
lean_object* v___x_3664_; uint8_t v___x_3665_; 
v___x_3664_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_3665_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3554_, v_options_3553_, v___x_3664_);
if (v___x_3665_ == 0)
{
v___y_3558_ = v_a_3527_;
v___y_3559_ = v_a_3528_;
v___y_3560_ = v_a_3529_;
v___y_3561_ = v_a_3530_;
v___y_3562_ = v_a_3531_;
v___y_3563_ = v_a_3532_;
v___y_3564_ = v_a_3533_;
v___y_3565_ = v_a_3534_;
v___y_3566_ = v_a_3535_;
v___y_3567_ = v_a_3536_;
goto v___jp_3557_;
}
else
{
lean_object* v___x_3666_; 
v___x_3666_ = l_Lean_Meta_Grind_updateLastTag(v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
lean_dec_ref_known(v___x_3666_, 1);
v___x_3667_ = lean_obj_once(&l_Lean_Meta_Grind_propagateMatchCondUp___closed__3, &l_Lean_Meta_Grind_propagateMatchCondUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3);
lean_inc_ref(v_e_3526_);
v___x_3668_ = l_Lean_indentExpr(v_e_3526_);
v___x_3669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3667_);
lean_ctor_set(v___x_3669_, 1, v___x_3668_);
v___x_3670_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3556_, v___x_3669_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_dec_ref_known(v___x_3670_, 1);
v___y_3558_ = v_a_3527_;
v___y_3559_ = v_a_3528_;
v___y_3560_ = v_a_3529_;
v___y_3561_ = v_a_3530_;
v___y_3562_ = v_a_3531_;
v___y_3563_ = v_a_3532_;
v___y_3564_ = v_a_3533_;
v___y_3565_ = v_a_3534_;
v___y_3566_ = v_a_3535_;
v___y_3567_ = v_a_3536_;
goto v___jp_3557_;
}
else
{
lean_dec_ref(v_e_3526_);
return v___x_3670_;
}
}
else
{
lean_dec_ref(v_e_3526_);
return v___x_3666_;
}
}
}
v___jp_3538_:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = lean_box(0);
v___x_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3539_);
return v___x_3540_;
}
v___jp_3541_:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
lean_inc_ref(v_e_3526_);
v___x_3550_ = l_Lean_Meta_mkEqTrueCore(v_e_3526_, v___y_3542_);
v___x_3551_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_3526_, v___x_3550_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
return v___x_3551_;
}
v___jp_3557_:
{
lean_object* v___x_3568_; 
lean_inc_ref(v_e_3526_);
v___x_3568_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3526_, v___y_3558_, v___y_3562_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; uint8_t v___x_3570_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc(v_a_3569_);
lean_dec_ref_known(v___x_3568_, 1);
v___x_3570_ = lean_unbox(v_a_3569_);
lean_dec(v_a_3569_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3571_; 
lean_inc_ref(v_e_3526_);
v___x_3571_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3526_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3627_; 
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3574_ = v___x_3571_;
v_isShared_3575_ = v_isSharedCheck_3627_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3571_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3627_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
uint8_t v___x_3576_; 
v___x_3576_ = lean_unbox(v_a_3572_);
lean_dec(v_a_3572_);
if (v___x_3576_ == 0)
{
lean_object* v___x_3577_; lean_object* v___x_3579_; 
lean_dec_ref(v_e_3526_);
v___x_3577_ = lean_box(0);
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v___x_3577_);
v___x_3579_ = v___x_3574_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
else
{
lean_object* v___x_3581_; 
lean_del_object(v___x_3574_);
lean_inc_ref(v_e_3526_);
v___x_3581_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_3526_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3582_);
lean_dec_ref_known(v___x_3581_, 1);
if (lean_obj_tag(v_a_3582_) == 1)
{
lean_object* v_toCold_3583_; lean_object* v_options_3584_; uint8_t v_hasTrace_3585_; 
v_toCold_3583_ = lean_ctor_get(v___y_3566_, 0);
v_options_3584_ = lean_ctor_get(v_toCold_3583_, 2);
v_hasTrace_3585_ = lean_ctor_get_uint8(v_options_3584_, sizeof(void*)*1);
if (v_hasTrace_3585_ == 0)
{
lean_object* v_val_3586_; 
v_val_3586_ = lean_ctor_get(v_a_3582_, 0);
lean_inc(v_val_3586_);
lean_dec_ref_known(v_a_3582_, 1);
v___y_3542_ = v_val_3586_;
v___y_3543_ = v___y_3558_;
v___y_3544_ = v___y_3560_;
v___y_3545_ = v___y_3562_;
v___y_3546_ = v___y_3564_;
v___y_3547_ = v___y_3565_;
v___y_3548_ = v___y_3566_;
v___y_3549_ = v___y_3567_;
goto v___jp_3541_;
}
else
{
lean_object* v_val_3587_; lean_object* v_inheritedTraceOptions_3588_; lean_object* v___x_3589_; uint8_t v___x_3590_; 
v_val_3587_ = lean_ctor_get(v_a_3582_, 0);
lean_inc(v_val_3587_);
lean_dec_ref_known(v_a_3582_, 1);
v_inheritedTraceOptions_3588_ = lean_ctor_get(v_toCold_3583_, 11);
v___x_3589_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_3590_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3588_, v_options_3584_, v___x_3589_);
if (v___x_3590_ == 0)
{
v___y_3542_ = v_val_3587_;
v___y_3543_ = v___y_3558_;
v___y_3544_ = v___y_3560_;
v___y_3545_ = v___y_3562_;
v___y_3546_ = v___y_3564_;
v___y_3547_ = v___y_3565_;
v___y_3548_ = v___y_3566_;
v___y_3549_ = v___y_3567_;
goto v___jp_3541_;
}
else
{
lean_object* v___x_3591_; 
v___x_3591_ = l_Lean_Meta_Grind_updateLastTag(v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v___x_3592_; 
lean_dec_ref_known(v___x_3591_, 1);
lean_inc(v___y_3567_);
lean_inc_ref(v___y_3566_);
lean_inc(v___y_3565_);
lean_inc_ref(v___y_3564_);
lean_inc(v_val_3587_);
v___x_3592_ = lean_infer_type(v_val_3587_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
if (lean_obj_tag(v___x_3592_) == 0)
{
lean_object* v_a_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
lean_inc(v_a_3593_);
lean_dec_ref_known(v___x_3592_, 1);
v___x_3594_ = l_Lean_MessageData_ofExpr(v_a_3593_);
v___x_3595_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3556_, v___x_3594_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_dec_ref_known(v___x_3595_, 1);
v___y_3542_ = v_val_3587_;
v___y_3543_ = v___y_3558_;
v___y_3544_ = v___y_3560_;
v___y_3545_ = v___y_3562_;
v___y_3546_ = v___y_3564_;
v___y_3547_ = v___y_3565_;
v___y_3548_ = v___y_3566_;
v___y_3549_ = v___y_3567_;
goto v___jp_3541_;
}
else
{
lean_dec(v_val_3587_);
lean_dec_ref(v_e_3526_);
return v___x_3595_;
}
}
else
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3603_; 
lean_dec(v_val_3587_);
lean_dec_ref(v_e_3526_);
v_a_3596_ = lean_ctor_get(v___x_3592_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3598_ = v___x_3592_;
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3592_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
}
else
{
lean_dec(v_val_3587_);
lean_dec_ref(v_e_3526_);
return v___x_3591_;
}
}
}
}
else
{
lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
lean_dec(v_a_3582_);
v___x_3604_ = lean_obj_once(&l_Lean_Meta_Grind_propagateMatchCondUp___closed__1, &l_Lean_Meta_Grind_propagateMatchCondUp___closed__1_once, _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1);
v___x_3605_ = l_Lean_indentExpr(v_e_3526_);
v___x_3606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3604_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
v___x_3607_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_3562_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; uint8_t v_verbose_3609_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_a_3608_);
lean_dec_ref_known(v___x_3607_, 1);
v_verbose_3609_ = lean_ctor_get_uint8(v_a_3608_, 0);
lean_dec(v_a_3608_);
if (v_verbose_3609_ == 0)
{
lean_dec_ref_known(v___x_3606_, 2);
goto v___jp_3538_;
}
else
{
lean_object* v___x_3610_; 
v___x_3610_ = l_Lean_Meta_Sym_reportIssue(v___x_3606_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_dec_ref_known(v___x_3610_, 1);
goto v___jp_3538_;
}
else
{
return v___x_3610_;
}
}
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec_ref_known(v___x_3606_, 2);
v_a_3611_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3607_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3607_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
lean_dec_ref(v_e_3526_);
v_a_3619_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3581_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3581_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
}
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_dec_ref(v_e_3526_);
v_a_3628_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3571_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3571_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
else
{
lean_object* v___x_3636_; 
lean_inc_ref(v_e_3526_);
v___x_3636_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3526_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3647_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3639_ = v___x_3636_;
v_isShared_3640_ = v_isSharedCheck_3647_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3636_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3647_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
uint8_t v___x_3641_; 
v___x_3641_ = lean_unbox(v_a_3637_);
lean_dec(v_a_3637_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3642_; 
lean_del_object(v___x_3639_);
v___x_3642_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3526_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
return v___x_3642_;
}
else
{
lean_object* v___x_3643_; lean_object* v___x_3645_; 
lean_dec_ref(v_e_3526_);
v___x_3643_ = lean_box(0);
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 0, v___x_3643_);
v___x_3645_ = v___x_3639_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v___x_3643_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
else
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3655_; 
lean_dec_ref(v_e_3526_);
v_a_3648_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3650_ = v___x_3636_;
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3636_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3653_; 
if (v_isShared_3651_ == 0)
{
v___x_3653_ = v___x_3650_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3648_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
}
}
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
lean_dec_ref(v_e_3526_);
v_a_3656_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___x_3568_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3568_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3656_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___boxed(lean_object* v_e_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_){
_start:
{
lean_object* v_res_3683_; 
v_res_3683_ = l_Lean_Meta_Grind_propagateMatchCondUp(v_e_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
lean_dec(v_a_3681_);
lean_dec_ref(v_a_3680_);
lean_dec(v_a_3679_);
lean_dec_ref(v_a_3678_);
lean_dec(v_a_3677_);
lean_dec_ref(v_a_3676_);
lean_dec(v_a_3675_);
lean_dec_ref(v_a_3674_);
lean_dec(v_a_3673_);
lean_dec(v_a_3672_);
return v_res_3683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3685_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3686_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondUp___boxed), 12, 0);
v___x_3687_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3685_, v___x_3686_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_9____boxed(lean_object* v_a_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_9_();
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown(lean_object* v_e_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_){
_start:
{
lean_object* v___x_3702_; 
lean_inc_ref(v_e_3690_);
v___x_3702_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3690_, v_a_3691_, v_a_3695_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_);
if (lean_obj_tag(v___x_3702_) == 0)
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3732_; 
v_a_3703_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3705_ = v___x_3702_;
v_isShared_3706_ = v_isSharedCheck_3732_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3702_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3732_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
uint8_t v___x_3707_; 
v___x_3707_ = lean_unbox(v_a_3703_);
lean_dec(v_a_3703_);
if (v___x_3707_ == 0)
{
lean_object* v___x_3708_; lean_object* v___x_3710_; 
lean_dec_ref(v_e_3690_);
v___x_3708_ = lean_box(0);
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 0, v___x_3708_);
v___x_3710_ = v___x_3705_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3708_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
else
{
lean_object* v___x_3712_; 
lean_del_object(v___x_3705_);
lean_inc_ref(v_e_3690_);
v___x_3712_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3723_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3715_ = v___x_3712_;
v_isShared_3716_ = v_isSharedCheck_3723_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3712_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3723_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
uint8_t v___x_3717_; 
v___x_3717_ = lean_unbox(v_a_3713_);
lean_dec(v_a_3713_);
if (v___x_3717_ == 0)
{
lean_object* v___x_3718_; 
lean_del_object(v___x_3715_);
v___x_3718_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_);
return v___x_3718_;
}
else
{
lean_object* v___x_3719_; lean_object* v___x_3721_; 
lean_dec_ref(v_e_3690_);
v___x_3719_ = lean_box(0);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3719_);
v___x_3721_ = v___x_3715_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3719_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
lean_dec_ref(v_e_3690_);
v_a_3724_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3712_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3712_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_dec_ref(v_e_3690_);
v_a_3733_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3702_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3702_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___boxed(lean_object* v_e_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_){
_start:
{
lean_object* v_res_3753_; 
v_res_3753_ = l_Lean_Meta_Grind_propagateMatchCondDown(v_e_3741_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
lean_dec(v_a_3751_);
lean_dec_ref(v_a_3750_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
lean_dec(v_a_3743_);
lean_dec(v_a_3742_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3755_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3756_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondDown___boxed), 12, 0);
v___x_3757_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3755_, v___x_3756_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_9____boxed(lean_object* v_a_3758_){
_start:
{
lean_object* v_res_3759_; 
v_res_3759_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_9_();
return v_res_3759_;
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
