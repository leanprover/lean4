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
lean_object* v___x_194_; size_t v___x_195_; uint8_t v___x_196_; 
lean_dec(v___x_179_);
lean_inc_ref(v_body_172_);
v___x_194_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_166_, v_tys_167_, v_body_172_, v_i_169_);
v___x_195_ = lean_ptr_addr(v_binderType_171_);
v___x_196_ = lean_usize_dec_eq(v___x_195_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; 
lean_inc_ref(v_binderType_171_);
lean_inc(v_binderName_170_);
lean_dec_ref_known(v_e_168_, 3);
v___x_197_ = l_Lean_Expr_forallE___override(v_binderName_170_, v_binderType_171_, v___x_194_, v_binderInfo_173_);
return v___x_197_;
}
else
{
size_t v___x_198_; size_t v___x_199_; uint8_t v___x_200_; 
v___x_198_ = lean_ptr_addr(v_body_172_);
v___x_199_ = lean_ptr_addr(v___x_194_);
v___x_200_ = lean_usize_dec_eq(v___x_198_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
lean_inc_ref(v_binderType_171_);
lean_inc(v_binderName_170_);
lean_dec_ref_known(v_e_168_, 3);
v___x_201_ = l_Lean_Expr_forallE___override(v_binderName_170_, v_binderType_171_, v___x_194_, v_binderInfo_173_);
return v___x_201_;
}
else
{
uint8_t v___x_202_; 
v___x_202_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_173_, v_binderInfo_173_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
lean_inc_ref(v_binderType_171_);
lean_inc(v_binderName_170_);
lean_dec_ref_known(v_e_168_, 3);
v___x_203_ = l_Lean_Expr_forallE___override(v_binderName_170_, v_binderType_171_, v___x_194_, v_binderInfo_173_);
return v___x_203_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss___boxed(lean_object* v_xs_204_, lean_object* v_tys_205_, lean_object* v_e_206_, lean_object* v_i_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_204_, v_tys_205_, v_e_206_, v_i_207_);
lean_dec(v_i_207_);
lean_dec_ref(v_tys_205_);
lean_dec_ref(v_xs_204_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0(lean_object* v_k_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v_b_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___x_222_; 
lean_inc(v___y_220_);
lean_inc_ref(v___y_219_);
lean_inc(v___y_218_);
lean_inc_ref(v___y_217_);
lean_inc(v___y_215_);
lean_inc_ref(v___y_214_);
lean_inc(v___y_213_);
lean_inc_ref(v___y_212_);
lean_inc(v___y_211_);
lean_inc(v___y_210_);
v___x_222_ = lean_apply_12(v_k_209_, v_b_216_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, lean_box(0));
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v_b_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0(v_k_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v_b_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec(v___y_224_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(lean_object* v_name_237_, uint8_t v_bi_238_, lean_object* v_type_239_, lean_object* v_k_240_, uint8_t v_kind_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v___f_253_; lean_object* v___x_254_; 
lean_inc(v___y_247_);
lean_inc_ref(v___y_246_);
lean_inc(v___y_245_);
lean_inc_ref(v___y_244_);
lean_inc(v___y_243_);
lean_inc(v___y_242_);
v___f_253_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_253_, 0, v_k_240_);
lean_closure_set(v___f_253_, 1, v___y_242_);
lean_closure_set(v___f_253_, 2, v___y_243_);
lean_closure_set(v___f_253_, 3, v___y_244_);
lean_closure_set(v___f_253_, 4, v___y_245_);
lean_closure_set(v___f_253_, 5, v___y_246_);
lean_closure_set(v___f_253_, 6, v___y_247_);
v___x_254_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_237_, v_bi_238_, v_type_239_, v___f_253_, v_kind_241_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
if (lean_obj_tag(v___x_254_) == 0)
{
return v___x_254_;
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___boxed(lean_object* v_name_263_, lean_object* v_bi_264_, lean_object* v_type_265_, lean_object* v_k_266_, lean_object* v_kind_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
uint8_t v_bi_boxed_279_; uint8_t v_kind_boxed_280_; lean_object* v_res_281_; 
v_bi_boxed_279_ = lean_unbox(v_bi_264_);
v_kind_boxed_280_ = lean_unbox(v_kind_267_);
v_res_281_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_263_, v_bi_boxed_279_, v_type_265_, v_k_266_, v_kind_boxed_280_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec(v___y_268_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(lean_object* v_name_282_, lean_object* v_type_283_, lean_object* v_k_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
uint8_t v___x_296_; uint8_t v___x_297_; lean_object* v___x_298_; 
v___x_296_ = 0;
v___x_297_ = 0;
v___x_298_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_282_, v___x_296_, v_type_283_, v_k_284_, v___x_297_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg___boxed(lean_object* v_name_299_, lean_object* v_type_300_, lean_object* v_k_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v_name_299_, v_type_300_, v_k_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec(v___y_302_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed(lean_object** _args){
lean_object* v_i_317_ = _args[0];
lean_object* v_xs_318_ = _args[1];
lean_object* v_tys_319_ = _args[2];
lean_object* v_tysxs_320_ = _args[3];
lean_object* v_args_321_ = _args[4];
lean_object* v_val_322_ = _args[5];
lean_object* v_fst_323_ = _args[6];
lean_object* v_e_324_ = _args[7];
lean_object* v_lhss_u03b1s_325_ = _args[8];
lean_object* v_ty_326_ = _args[9];
lean_object* v___y_327_ = _args[10];
lean_object* v___y_328_ = _args[11];
lean_object* v___y_329_ = _args[12];
lean_object* v___y_330_ = _args[13];
lean_object* v___y_331_ = _args[14];
lean_object* v___y_332_ = _args[15];
lean_object* v___y_333_ = _args[16];
lean_object* v___y_334_ = _args[17];
lean_object* v___y_335_ = _args[18];
lean_object* v___y_336_ = _args[19];
lean_object* v___y_337_ = _args[20];
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(v_i_317_, v_xs_318_, v_tys_319_, v_tysxs_320_, v_args_321_, v_val_322_, v_fst_323_, v_e_324_, v_lhss_u03b1s_325_, v_ty_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec(v___y_327_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(lean_object* v_i_342_, lean_object* v_xs_343_, lean_object* v_tys_344_, lean_object* v_tysxs_345_, lean_object* v_args_346_, lean_object* v_fst_347_, lean_object* v_e_348_, lean_object* v_lhss_u03b1s_349_, lean_object* v_x_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_362_ = lean_unsigned_to_nat(1u);
v___x_363_ = lean_nat_add(v_i_342_, v___x_362_);
lean_inc_ref(v_x_350_);
v___x_364_ = lean_array_push(v_xs_343_, v_x_350_);
v___x_365_ = lean_box(0);
v___x_366_ = lean_array_push(v_tys_344_, v___x_365_);
v___x_367_ = lean_array_push(v_tysxs_345_, v_x_350_);
v___x_368_ = lean_array_push(v_args_346_, v_fst_347_);
v___x_369_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_348_, v_lhss_u03b1s_349_, v___x_363_, v___x_364_, v___x_366_, v___x_367_, v___x_368_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed(lean_object** _args){
lean_object* v_i_370_ = _args[0];
lean_object* v_xs_371_ = _args[1];
lean_object* v_tys_372_ = _args[2];
lean_object* v_tysxs_373_ = _args[3];
lean_object* v_args_374_ = _args[4];
lean_object* v_fst_375_ = _args[5];
lean_object* v_e_376_ = _args[6];
lean_object* v_lhss_u03b1s_377_ = _args[7];
lean_object* v_x_378_ = _args[8];
lean_object* v___y_379_ = _args[9];
lean_object* v___y_380_ = _args[10];
lean_object* v___y_381_ = _args[11];
lean_object* v___y_382_ = _args[12];
lean_object* v___y_383_ = _args[13];
lean_object* v___y_384_ = _args[14];
lean_object* v___y_385_ = _args[15];
lean_object* v___y_386_ = _args[16];
lean_object* v___y_387_ = _args[17];
lean_object* v___y_388_ = _args[18];
lean_object* v___y_389_ = _args[19];
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(v_i_370_, v_xs_371_, v_tys_372_, v_tysxs_373_, v_args_374_, v_fst_375_, v_e_376_, v_lhss_u03b1s_377_, v_x_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec(v___y_379_);
lean_dec(v_i_370_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(lean_object* v_e_391_, lean_object* v_lhss_u03b1s_392_, lean_object* v_i_393_, lean_object* v_xs_394_, lean_object* v_tys_395_, lean_object* v_tysxs_396_, lean_object* v_args_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = lean_array_get_size(v_lhss_u03b1s_392_);
v___x_410_ = lean_nat_dec_lt(v_i_393_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v_eAbst_412_; uint8_t v___x_413_; uint8_t v___x_414_; lean_object* v___x_415_; 
lean_dec(v_i_393_);
lean_dec_ref(v_lhss_u03b1s_392_);
v___x_411_ = lean_unsigned_to_nat(0u);
v_eAbst_412_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_394_, v_tys_395_, v_e_391_, v___x_411_);
lean_dec_ref(v_tys_395_);
lean_dec_ref(v_xs_394_);
v___x_413_ = 1;
v___x_414_ = 1;
v___x_415_ = l_Lean_Meta_mkLambdaFVars(v_tysxs_396_, v_eAbst_412_, v___x_410_, v___x_413_, v___x_410_, v___x_413_, v___x_414_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
lean_dec_ref(v_tysxs_396_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_a_416_);
lean_dec_ref_known(v___x_415_, 1);
v___x_417_ = l_Lean_mkAppN(v_a_416_, v_args_397_);
v___x_418_ = l_Lean_Meta_Sym_shareCommon(v___x_417_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_427_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_427_ == 0)
{
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_427_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_427_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v_args_397_);
lean_ctor_set(v___x_423_, 1, v_a_419_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_423_);
v___x_425_ = v___x_421_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec_ref(v_args_397_);
v_a_428_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_418_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_418_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec_ref(v_args_397_);
v_a_436_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_415_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_415_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
else
{
lean_object* v___x_444_; lean_object* v_snd_445_; 
v___x_444_ = lean_array_fget_borrowed(v_lhss_u03b1s_392_, v_i_393_);
v_snd_445_ = lean_ctor_get(v___x_444_, 1);
if (lean_obj_tag(v_snd_445_) == 1)
{
lean_object* v_fst_446_; lean_object* v_val_447_; lean_object* v___f_448_; lean_object* v___x_449_; 
v_fst_446_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_fst_446_);
v_val_447_ = lean_ctor_get(v_snd_445_, 0);
lean_inc_n(v_val_447_, 2);
lean_inc(v_i_393_);
v___f_448_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed), 21, 9);
lean_closure_set(v___f_448_, 0, v_i_393_);
lean_closure_set(v___f_448_, 1, v_xs_394_);
lean_closure_set(v___f_448_, 2, v_tys_395_);
lean_closure_set(v___f_448_, 3, v_tysxs_396_);
lean_closure_set(v___f_448_, 4, v_args_397_);
lean_closure_set(v___f_448_, 5, v_val_447_);
lean_closure_set(v___f_448_, 6, v_fst_446_);
lean_closure_set(v___f_448_, 7, v_e_391_);
lean_closure_set(v___f_448_, 8, v_lhss_u03b1s_392_);
lean_inc(v_a_407_);
lean_inc_ref(v_a_406_);
lean_inc(v_a_405_);
lean_inc_ref(v_a_404_);
v___x_449_ = lean_infer_type(v_val_447_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref_known(v___x_449_, 1);
v___x_451_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__1));
v___x_452_ = lean_name_append_index_after(v___x_451_, v_i_393_);
v___x_453_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v___x_452_, v_a_450_, v___f_448_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
return v___x_453_;
}
else
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
lean_dec_ref(v___f_448_);
lean_dec(v_i_393_);
v_a_454_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_449_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_449_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
else
{
lean_object* v_fst_462_; lean_object* v___f_463_; lean_object* v___x_464_; 
v_fst_462_ = lean_ctor_get(v___x_444_, 0);
lean_inc_n(v_fst_462_, 2);
lean_inc(v_i_393_);
v___f_463_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed), 20, 8);
lean_closure_set(v___f_463_, 0, v_i_393_);
lean_closure_set(v___f_463_, 1, v_xs_394_);
lean_closure_set(v___f_463_, 2, v_tys_395_);
lean_closure_set(v___f_463_, 3, v_tysxs_396_);
lean_closure_set(v___f_463_, 4, v_args_397_);
lean_closure_set(v___f_463_, 5, v_fst_462_);
lean_closure_set(v___f_463_, 6, v_e_391_);
lean_closure_set(v___f_463_, 7, v_lhss_u03b1s_392_);
lean_inc(v_a_407_);
lean_inc_ref(v_a_406_);
lean_inc(v_a_405_);
lean_inc_ref(v_a_404_);
v___x_464_ = lean_infer_type(v_fst_462_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_464_, 1);
v___x_466_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1));
v___x_467_ = lean_name_append_index_after(v___x_466_, v_i_393_);
v___x_468_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v___x_467_, v_a_465_, v___f_463_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
return v___x_468_;
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec_ref(v___f_463_);
lean_dec(v_i_393_);
v_a_469_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_464_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_464_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(lean_object* v_i_477_, lean_object* v_xs_478_, lean_object* v_ty_479_, lean_object* v_tys_480_, lean_object* v_tysxs_481_, lean_object* v_args_482_, lean_object* v_val_483_, lean_object* v_fst_484_, lean_object* v_e_485_, lean_object* v_lhss_u03b1s_486_, lean_object* v_x_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_nat_add(v_i_477_, v___x_499_);
lean_inc_ref(v_x_487_);
v___x_501_ = lean_array_push(v_xs_478_, v_x_487_);
lean_inc_ref(v_ty_479_);
v___x_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_502_, 0, v_ty_479_);
v___x_503_ = lean_array_push(v_tys_480_, v___x_502_);
v___x_504_ = lean_array_push(v_tysxs_481_, v_ty_479_);
v___x_505_ = lean_array_push(v___x_504_, v_x_487_);
v___x_506_ = lean_array_push(v_args_482_, v_val_483_);
v___x_507_ = lean_array_push(v___x_506_, v_fst_484_);
v___x_508_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_485_, v_lhss_u03b1s_486_, v___x_500_, v___x_501_, v___x_503_, v___x_505_, v___x_507_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0___boxed(lean_object** _args){
lean_object* v_i_509_ = _args[0];
lean_object* v_xs_510_ = _args[1];
lean_object* v_ty_511_ = _args[2];
lean_object* v_tys_512_ = _args[3];
lean_object* v_tysxs_513_ = _args[4];
lean_object* v_args_514_ = _args[5];
lean_object* v_val_515_ = _args[6];
lean_object* v_fst_516_ = _args[7];
lean_object* v_e_517_ = _args[8];
lean_object* v_lhss_u03b1s_518_ = _args[9];
lean_object* v_x_519_ = _args[10];
lean_object* v___y_520_ = _args[11];
lean_object* v___y_521_ = _args[12];
lean_object* v___y_522_ = _args[13];
lean_object* v___y_523_ = _args[14];
lean_object* v___y_524_ = _args[15];
lean_object* v___y_525_ = _args[16];
lean_object* v___y_526_ = _args[17];
lean_object* v___y_527_ = _args[18];
lean_object* v___y_528_ = _args[19];
lean_object* v___y_529_ = _args[20];
lean_object* v___y_530_ = _args[21];
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(v_i_509_, v_xs_510_, v_ty_511_, v_tys_512_, v_tysxs_513_, v_args_514_, v_val_515_, v_fst_516_, v_e_517_, v_lhss_u03b1s_518_, v_x_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec(v___y_520_);
lean_dec(v_i_509_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(lean_object* v_i_532_, lean_object* v_xs_533_, lean_object* v_tys_534_, lean_object* v_tysxs_535_, lean_object* v_args_536_, lean_object* v_val_537_, lean_object* v_fst_538_, lean_object* v_e_539_, lean_object* v_lhss_u03b1s_540_, lean_object* v_ty_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___f_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
lean_inc_ref(v_ty_541_);
lean_inc(v_i_532_);
v___f_553_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0___boxed), 22, 10);
lean_closure_set(v___f_553_, 0, v_i_532_);
lean_closure_set(v___f_553_, 1, v_xs_533_);
lean_closure_set(v___f_553_, 2, v_ty_541_);
lean_closure_set(v___f_553_, 3, v_tys_534_);
lean_closure_set(v___f_553_, 4, v_tysxs_535_);
lean_closure_set(v___f_553_, 5, v_args_536_);
lean_closure_set(v___f_553_, 6, v_val_537_);
lean_closure_set(v___f_553_, 7, v_fst_538_);
lean_closure_set(v___f_553_, 8, v_e_539_);
lean_closure_set(v___f_553_, 9, v_lhss_u03b1s_540_);
v___x_554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1));
v___x_555_ = lean_name_append_index_after(v___x_554_, v_i_532_);
v___x_556_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v___x_555_, v_ty_541_, v___f_553_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___boxed(lean_object** _args){
lean_object* v_e_557_ = _args[0];
lean_object* v_lhss_u03b1s_558_ = _args[1];
lean_object* v_i_559_ = _args[2];
lean_object* v_xs_560_ = _args[3];
lean_object* v_tys_561_ = _args[4];
lean_object* v_tysxs_562_ = _args[5];
lean_object* v_args_563_ = _args[6];
lean_object* v_a_564_ = _args[7];
lean_object* v_a_565_ = _args[8];
lean_object* v_a_566_ = _args[9];
lean_object* v_a_567_ = _args[10];
lean_object* v_a_568_ = _args[11];
lean_object* v_a_569_ = _args[12];
lean_object* v_a_570_ = _args[13];
lean_object* v_a_571_ = _args[14];
lean_object* v_a_572_ = _args[15];
lean_object* v_a_573_ = _args[16];
lean_object* v_a_574_ = _args[17];
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_557_, v_lhss_u03b1s_558_, v_i_559_, v_xs_560_, v_tys_561_, v_tysxs_562_, v_args_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec(v_a_564_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0(lean_object* v_00_u03b1_576_, lean_object* v_name_577_, uint8_t v_bi_578_, lean_object* v_type_579_, lean_object* v_k_580_, uint8_t v_kind_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_577_, v_bi_578_, v_type_579_, v_k_580_, v_kind_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_594_ = _args[0];
lean_object* v_name_595_ = _args[1];
lean_object* v_bi_596_ = _args[2];
lean_object* v_type_597_ = _args[3];
lean_object* v_k_598_ = _args[4];
lean_object* v_kind_599_ = _args[5];
lean_object* v___y_600_ = _args[6];
lean_object* v___y_601_ = _args[7];
lean_object* v___y_602_ = _args[8];
lean_object* v___y_603_ = _args[9];
lean_object* v___y_604_ = _args[10];
lean_object* v___y_605_ = _args[11];
lean_object* v___y_606_ = _args[12];
lean_object* v___y_607_ = _args[13];
lean_object* v___y_608_ = _args[14];
lean_object* v___y_609_ = _args[15];
lean_object* v___y_610_ = _args[16];
_start:
{
uint8_t v_bi_boxed_611_; uint8_t v_kind_boxed_612_; lean_object* v_res_613_; 
v_bi_boxed_611_ = lean_unbox(v_bi_596_);
v_kind_boxed_612_ = lean_unbox(v_kind_599_);
v_res_613_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0(v_00_u03b1_594_, v_name_595_, v_bi_boxed_611_, v_type_597_, v_k_598_, v_kind_boxed_612_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec(v___y_600_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0(lean_object* v_00_u03b1_614_, lean_object* v_name_615_, lean_object* v_type_616_, lean_object* v_k_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v_name_615_, v_type_616_, v_k_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___boxed(lean_object* v_00_u03b1_630_, lean_object* v_name_631_, lean_object* v_type_632_, lean_object* v_k_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0(v_00_u03b1_630_, v_name_631_, v_type_632_, v_k_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec(v___y_634_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter___redArg(lean_object* v_x_646_, lean_object* v_h__1_647_){
_start:
{
lean_object* v_fst_648_; lean_object* v_snd_649_; lean_object* v___x_650_; 
v_fst_648_ = lean_ctor_get(v_x_646_, 0);
lean_inc(v_fst_648_);
v_snd_649_ = lean_ctor_get(v_x_646_, 1);
lean_inc(v_snd_649_);
lean_dec_ref(v_x_646_);
v___x_650_ = lean_apply_2(v_h__1_647_, v_fst_648_, v_snd_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter(lean_object* v_motive_651_, lean_object* v_x_652_, lean_object* v_h__1_653_){
_start:
{
lean_object* v_fst_654_; lean_object* v_snd_655_; lean_object* v___x_656_; 
v_fst_654_ = lean_ctor_get(v_x_652_, 0);
lean_inc(v_fst_654_);
v_snd_655_ = lean_ctor_get(v_x_652_, 1);
lean_inc(v_snd_655_);
lean_dec_ref(v_x_652_);
v___x_656_ = lean_apply_2(v_h__1_653_, v_fst_654_, v_snd_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter___redArg(lean_object* v_00_u03b1_x3f_657_, lean_object* v_h__1_658_, lean_object* v_h__2_659_){
_start:
{
if (lean_obj_tag(v_00_u03b1_x3f_657_) == 1)
{
lean_object* v_val_660_; lean_object* v___x_661_; 
lean_dec(v_h__2_659_);
v_val_660_ = lean_ctor_get(v_00_u03b1_x3f_657_, 0);
lean_inc(v_val_660_);
lean_dec_ref_known(v_00_u03b1_x3f_657_, 1);
v___x_661_ = lean_apply_1(v_h__1_658_, v_val_660_);
return v___x_661_;
}
else
{
lean_object* v___x_662_; 
lean_dec(v_h__1_658_);
v___x_662_ = lean_apply_2(v_h__2_659_, v_00_u03b1_x3f_657_, lean_box(0));
return v___x_662_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter(lean_object* v_motive_663_, lean_object* v_00_u03b1_x3f_664_, lean_object* v_h__1_665_, lean_object* v_h__2_666_){
_start:
{
if (lean_obj_tag(v_00_u03b1_x3f_664_) == 1)
{
lean_object* v_val_667_; lean_object* v___x_668_; 
lean_dec(v_h__2_666_);
v_val_667_ = lean_ctor_get(v_00_u03b1_x3f_664_, 0);
lean_inc(v_val_667_);
lean_dec_ref_known(v_00_u03b1_x3f_664_, 1);
v___x_668_ = lean_apply_1(v_h__1_665_, v_val_667_);
return v___x_668_;
}
else
{
lean_object* v___x_669_; 
lean_dec(v_h__1_665_);
v___x_669_ = lean_apply_2(v_h__2_666_, v_00_u03b1_x3f_664_, lean_box(0));
return v___x_669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(lean_object* v_matchCond_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_695_ = l_Lean_Expr_cleanupAnnotations(v_matchCond_679_);
v___x_696_ = l_Lean_Expr_isApp(v___x_695_);
if (v___x_696_ == 0)
{
lean_dec_ref(v___x_695_);
goto v___jp_691_;
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_697_ = l_Lean_Expr_appFnCleanup___redArg(v___x_695_);
v___x_698_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_699_ = l_Lean_Expr_isConstOf(v___x_697_, v___x_698_);
lean_dec_ref(v___x_697_);
if (v___x_699_ == 0)
{
lean_dec_ref(v___x_695_);
goto v___jp_691_;
}
else
{
lean_object* v_arg_700_; lean_object* v_lhss_u03b1s_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec_ref(v_matchCond_679_);
v_arg_700_ = lean_ctor_get(v___x_695_, 1);
lean_inc_ref_n(v_arg_700_, 2);
lean_dec_ref(v___x_695_);
v_lhss_u03b1s_701_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss(v_arg_700_);
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0));
v___x_704_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_arg_700_, v_lhss_u03b1s_701_, v___x_702_, v___x_703_, v___x_703_, v___x_703_, v___x_703_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
return v___x_704_;
}
}
v___jp_691_:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_692_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0));
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
lean_ctor_set(v___x_693_, 1, v_matchCond_679_);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___boxed(lean_object* v_matchCond_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(v_matchCond_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_a_707_);
lean_dec(v_a_706_);
return v_res_717_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0(void){
_start:
{
lean_object* v___x_721_; lean_object* v_dummy_722_; 
v___x_721_ = lean_box(0);
v_dummy_722_ = l_Lean_Expr_sort___override(v___x_721_);
return v_dummy_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(lean_object* v_matchCond_x3f_723_, lean_object* v_lhs_724_, lean_object* v_rhs_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
uint8_t v___x_737_; 
v___x_737_ = l_Lean_Expr_hasLooseBVars(v_lhs_724_);
if (v___x_737_ == 0)
{
uint8_t v___x_738_; lean_object* v___x_739_; 
v___x_738_ = 1;
lean_inc_ref(v_lhs_724_);
v___x_739_ = l_Lean_Meta_Grind_getRootENode___redArg(v_lhs_724_, v_a_726_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_901_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_901_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_901_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_901_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
uint8_t v_ctor_744_; 
v_ctor_744_ = lean_ctor_get_uint8(v_a_740_, sizeof(void*)*12 + 2);
if (v_ctor_744_ == 0)
{
uint8_t v_interpreted_745_; 
v_interpreted_745_ = lean_ctor_get_uint8(v_a_740_, sizeof(void*)*12 + 1);
if (v_interpreted_745_ == 0)
{
lean_dec(v_a_740_);
if (lean_obj_tag(v_matchCond_x3f_723_) == 1)
{
lean_object* v_val_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v_val_746_ = lean_ctor_get(v_matchCond_x3f_723_, 0);
lean_inc(v_val_746_);
lean_dec_ref_known(v_matchCond_x3f_723_, 1);
v___x_747_ = l_Lean_Expr_getAppFn(v_rhs_725_);
lean_dec_ref(v_rhs_725_);
v___x_748_ = l_Lean_Expr_isBVar(v___x_747_);
lean_dec_ref(v___x_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; 
lean_del_object(v___x_742_);
v___x_749_ = l_Lean_Meta_Grind_registerParent___redArg(v_val_746_, v_lhs_724_, v_a_726_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_757_; 
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; 
v_unused_758_ = lean_ctor_get(v___x_749_, 0);
lean_dec(v_unused_758_);
v___x_751_ = v___x_749_;
v_isShared_752_ = v_isSharedCheck_757_;
goto v_resetjp_750_;
}
else
{
lean_dec(v___x_749_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_757_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_753_ = lean_box(v_interpreted_745_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_753_);
v___x_755_ = v___x_751_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
v_a_759_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_749_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_749_);
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
else
{
lean_object* v___x_767_; lean_object* v___x_769_; 
lean_dec(v_val_746_);
lean_dec_ref(v_lhs_724_);
v___x_767_ = lean_box(v_interpreted_745_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_767_);
v___x_769_ = v___x_742_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
else
{
lean_object* v___x_771_; lean_object* v___x_773_; 
lean_dec_ref(v_rhs_725_);
lean_dec_ref(v_lhs_724_);
lean_dec(v_matchCond_x3f_723_);
v___x_771_ = lean_box(v_interpreted_745_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_771_);
v___x_773_ = v___x_742_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
else
{
lean_object* v_self_775_; uint8_t v___x_776_; 
lean_dec_ref(v_lhs_724_);
lean_dec(v_matchCond_x3f_723_);
v_self_775_ = lean_ctor_get(v_a_740_, 0);
lean_inc_ref(v_self_775_);
lean_dec(v_a_740_);
v___x_776_ = l_Lean_Expr_hasLooseBVars(v_rhs_725_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; 
lean_del_object(v___x_742_);
lean_inc_ref(v_rhs_725_);
v___x_777_ = l_Lean_Meta_isLitValue(v_rhs_725_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; uint8_t v___x_779_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v___x_779_ = lean_unbox(v_a_778_);
if (v___x_779_ == 0)
{
lean_dec_ref(v_self_775_);
lean_dec_ref(v_rhs_725_);
return v___x_777_;
}
else
{
lean_object* v___x_780_; 
lean_inc(v_a_778_);
lean_dec_ref_known(v___x_777_, 1);
v___x_780_ = l_Lean_Meta_normLitValue(v_self_775_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v___x_782_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref_known(v___x_780_, 1);
v___x_782_ = l_Lean_Meta_normLitValue(v_rhs_725_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_795_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_795_ == 0)
{
v___x_785_ = v___x_782_;
v_isShared_786_ = v_isSharedCheck_795_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_795_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
uint8_t v___x_787_; 
v___x_787_ = lean_expr_eqv(v_a_781_, v_a_783_);
lean_dec(v_a_783_);
lean_dec(v_a_781_);
if (v___x_787_ == 0)
{
lean_object* v___x_789_; 
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v_a_778_);
v___x_789_ = v___x_785_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_778_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
else
{
lean_object* v___x_791_; lean_object* v___x_793_; 
lean_dec(v_a_778_);
v___x_791_ = lean_box(v___x_776_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_791_);
v___x_793_ = v___x_785_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec(v_a_781_);
lean_dec(v_a_778_);
v_a_796_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_782_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_782_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec(v_a_778_);
lean_dec_ref(v_rhs_725_);
v_a_804_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_780_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_780_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
else
{
lean_dec_ref(v_self_775_);
lean_dec_ref(v_rhs_725_);
return v___x_777_;
}
}
else
{
lean_object* v___x_812_; lean_object* v___x_814_; 
lean_dec_ref(v_self_775_);
lean_dec_ref(v_rhs_725_);
v___x_812_ = lean_box(v_ctor_744_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_812_);
v___x_814_ = v___x_742_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
else
{
lean_object* v_self_816_; lean_object* v___x_817_; 
lean_del_object(v___x_742_);
lean_dec_ref(v_lhs_724_);
v_self_816_ = lean_ctor_get(v_a_740_, 0);
lean_inc_ref_n(v_self_816_, 2);
lean_dec(v_a_740_);
v___x_817_ = l_Lean_Meta_isConstructorApp_x3f(v_self_816_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_892_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_892_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_892_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_892_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
if (lean_obj_tag(v_a_818_) == 1)
{
lean_object* v_val_822_; lean_object* v___x_823_; 
lean_del_object(v___x_820_);
v_val_822_ = lean_ctor_get(v_a_818_, 0);
lean_inc(v_val_822_);
lean_dec_ref_known(v_a_818_, 1);
lean_inc_ref(v_rhs_725_);
v___x_823_ = l_Lean_Meta_isConstructorApp_x3f(v_rhs_725_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_879_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_879_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_879_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_879_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
if (lean_obj_tag(v_a_824_) == 1)
{
lean_object* v_toConstantVal_828_; lean_object* v_val_829_; lean_object* v_toConstantVal_830_; lean_object* v_numParams_831_; lean_object* v_numFields_832_; lean_object* v_name_833_; lean_object* v_name_834_; uint8_t v___x_835_; 
v_toConstantVal_828_ = lean_ctor_get(v_val_822_, 0);
lean_inc_ref(v_toConstantVal_828_);
v_val_829_ = lean_ctor_get(v_a_824_, 0);
lean_inc(v_val_829_);
lean_dec_ref_known(v_a_824_, 1);
v_toConstantVal_830_ = lean_ctor_get(v_val_829_, 0);
lean_inc_ref(v_toConstantVal_830_);
lean_dec(v_val_829_);
v_numParams_831_ = lean_ctor_get(v_val_822_, 3);
lean_inc(v_numParams_831_);
v_numFields_832_ = lean_ctor_get(v_val_822_, 4);
lean_inc(v_numFields_832_);
lean_dec(v_val_822_);
v_name_833_ = lean_ctor_get(v_toConstantVal_828_, 0);
lean_inc(v_name_833_);
lean_dec_ref(v_toConstantVal_828_);
v_name_834_ = lean_ctor_get(v_toConstantVal_830_, 0);
lean_inc(v_name_834_);
lean_dec_ref(v_toConstantVal_830_);
v___x_835_ = lean_name_eq(v_name_833_, v_name_834_);
lean_dec(v_name_834_);
lean_dec(v_name_833_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_838_; 
lean_dec(v_numFields_832_);
lean_dec(v_numParams_831_);
lean_dec_ref(v_self_816_);
lean_dec_ref(v_rhs_725_);
lean_dec(v_matchCond_x3f_723_);
v___x_836_ = lean_box(v___x_738_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_836_);
v___x_838_ = v___x_826_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
else
{
lean_object* v_nargs_840_; lean_object* v_nargs_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v_dummy_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
lean_del_object(v___x_826_);
v_nargs_840_ = l_Lean_Expr_getAppNumArgs(v_self_816_);
v_nargs_841_ = l_Lean_Expr_getAppNumArgs(v_rhs_725_);
v___x_842_ = lean_nat_add(v_numParams_831_, v_numFields_832_);
lean_dec(v_numFields_832_);
v___x_843_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0));
v_dummy_844_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0);
lean_inc(v_nargs_840_);
v___x_845_ = lean_mk_array(v_nargs_840_, v_dummy_844_);
v___x_846_ = lean_unsigned_to_nat(1u);
v___x_847_ = lean_nat_sub(v_nargs_840_, v___x_846_);
lean_dec(v_nargs_840_);
v___x_848_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_816_, v___x_845_, v___x_847_);
lean_inc(v_nargs_841_);
v___x_849_ = lean_mk_array(v_nargs_841_, v_dummy_844_);
v___x_850_ = lean_nat_sub(v_nargs_841_, v___x_846_);
lean_dec(v_nargs_841_);
v___x_851_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_rhs_725_, v___x_849_, v___x_850_);
v___x_852_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v___x_842_, v___x_848_, v___x_851_, v_matchCond_x3f_723_, v_numParams_831_, v___x_843_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
lean_dec_ref(v___x_851_);
lean_dec_ref(v___x_848_);
lean_dec(v___x_842_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_866_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_866_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_866_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_866_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v_fst_857_; 
v_fst_857_ = lean_ctor_get(v_a_853_, 0);
lean_inc(v_fst_857_);
lean_dec(v_a_853_);
if (lean_obj_tag(v_fst_857_) == 0)
{
lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_858_ = lean_box(v___x_737_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_858_);
v___x_860_ = v___x_855_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
else
{
lean_object* v_val_862_; lean_object* v___x_864_; 
v_val_862_ = lean_ctor_get(v_fst_857_, 0);
lean_inc(v_val_862_);
lean_dec_ref_known(v_fst_857_, 1);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v_val_862_);
v___x_864_ = v___x_855_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_val_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
v_a_867_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_852_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_852_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
else
{
lean_object* v___x_875_; lean_object* v___x_877_; 
lean_dec(v_a_824_);
lean_dec(v_val_822_);
lean_dec_ref(v_self_816_);
lean_dec_ref(v_rhs_725_);
lean_dec(v_matchCond_x3f_723_);
v___x_875_ = lean_box(v___x_737_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_875_);
v___x_877_ = v___x_826_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec(v_val_822_);
lean_dec_ref(v_self_816_);
lean_dec_ref(v_rhs_725_);
lean_dec(v_matchCond_x3f_723_);
v_a_880_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_823_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_823_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
lean_object* v___x_888_; lean_object* v___x_890_; 
lean_dec(v_a_818_);
lean_dec_ref(v_self_816_);
lean_dec_ref(v_rhs_725_);
lean_dec(v_matchCond_x3f_723_);
v___x_888_ = lean_box(v___x_737_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_888_);
v___x_890_ = v___x_820_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec_ref(v_self_816_);
lean_dec_ref(v_rhs_725_);
lean_dec(v_matchCond_x3f_723_);
v_a_893_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_817_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_817_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec_ref(v_rhs_725_);
lean_dec_ref(v_lhs_724_);
lean_dec(v_matchCond_x3f_723_);
v_a_902_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_739_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_739_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
else
{
uint8_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
lean_dec_ref(v_rhs_725_);
lean_dec_ref(v_lhs_724_);
lean_dec(v_matchCond_x3f_723_);
v___x_910_ = 0;
v___x_911_ = lean_box(v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(lean_object* v_upperBound_913_, lean_object* v___x_914_, lean_object* v___x_915_, lean_object* v_matchCond_x3f_916_, lean_object* v_a_917_, lean_object* v_b_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
uint8_t v___x_930_; 
v___x_930_ = lean_nat_dec_lt(v_a_917_, v_upperBound_913_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; 
lean_dec(v_a_917_);
lean_dec(v_matchCond_x3f_916_);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v_b_918_);
return v___x_931_;
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec_ref(v_b_918_);
v___x_932_ = l_Lean_instInhabitedExpr;
v___x_933_ = lean_box(0);
v___x_934_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0));
v___x_935_ = lean_array_get_borrowed(v___x_932_, v___x_914_, v_a_917_);
v___x_936_ = lean_array_get_borrowed(v___x_932_, v___x_915_, v_a_917_);
lean_inc(v___x_936_);
lean_inc(v___x_935_);
lean_inc(v_matchCond_x3f_916_);
v___x_937_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v_matchCond_x3f_916_, v___x_935_, v___x_936_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_952_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_952_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_952_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_952_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
uint8_t v___x_942_; 
v___x_942_ = lean_unbox(v_a_938_);
lean_dec(v_a_938_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; 
lean_del_object(v___x_940_);
v___x_943_ = lean_unsigned_to_nat(1u);
v___x_944_ = lean_nat_add(v_a_917_, v___x_943_);
lean_dec(v_a_917_);
v_a_917_ = v___x_944_;
v_b_918_ = v___x_934_;
goto _start;
}
else
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_950_; 
lean_dec(v_a_917_);
lean_dec(v_matchCond_x3f_916_);
v___x_946_ = lean_box(v___x_930_);
v___x_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
v___x_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
lean_ctor_set(v___x_948_, 1, v___x_933_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_948_);
v___x_950_ = v___x_940_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec(v_a_917_);
lean_dec(v_matchCond_x3f_916_);
v_a_953_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_937_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_937_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_961_ = _args[0];
lean_object* v___x_962_ = _args[1];
lean_object* v___x_963_ = _args[2];
lean_object* v_matchCond_x3f_964_ = _args[3];
lean_object* v_a_965_ = _args[4];
lean_object* v_b_966_ = _args[5];
lean_object* v___y_967_ = _args[6];
lean_object* v___y_968_ = _args[7];
lean_object* v___y_969_ = _args[8];
lean_object* v___y_970_ = _args[9];
lean_object* v___y_971_ = _args[10];
lean_object* v___y_972_ = _args[11];
lean_object* v___y_973_ = _args[12];
lean_object* v___y_974_ = _args[13];
lean_object* v___y_975_ = _args[14];
lean_object* v___y_976_ = _args[15];
lean_object* v___y_977_ = _args[16];
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v_upperBound_961_, v___x_962_, v___x_963_, v_matchCond_x3f_964_, v_a_965_, v_b_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___x_963_);
lean_dec_ref(v___x_962_);
lean_dec(v_upperBound_961_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___boxed(lean_object* v_matchCond_x3f_979_, lean_object* v_lhs_980_, lean_object* v_rhs_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v_matchCond_x3f_979_, v_lhs_980_, v_rhs_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec(v_a_982_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(lean_object* v_upperBound_994_, lean_object* v___x_995_, lean_object* v___x_996_, lean_object* v_matchCond_x3f_997_, lean_object* v_inst_998_, lean_object* v_R_999_, lean_object* v_a_1000_, lean_object* v_b_1001_, lean_object* v_c_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v_upperBound_994_, v___x_995_, v___x_996_, v_matchCond_x3f_997_, v_a_1000_, v_b_1001_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_1015_ = _args[0];
lean_object* v___x_1016_ = _args[1];
lean_object* v___x_1017_ = _args[2];
lean_object* v_matchCond_x3f_1018_ = _args[3];
lean_object* v_inst_1019_ = _args[4];
lean_object* v_R_1020_ = _args[5];
lean_object* v_a_1021_ = _args[6];
lean_object* v_b_1022_ = _args[7];
lean_object* v_c_1023_ = _args[8];
lean_object* v___y_1024_ = _args[9];
lean_object* v___y_1025_ = _args[10];
lean_object* v___y_1026_ = _args[11];
lean_object* v___y_1027_ = _args[12];
lean_object* v___y_1028_ = _args[13];
lean_object* v___y_1029_ = _args[14];
lean_object* v___y_1030_ = _args[15];
lean_object* v___y_1031_ = _args[16];
lean_object* v___y_1032_ = _args[17];
lean_object* v___y_1033_ = _args[18];
lean_object* v___y_1034_ = _args[19];
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(v_upperBound_1015_, v___x_1016_, v___x_1017_, v_matchCond_x3f_1018_, v_inst_1019_, v_R_1020_, v_a_1021_, v_b_1022_, v_c_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___x_1017_);
lean_dec_ref(v___x_1016_);
lean_dec(v_upperBound_1015_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(lean_object* v_e_1036_, lean_object* v_matchCond_x3f_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_e_1036_);
if (lean_obj_tag(v___x_1049_) == 1)
{
lean_object* v_val_1050_; lean_object* v_snd_1051_; lean_object* v_fst_1052_; lean_object* v_snd_1053_; lean_object* v___x_1054_; 
v_val_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_val_1050_);
lean_dec_ref_known(v___x_1049_, 1);
v_snd_1051_ = lean_ctor_get(v_val_1050_, 1);
lean_inc(v_snd_1051_);
lean_dec(v_val_1050_);
v_fst_1052_ = lean_ctor_get(v_snd_1051_, 0);
lean_inc(v_fst_1052_);
v_snd_1053_ = lean_ctor_get(v_snd_1051_, 1);
lean_inc(v_snd_1053_);
lean_dec(v_snd_1051_);
v___x_1054_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v_matchCond_x3f_1037_, v_fst_1052_, v_snd_1053_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
return v___x_1054_;
}
else
{
uint8_t v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
lean_dec(v___x_1049_);
lean_dec(v_matchCond_x3f_1037_);
v___x_1055_ = 0;
v___x_1056_ = lean_box(v___x_1055_);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp___boxed(lean_object* v_e_1058_, lean_object* v_matchCond_x3f_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_e_1058_, v_matchCond_x3f_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_e_1058_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(uint8_t v___x_1072_, lean_object* v_snd_1073_, lean_object* v_____r_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1086_ = lean_box(v___x_1072_);
v___x_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
v___x_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v_snd_1073_);
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0___boxed(lean_object* v___x_1091_, lean_object* v_snd_1092_, lean_object* v_____r_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
uint8_t v___x_23471__boxed_1105_; lean_object* v_res_1106_; 
v___x_23471__boxed_1105_ = lean_unbox(v___x_1091_);
v_res_1106_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_23471__boxed_1105_, v_snd_1092_, v_____r_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec(v___y_1094_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(lean_object* v_msgData_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v___x_1113_; lean_object* v_env_1114_; uint8_t v___x_1115_; lean_object* v_env_1116_; lean_object* v___x_1117_; lean_object* v_toCold_1118_; lean_object* v_mctx_1119_; lean_object* v_lctx_1120_; lean_object* v_options_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1113_ = lean_st_ref_get(v___y_1111_);
v_env_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc_ref(v_env_1114_);
lean_dec(v___x_1113_);
v___x_1115_ = 0;
v_env_1116_ = l_Lean_Environment_setRecordingDeps(v_env_1114_, v___x_1115_);
v___x_1117_ = lean_st_ref_get(v___y_1109_);
v_toCold_1118_ = lean_ctor_get(v___y_1110_, 0);
v_mctx_1119_ = lean_ctor_get(v___x_1117_, 0);
lean_inc_ref(v_mctx_1119_);
lean_dec(v___x_1117_);
v_lctx_1120_ = lean_ctor_get(v___y_1108_, 2);
v_options_1121_ = lean_ctor_get(v_toCold_1118_, 2);
lean_inc_ref(v_options_1121_);
lean_inc_ref(v_lctx_1120_);
v___x_1122_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1122_, 0, v_env_1116_);
lean_ctor_set(v___x_1122_, 1, v_mctx_1119_);
lean_ctor_set(v___x_1122_, 2, v_lctx_1120_);
lean_ctor_set(v___x_1122_, 3, v_options_1121_);
v___x_1123_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
lean_ctor_set(v___x_1123_, 1, v_msgData_1107_);
v___x_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0___boxed(lean_object* v_msgData_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(v_msgData_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
return v_res_1131_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1132_; double v___x_1133_; 
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_float_of_nat(v___x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(lean_object* v_cls_1137_, lean_object* v_msg_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_ref_1144_; lean_object* v___x_1145_; lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1191_; 
v_ref_1144_ = lean_ctor_get(v___y_1141_, 2);
v___x_1145_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(v_msg_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1191_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1191_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v_traceState_1151_; lean_object* v_env_1152_; lean_object* v_nextMacroScope_1153_; lean_object* v_ngen_1154_; lean_object* v_auxDeclNGen_1155_; lean_object* v_cache_1156_; lean_object* v_recordedDeps_1157_; lean_object* v_messages_1158_; lean_object* v_infoState_1159_; lean_object* v_snapshotTasks_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1190_; 
v___x_1150_ = lean_st_ref_take(v___y_1142_);
v_traceState_1151_ = lean_ctor_get(v___x_1150_, 4);
v_env_1152_ = lean_ctor_get(v___x_1150_, 0);
v_nextMacroScope_1153_ = lean_ctor_get(v___x_1150_, 1);
v_ngen_1154_ = lean_ctor_get(v___x_1150_, 2);
v_auxDeclNGen_1155_ = lean_ctor_get(v___x_1150_, 3);
v_cache_1156_ = lean_ctor_get(v___x_1150_, 5);
v_recordedDeps_1157_ = lean_ctor_get(v___x_1150_, 6);
v_messages_1158_ = lean_ctor_get(v___x_1150_, 7);
v_infoState_1159_ = lean_ctor_get(v___x_1150_, 8);
v_snapshotTasks_1160_ = lean_ctor_get(v___x_1150_, 9);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1162_ = v___x_1150_;
v_isShared_1163_ = v_isSharedCheck_1190_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_snapshotTasks_1160_);
lean_inc(v_infoState_1159_);
lean_inc(v_messages_1158_);
lean_inc(v_recordedDeps_1157_);
lean_inc(v_cache_1156_);
lean_inc(v_traceState_1151_);
lean_inc(v_auxDeclNGen_1155_);
lean_inc(v_ngen_1154_);
lean_inc(v_nextMacroScope_1153_);
lean_inc(v_env_1152_);
lean_dec(v___x_1150_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1190_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
uint64_t v_tid_1164_; lean_object* v_traces_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1189_; 
v_tid_1164_ = lean_ctor_get_uint64(v_traceState_1151_, sizeof(void*)*1);
v_traces_1165_ = lean_ctor_get(v_traceState_1151_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_traceState_1151_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1167_ = v_traceState_1151_;
v_isShared_1168_ = v_isSharedCheck_1189_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_traces_1165_);
lean_dec(v_traceState_1151_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1189_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; double v___x_1171_; uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1169_ = lean_box(0);
v___x_1170_ = lean_box(0);
v___x_1171_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0);
v___x_1172_ = 0;
v___x_1173_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1));
v___x_1174_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1174_, 0, v_cls_1137_);
lean_ctor_set(v___x_1174_, 1, v___x_1170_);
lean_ctor_set(v___x_1174_, 2, v___x_1173_);
lean_ctor_set_float(v___x_1174_, sizeof(void*)*3, v___x_1171_);
lean_ctor_set_float(v___x_1174_, sizeof(void*)*3 + 8, v___x_1171_);
lean_ctor_set_uint8(v___x_1174_, sizeof(void*)*3 + 16, v___x_1172_);
v___x_1175_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__2));
v___x_1176_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1174_);
lean_ctor_set(v___x_1176_, 1, v_a_1146_);
lean_ctor_set(v___x_1176_, 2, v___x_1175_);
lean_inc(v_ref_1144_);
v___x_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1177_, 0, v_ref_1144_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___x_1178_ = l_Lean_PersistentArray_push___redArg(v_traces_1165_, v___x_1177_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1178_);
v___x_1180_ = v___x_1167_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1178_);
lean_ctor_set_uint64(v_reuseFailAlloc_1188_, sizeof(void*)*1, v_tid_1164_);
v___x_1180_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1182_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 4, v___x_1180_);
v___x_1182_ = v___x_1162_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_env_1152_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_nextMacroScope_1153_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v_ngen_1154_);
lean_ctor_set(v_reuseFailAlloc_1187_, 3, v_auxDeclNGen_1155_);
lean_ctor_set(v_reuseFailAlloc_1187_, 4, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1187_, 5, v_cache_1156_);
lean_ctor_set(v_reuseFailAlloc_1187_, 6, v_recordedDeps_1157_);
lean_ctor_set(v_reuseFailAlloc_1187_, 7, v_messages_1158_);
lean_ctor_set(v_reuseFailAlloc_1187_, 8, v_infoState_1159_);
lean_ctor_set(v_reuseFailAlloc_1187_, 9, v_snapshotTasks_1160_);
v___x_1182_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = lean_st_ref_put(v___y_1142_, v___x_1182_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1169_);
v___x_1185_ = v___x_1148_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1169_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___boxed(lean_object* v_cls_1192_, lean_object* v_msg_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1192_, v_msg_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
return v_res_1199_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1210_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_1211_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5));
v___x_1212_ = l_Lean_Name_append(v___x_1211_, v___x_1210_);
return v___x_1212_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__7));
v___x_1215_ = l_Lean_stringToMessageData(v___x_1214_);
return v___x_1215_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__9));
v___x_1218_ = l_Lean_stringToMessageData(v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(uint8_t v___x_1219_, lean_object* v_e_1220_, lean_object* v_a_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___y_1234_; lean_object* v_snd_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1318_; 
v_snd_1254_ = lean_ctor_get(v_a_1221_, 1);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_a_1221_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; 
v_unused_1319_ = lean_ctor_get(v_a_1221_, 0);
lean_dec(v_unused_1319_);
v___x_1256_ = v_a_1221_;
v_isShared_1257_ = v_isSharedCheck_1318_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_snd_1254_);
lean_dec(v_a_1221_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1318_;
goto v_resetjp_1255_;
}
v___jp_1233_:
{
if (lean_obj_tag(v___y_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1245_; 
v_a_1235_ = lean_ctor_get(v___y_1234_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___y_1234_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1237_ = v___y_1234_;
v_isShared_1238_ = v_isSharedCheck_1245_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___y_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1245_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
if (lean_obj_tag(v_a_1235_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1241_; 
lean_dec_ref(v_e_1220_);
v_a_1239_ = lean_ctor_get(v_a_1235_, 0);
lean_inc(v_a_1239_);
lean_dec_ref_known(v_a_1235_, 1);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v_a_1239_);
v___x_1241_ = v___x_1237_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1239_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
else
{
lean_object* v_a_1243_; 
lean_del_object(v___x_1237_);
v_a_1243_ = lean_ctor_get(v_a_1235_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v_a_1235_, 1);
v_a_1221_ = v_a_1243_;
goto _start;
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec_ref(v_e_1220_);
v_a_1246_ = lean_ctor_get(v___y_1234_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___y_1234_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___y_1234_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___y_1234_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; 
v___x_1258_ = lean_box(0);
if (lean_obj_tag(v_snd_1254_) == 7)
{
lean_object* v_binderType_1259_; lean_object* v_body_1260_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v_binderType_1259_ = lean_ctor_get(v_snd_1254_, 1);
v_body_1260_ = lean_ctor_get(v_snd_1254_, 2);
lean_inc_ref(v_e_1220_);
v___x_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1264_, 0, v_e_1220_);
v___x_1265_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_binderType_1259_, v___x_1264_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; uint8_t v___x_1267_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1265_, 1);
v___x_1267_ = lean_unbox(v_a_1266_);
lean_dec(v_a_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1269_; 
lean_inc_ref(v_body_1260_);
lean_dec_ref_known(v_snd_1254_, 3);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v_body_1260_);
lean_ctor_set(v___x_1256_, 0, v___x_1258_);
v___x_1269_ = v___x_1256_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_body_1260_);
v___x_1269_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
v_a_1221_ = v___x_1269_;
goto _start;
}
}
else
{
lean_object* v_toCold_1272_; lean_object* v_options_1273_; uint8_t v_hasTrace_1274_; 
lean_del_object(v___x_1256_);
v_toCold_1272_ = lean_ctor_get(v___y_1230_, 0);
v_options_1273_ = lean_ctor_get(v_toCold_1272_, 2);
v_hasTrace_1274_ = lean_ctor_get_uint8(v_options_1273_, sizeof(void*)*1);
if (v_hasTrace_1274_ == 0)
{
goto v___jp_1261_;
}
else
{
lean_object* v_inheritedTraceOptions_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
v_inheritedTraceOptions_1275_ = lean_ctor_get(v_toCold_1272_, 11);
v___x_1276_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_1277_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_1278_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1275_, v_options_1273_, v___x_1277_);
if (v___x_1278_ == 0)
{
goto v___jp_1261_;
}
else
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_Meta_Grind_updateLastTag(v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_dec_ref_known(v___x_1279_, 1);
v___x_1280_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8);
lean_inc_ref(v_snd_1254_);
v___x_1281_ = l_Lean_indentExpr(v_snd_1254_);
v___x_1282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1280_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10);
v___x_1284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
lean_inc_ref(v_binderType_1259_);
v___x_1285_ = l_Lean_indentExpr(v_binderType_1259_);
v___x_1286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_1276_, v___x_1286_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1289_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
v___x_1289_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_1219_, v_snd_1254_, v_a_1288_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
v___y_1234_ = v___x_1289_;
goto v___jp_1233_;
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec_ref_known(v_snd_1254_, 3);
lean_dec_ref(v_e_1220_);
v_a_1290_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1287_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1287_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec_ref_known(v_snd_1254_, 3);
lean_dec_ref(v_e_1220_);
v_a_1298_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1279_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1279_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec_ref_known(v_snd_1254_, 3);
lean_del_object(v___x_1256_);
lean_dec_ref(v_e_1220_);
v_a_1306_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1265_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1265_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
v___jp_1261_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_box(0);
v___x_1263_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_1219_, v_snd_1254_, v___x_1262_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
v___y_1234_ = v___x_1263_;
goto v___jp_1233_;
}
}
else
{
lean_object* v___x_1315_; 
lean_dec_ref(v_e_1220_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1258_);
v___x_1315_ = v___x_1256_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_snd_1254_);
v___x_1315_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1316_; 
v___x_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
return v___x_1316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___boxed(lean_object* v___x_1320_, lean_object* v_e_1321_, lean_object* v_a_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
uint8_t v___x_23686__boxed_1334_; lean_object* v_res_1335_; 
v___x_23686__boxed_1334_ = lean_unbox(v___x_1320_);
v_res_1335_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_23686__boxed_1334_, v_e_1321_, v_a_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec(v___y_1323_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(lean_object* v_e_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v___x_1352_; 
lean_inc_ref(v_e_1336_);
v___x_1352_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1336_, v_a_1344_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1353_);
lean_dec_ref_known(v___x_1352_, 1);
v___x_1354_ = l_Lean_Expr_cleanupAnnotations(v_a_1353_);
lean_dec(v_a_1353_);
v___x_1355_ = l_Lean_Expr_isApp(v___x_1354_);
if (v___x_1355_ == 0)
{
lean_dec_ref(v___x_1354_);
lean_dec_ref(v_e_1336_);
goto v___jp_1348_;
}
else
{
lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1356_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1354_);
v___x_1357_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_1358_ = l_Lean_Expr_isConstOf(v___x_1356_, v___x_1357_);
lean_dec_ref(v___x_1356_);
if (v___x_1358_ == 0)
{
lean_dec_ref(v___x_1354_);
lean_dec_ref(v_e_1336_);
goto v___jp_1348_;
}
else
{
lean_object* v_arg_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v_arg_1359_ = lean_ctor_get(v___x_1354_, 1);
lean_inc_ref(v_arg_1359_);
lean_dec_ref(v___x_1354_);
v___x_1360_ = lean_box(0);
v___x_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
lean_ctor_set(v___x_1361_, 1, v_arg_1359_);
v___x_1362_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_1358_, v_e_1336_, v___x_1361_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1377_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1365_ = v___x_1362_;
v_isShared_1366_ = v_isSharedCheck_1377_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1362_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1377_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v_fst_1367_; 
v_fst_1367_ = lean_ctor_get(v_a_1363_, 0);
lean_inc(v_fst_1367_);
lean_dec(v_a_1363_);
if (lean_obj_tag(v_fst_1367_) == 0)
{
uint8_t v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1368_ = 0;
v___x_1369_ = lean_box(v___x_1368_);
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
else
{
lean_object* v_val_1373_; lean_object* v___x_1375_; 
v_val_1373_ = lean_ctor_get(v_fst_1367_, 0);
lean_inc(v_val_1373_);
lean_dec_ref_known(v_fst_1367_, 1);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v_val_1373_);
v___x_1375_ = v___x_1365_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_val_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
v_a_1378_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1362_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1362_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec_ref(v_e_1336_);
v_a_1386_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1352_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1352_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
v___jp_1348_:
{
uint8_t v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1349_ = 0;
v___x_1350_ = lean_box(v___x_1349_);
v___x_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
return v___x_1351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied___boxed(lean_object* v_e_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
lean_dec(v_a_1396_);
lean_dec(v_a_1395_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(lean_object* v_cls_1407_, lean_object* v_msg_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1407_, v_msg_1408_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___boxed(lean_object* v_cls_1421_, lean_object* v_msg_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(v_cls_1421_, v_msg_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec(v___y_1423_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(uint8_t v___x_1435_, lean_object* v_e_1436_, lean_object* v_inst_1437_, lean_object* v_a_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_1435_, v_e_1436_, v_a_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___boxed(lean_object* v___x_1451_, lean_object* v_e_1452_, lean_object* v_inst_1453_, lean_object* v_a_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
uint8_t v___x_24047__boxed_1466_; lean_object* v_res_1467_; 
v___x_24047__boxed_1466_ = lean_unbox(v___x_1451_);
v_res_1467_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(v___x_24047__boxed_1466_, v_e_1452_, v_inst_1453_, v_a_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec(v___y_1455_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(lean_object* v_k_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v_b_1475_, lean_object* v_c_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v___x_1482_; 
lean_inc(v___y_1480_);
lean_inc_ref(v___y_1479_);
lean_inc(v___y_1478_);
lean_inc_ref(v___y_1477_);
lean_inc(v___y_1474_);
lean_inc_ref(v___y_1473_);
lean_inc(v___y_1472_);
lean_inc_ref(v___y_1471_);
lean_inc(v___y_1470_);
lean_inc(v___y_1469_);
v___x_1482_ = lean_apply_13(v_k_1468_, v_b_1475_, v_c_1476_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, lean_box(0));
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed(lean_object* v_k_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v_b_1490_, lean_object* v_c_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(v_k_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v_b_1490_, v_c_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec(v___y_1484_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(lean_object* v_type_1498_, lean_object* v_k_1499_, uint8_t v_cleanupAnnotations_1500_, uint8_t v_whnfType_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___f_1513_; lean_object* v___x_1514_; 
lean_inc(v___y_1507_);
lean_inc_ref(v___y_1506_);
lean_inc(v___y_1505_);
lean_inc_ref(v___y_1504_);
lean_inc(v___y_1503_);
lean_inc(v___y_1502_);
v___f_1513_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1513_, 0, v_k_1499_);
lean_closure_set(v___f_1513_, 1, v___y_1502_);
lean_closure_set(v___f_1513_, 2, v___y_1503_);
lean_closure_set(v___f_1513_, 3, v___y_1504_);
lean_closure_set(v___f_1513_, 4, v___y_1505_);
lean_closure_set(v___f_1513_, 5, v___y_1506_);
lean_closure_set(v___f_1513_, 6, v___y_1507_);
v___x_1514_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1498_, v___f_1513_, v_cleanupAnnotations_1500_, v_whnfType_1501_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
if (lean_obj_tag(v___x_1514_) == 0)
{
return v___x_1514_;
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___boxed(lean_object* v_type_1523_, lean_object* v_k_1524_, lean_object* v_cleanupAnnotations_1525_, lean_object* v_whnfType_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1538_; uint8_t v_whnfType_boxed_1539_; lean_object* v_res_1540_; 
v_cleanupAnnotations_boxed_1538_ = lean_unbox(v_cleanupAnnotations_1525_);
v_whnfType_boxed_1539_ = lean_unbox(v_whnfType_1526_);
v_res_1540_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_1523_, v_k_1524_, v_cleanupAnnotations_boxed_1538_, v_whnfType_boxed_1539_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec(v___y_1527_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(lean_object* v_00_u03b1_1541_, lean_object* v_type_1542_, lean_object* v_k_1543_, uint8_t v_cleanupAnnotations_1544_, uint8_t v_whnfType_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_1542_, v_k_1543_, v_cleanupAnnotations_1544_, v_whnfType_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___boxed(lean_object* v_00_u03b1_1558_, lean_object* v_type_1559_, lean_object* v_k_1560_, lean_object* v_cleanupAnnotations_1561_, lean_object* v_whnfType_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1574_; uint8_t v_whnfType_boxed_1575_; lean_object* v_res_1576_; 
v_cleanupAnnotations_boxed_1574_ = lean_unbox(v_cleanupAnnotations_1561_);
v_whnfType_boxed_1575_ = lean_unbox(v_whnfType_1562_);
v_res_1576_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(v_00_u03b1_1558_, v_type_1559_, v_k_1560_, v_cleanupAnnotations_boxed_1574_, v_whnfType_boxed_1575_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec(v___y_1563_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed(lean_object** _args){
lean_object* v_e_1580_ = _args[0];
lean_object* v_name_1581_ = _args[1];
lean_object* v_name_1582_ = _args[2];
lean_object* v_a_1583_ = _args[3];
lean_object* v_a_1584_ = _args[4];
lean_object* v_xs_1585_ = _args[5];
lean_object* v_x_1586_ = _args[6];
lean_object* v___y_1587_ = _args[7];
lean_object* v___y_1588_ = _args[8];
lean_object* v___y_1589_ = _args[9];
lean_object* v___y_1590_ = _args[10];
lean_object* v___y_1591_ = _args[11];
lean_object* v___y_1592_ = _args[12];
lean_object* v___y_1593_ = _args[13];
lean_object* v___y_1594_ = _args[14];
lean_object* v___y_1595_ = _args[15];
lean_object* v___y_1596_ = _args[16];
lean_object* v___y_1597_ = _args[17];
_start:
{
uint8_t v_a_80064__boxed_1598_; lean_object* v_res_1599_; 
v_a_80064__boxed_1598_ = lean_unbox(v_a_1583_);
v_res_1599_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(v_e_1580_, v_name_1581_, v_name_1582_, v_a_80064__boxed_1598_, v_a_1584_, v_xs_1585_, v_x_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v_x_1586_);
lean_dec_ref(v_xs_1585_);
lean_dec(v_name_1582_);
lean_dec(v_name_1581_);
return v_res_1599_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1(void){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__0));
v___x_1602_ = l_Lean_stringToMessageData(v___x_1601_);
return v___x_1602_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__2));
v___x_1605_ = l_Lean_stringToMessageData(v___x_1604_);
return v___x_1605_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5(void){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__4));
v___x_1608_ = l_Lean_stringToMessageData(v___x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(lean_object* v_e_1609_, lean_object* v_h_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_){
_start:
{
uint8_t v___y_1626_; uint8_t v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; uint8_t v___y_1630_; lean_object* v_h_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; uint8_t v___y_1827_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v_toCold_2001_; lean_object* v_options_2002_; uint8_t v_hasTrace_2003_; 
v_toCold_2001_ = lean_ctor_get(v_a_1619_, 0);
v_options_2002_ = lean_ctor_get(v_toCold_2001_, 2);
v_hasTrace_2003_ = lean_ctor_get_uint8(v_options_2002_, sizeof(void*)*1);
if (v_hasTrace_2003_ == 0)
{
v___y_1904_ = v_a_1611_;
v___y_1905_ = v_a_1612_;
v___y_1906_ = v_a_1613_;
v___y_1907_ = v_a_1614_;
v___y_1908_ = v_a_1615_;
v___y_1909_ = v_a_1616_;
v___y_1910_ = v_a_1617_;
v___y_1911_ = v_a_1618_;
v___y_1912_ = v_a_1619_;
v___y_1913_ = v_a_1620_;
goto v___jp_1903_;
}
else
{
lean_object* v_inheritedTraceOptions_2004_; lean_object* v_cls_2005_; lean_object* v___x_2006_; uint8_t v___x_2007_; 
v_inheritedTraceOptions_2004_ = lean_ctor_get(v_toCold_2001_, 11);
v_cls_2005_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_2006_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_2007_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2004_, v_options_2002_, v___x_2006_);
if (v___x_2007_ == 0)
{
v___y_1904_ = v_a_1611_;
v___y_1905_ = v_a_1612_;
v___y_1906_ = v_a_1613_;
v___y_1907_ = v_a_1614_;
v___y_1908_ = v_a_1615_;
v___y_1909_ = v_a_1616_;
v___y_1910_ = v_a_1617_;
v___y_1911_ = v_a_1618_;
v___y_1912_ = v_a_1619_;
v___y_1913_ = v_a_1620_;
goto v___jp_1903_;
}
else
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_Meta_Grind_updateLastTag(v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v___x_2009_; 
lean_dec_ref_known(v___x_2008_, 1);
lean_inc(v_a_1620_);
lean_inc_ref(v_a_1619_);
lean_inc(v_a_1618_);
lean_inc_ref(v_a_1617_);
lean_inc_ref(v_h_1610_);
v___x_2009_ = lean_infer_type(v_h_1610_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref_known(v___x_2009_, 1);
v___x_2011_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5);
v___x_2012_ = l_Lean_MessageData_ofExpr(v_a_2010_);
v___x_2013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2011_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_2005_, v___x_2013_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_dec_ref_known(v___x_2014_, 1);
v___y_1904_ = v_a_1611_;
v___y_1905_ = v_a_1612_;
v___y_1906_ = v_a_1613_;
v___y_1907_ = v_a_1614_;
v___y_1908_ = v_a_1615_;
v___y_1909_ = v_a_1616_;
v___y_1910_ = v_a_1617_;
v___y_1911_ = v_a_1618_;
v___y_1912_ = v_a_1619_;
v___y_1913_ = v_a_1620_;
goto v___jp_1903_;
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec_ref(v_h_1610_);
lean_dec_ref(v_e_1609_);
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
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
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec_ref(v_h_1610_);
lean_dec_ref(v_e_1609_);
v_a_2023_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_2009_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2009_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec_ref(v_h_1610_);
lean_dec_ref(v_e_1609_);
v_a_2031_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2008_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2008_);
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
}
v___jp_1622_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = lean_box(0);
v___x_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
return v___x_1624_;
}
v___jp_1625_:
{
if (v___y_1630_ == 0)
{
lean_dec_ref(v_e_1609_);
if (v___y_1627_ == 0)
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_dec_ref(v_h_1631_);
lean_dec_ref(v___y_1629_);
lean_dec_ref(v___y_1628_);
v___x_1642_ = lean_box(0);
v___x_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
return v___x_1643_;
}
else
{
lean_object* v___x_1644_; 
lean_inc_ref(v___y_1629_);
v___x_1644_ = l_Lean_Meta_normLitValue(v___y_1629_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1646_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v___x_1644_, 1);
lean_inc_ref(v___y_1628_);
v___x_1646_ = l_Lean_Meta_normLitValue(v___y_1628_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1686_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1686_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1686_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
uint8_t v___x_1651_; 
v___x_1651_ = lean_expr_eqv(v_a_1645_, v_a_1647_);
lean_dec(v_a_1647_);
lean_dec(v_a_1645_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; 
lean_del_object(v___x_1649_);
v___x_1652_ = l_Lean_Meta_mkEq(v___y_1629_, v___y_1628_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref_known(v___x_1652_, 1);
v___x_1654_ = l_Lean_mkNot(v_a_1653_);
v___x_1655_ = l_Lean_Meta_mkDecideProof(v___x_1654_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1665_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1665_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1665_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1660_ = l_Lean_Expr_app___override(v_a_1656_, v_h_1631_);
v___x_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1661_);
v___x_1663_ = v___x_1658_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
lean_dec_ref(v_h_1631_);
v_a_1666_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1655_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1655_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_dec_ref(v_h_1631_);
v_a_1674_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1652_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1652_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
else
{
lean_object* v___x_1682_; lean_object* v___x_1684_; 
lean_dec_ref(v_h_1631_);
lean_dec_ref(v___y_1629_);
lean_dec_ref(v___y_1628_);
v___x_1682_ = lean_box(0);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1682_);
v___x_1684_ = v___x_1649_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1682_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec(v_a_1645_);
lean_dec_ref(v_h_1631_);
lean_dec_ref(v___y_1629_);
lean_dec_ref(v___y_1628_);
v_a_1687_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1646_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1646_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_dec_ref(v_h_1631_);
lean_dec_ref(v___y_1629_);
lean_dec_ref(v___y_1628_);
v_a_1695_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1644_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1644_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
else
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_Meta_isConstructorApp_x3f(v___y_1629_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1804_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1706_ = v___x_1703_;
v_isShared_1707_ = v_isSharedCheck_1804_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1703_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1804_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
if (lean_obj_tag(v_a_1704_) == 1)
{
lean_object* v_val_1708_; lean_object* v___x_1709_; 
lean_del_object(v___x_1706_);
v_val_1708_ = lean_ctor_get(v_a_1704_, 0);
lean_inc(v_val_1708_);
lean_dec_ref_known(v_a_1704_, 1);
v___x_1709_ = l_Lean_Meta_isConstructorApp_x3f(v___y_1628_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1791_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1712_ = v___x_1709_;
v_isShared_1713_ = v_isSharedCheck_1791_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1709_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1791_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
if (lean_obj_tag(v_a_1710_) == 1)
{
lean_object* v_val_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1786_; 
lean_del_object(v___x_1712_);
v_val_1714_ = lean_ctor_get(v_a_1710_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_a_1710_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1716_ = v_a_1710_;
v_isShared_1717_ = v_isSharedCheck_1786_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_val_1714_);
lean_dec(v_a_1710_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1786_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_1636_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1720_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
v___x_1720_ = l_Lean_Meta_mkNoConfusion(v_a_1719_, v_h_1631_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_toConstantVal_1721_; lean_object* v_toConstantVal_1722_; lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1769_; 
v_toConstantVal_1721_ = lean_ctor_get(v_val_1708_, 0);
lean_inc_ref(v_toConstantVal_1721_);
lean_dec(v_val_1708_);
v_toConstantVal_1722_ = lean_ctor_get(v_val_1714_, 0);
lean_inc_ref(v_toConstantVal_1722_);
lean_dec(v_val_1714_);
v_a_1723_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1725_ = v___x_1720_;
v_isShared_1726_ = v_isSharedCheck_1769_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1720_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1769_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v_name_1727_; lean_object* v_name_1728_; uint8_t v___x_1729_; 
v_name_1727_ = lean_ctor_get(v_toConstantVal_1721_, 0);
lean_inc(v_name_1727_);
lean_dec_ref(v_toConstantVal_1721_);
v_name_1728_ = lean_ctor_get(v_toConstantVal_1722_, 0);
lean_inc(v_name_1728_);
lean_dec_ref(v_toConstantVal_1722_);
v___x_1729_ = lean_name_eq(v_name_1727_, v_name_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1731_; 
lean_dec(v_name_1728_);
lean_dec(v_name_1727_);
lean_dec_ref(v_e_1609_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v_a_1723_);
v___x_1731_ = v___x_1716_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1723_);
v___x_1731_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1733_; 
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1731_);
v___x_1733_ = v___x_1725_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
else
{
lean_object* v___x_1736_; lean_object* v___f_1737_; uint8_t v___x_1738_; lean_object* v___x_1739_; 
lean_del_object(v___x_1725_);
lean_del_object(v___x_1716_);
v___x_1736_ = lean_box(v___y_1626_);
lean_inc(v_a_1723_);
v___f_1737_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed), 18, 5);
lean_closure_set(v___f_1737_, 0, v_e_1609_);
lean_closure_set(v___f_1737_, 1, v_name_1727_);
lean_closure_set(v___f_1737_, 2, v_name_1728_);
lean_closure_set(v___f_1737_, 3, v___x_1736_);
lean_closure_set(v___f_1737_, 4, v_a_1723_);
v___x_1738_ = 0;
lean_inc(v___y_1641_);
lean_inc_ref(v___y_1640_);
lean_inc(v___y_1639_);
lean_inc_ref(v___y_1638_);
v___x_1739_ = lean_infer_type(v_a_1723_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1741_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v___x_1741_ = l_Lean_Meta_whnfD(v_a_1740_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1752_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1744_ = v___x_1741_;
v_isShared_1745_ = v_isSharedCheck_1752_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1741_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1752_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
if (lean_obj_tag(v_a_1742_) == 7)
{
lean_object* v_binderType_1746_; lean_object* v___x_1747_; 
lean_del_object(v___x_1744_);
v_binderType_1746_ = lean_ctor_get(v_a_1742_, 1);
lean_inc_ref(v_binderType_1746_);
lean_dec_ref_known(v_a_1742_, 3);
v___x_1747_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_binderType_1746_, v___f_1737_, v___x_1738_, v___x_1738_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
return v___x_1747_;
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1750_; 
lean_dec(v_a_1742_);
lean_dec_ref(v___f_1737_);
v___x_1748_ = lean_box(0);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1748_);
v___x_1750_ = v___x_1744_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec_ref(v___f_1737_);
v_a_1753_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1741_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1741_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec_ref(v___f_1737_);
v_a_1761_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1739_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1739_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_del_object(v___x_1716_);
lean_dec(v_val_1714_);
lean_dec(v_val_1708_);
lean_dec_ref(v_e_1609_);
v_a_1770_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1720_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1720_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_del_object(v___x_1716_);
lean_dec(v_val_1714_);
lean_dec(v_val_1708_);
lean_dec_ref(v_h_1631_);
lean_dec_ref(v_e_1609_);
v_a_1778_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1718_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1718_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
}
else
{
lean_object* v___x_1787_; lean_object* v___x_1789_; 
lean_dec(v_a_1710_);
lean_dec(v_val_1708_);
lean_dec_ref(v_h_1631_);
lean_dec_ref(v_e_1609_);
v___x_1787_ = lean_box(0);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v___x_1787_);
v___x_1789_ = v___x_1712_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
lean_dec(v_val_1708_);
lean_dec_ref(v_h_1631_);
lean_dec_ref(v_e_1609_);
v_a_1792_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1709_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1709_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1802_; 
lean_dec(v_a_1704_);
lean_dec_ref(v_h_1631_);
lean_dec_ref(v___y_1628_);
lean_dec_ref(v_e_1609_);
v___x_1800_ = lean_box(0);
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 0, v___x_1800_);
v___x_1802_ = v___x_1706_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
lean_dec_ref(v_h_1631_);
lean_dec_ref(v___y_1628_);
lean_dec_ref(v_e_1609_);
v_a_1805_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1703_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1703_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
v___jp_1813_:
{
lean_object* v_self_1828_; uint8_t v_interpreted_1829_; uint8_t v_ctor_1830_; lean_object* v___x_1831_; 
v_self_1828_ = lean_ctor_get(v___y_1826_, 0);
lean_inc_ref_n(v_self_1828_, 2);
v_interpreted_1829_ = lean_ctor_get_uint8(v___y_1826_, sizeof(void*)*12 + 1);
v_ctor_1830_ = lean_ctor_get_uint8(v___y_1826_, sizeof(void*)*12 + 2);
lean_dec_ref(v___y_1826_);
lean_inc_ref(v___y_1821_);
v___x_1831_ = l_Lean_Meta_Grind_hasSameType(v_self_1828_, v___y_1821_, v___y_1816_, v___y_1817_, v___y_1815_, v___y_1818_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1894_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1894_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1894_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
uint8_t v___x_1836_; 
v___x_1836_ = lean_unbox(v_a_1832_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
lean_dec(v_a_1832_);
lean_dec_ref(v_self_1828_);
lean_dec_ref(v___y_1821_);
lean_dec_ref(v___y_1819_);
lean_dec_ref(v_h_1610_);
lean_dec_ref(v_e_1609_);
v___x_1837_ = lean_box(0);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1837_);
v___x_1839_ = v___x_1834_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
else
{
lean_del_object(v___x_1834_);
if (v___y_1827_ == 0)
{
lean_object* v___x_1841_; 
lean_inc(v___y_1818_);
lean_inc_ref(v___y_1815_);
lean_inc(v___y_1817_);
lean_inc_ref(v___y_1816_);
lean_inc(v___y_1820_);
lean_inc_ref(v___y_1825_);
lean_inc(v___y_1824_);
lean_inc_ref(v___y_1823_);
lean_inc(v___y_1814_);
lean_inc(v___y_1822_);
lean_inc_ref(v_self_1828_);
v___x_1841_ = lean_grind_mk_eq_proof(v_self_1828_, v___y_1819_, v___y_1822_, v___y_1814_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1820_, v___y_1816_, v___y_1817_, v___y_1815_, v___y_1818_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1843_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v___x_1843_ = l_Lean_Meta_mkEqTrans(v_a_1842_, v_h_1610_, v___y_1816_, v___y_1817_, v___y_1815_, v___y_1818_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; uint8_t v___x_1845_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref_known(v___x_1843_, 1);
v___x_1845_ = lean_unbox(v_a_1832_);
lean_dec(v_a_1832_);
v___y_1626_ = v___x_1845_;
v___y_1627_ = v_interpreted_1829_;
v___y_1628_ = v___y_1821_;
v___y_1629_ = v_self_1828_;
v___y_1630_ = v_ctor_1830_;
v_h_1631_ = v_a_1844_;
v___y_1632_ = v___y_1822_;
v___y_1633_ = v___y_1814_;
v___y_1634_ = v___y_1823_;
v___y_1635_ = v___y_1824_;
v___y_1636_ = v___y_1825_;
v___y_1637_ = v___y_1820_;
v___y_1638_ = v___y_1816_;
v___y_1639_ = v___y_1817_;
v___y_1640_ = v___y_1815_;
v___y_1641_ = v___y_1818_;
goto v___jp_1625_;
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_dec(v_a_1832_);
lean_dec_ref(v_self_1828_);
lean_dec_ref(v___y_1821_);
lean_dec_ref(v_e_1609_);
v_a_1846_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1843_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1843_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec(v_a_1832_);
lean_dec_ref(v_self_1828_);
lean_dec_ref(v___y_1821_);
lean_dec_ref(v_h_1610_);
lean_dec_ref(v_e_1609_);
v_a_1854_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1841_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1841_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
else
{
lean_object* v___x_1862_; 
lean_inc(v___y_1818_);
lean_inc_ref(v___y_1815_);
lean_inc(v___y_1817_);
lean_inc_ref(v___y_1816_);
lean_inc(v___y_1820_);
lean_inc_ref(v___y_1825_);
lean_inc(v___y_1824_);
lean_inc_ref(v___y_1823_);
lean_inc(v___y_1814_);
lean_inc(v___y_1822_);
lean_inc_ref(v_self_1828_);
v___x_1862_ = lean_grind_mk_heq_proof(v_self_1828_, v___y_1819_, v___y_1822_, v___y_1814_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1820_, v___y_1816_, v___y_1817_, v___y_1815_, v___y_1818_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1864_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1863_);
lean_dec_ref_known(v___x_1862_, 1);
v___x_1864_ = l_Lean_Meta_mkHEqTrans(v_a_1863_, v_h_1610_, v___y_1816_, v___y_1817_, v___y_1815_, v___y_1818_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; uint8_t v___x_1866_; lean_object* v___x_1867_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref_known(v___x_1864_, 1);
v___x_1866_ = 0;
v___x_1867_ = l_Lean_Meta_mkEqOfHEq(v_a_1865_, v___x_1866_, v___y_1816_, v___y_1817_, v___y_1815_, v___y_1818_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; uint8_t v___x_1869_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref_known(v___x_1867_, 1);
v___x_1869_ = lean_unbox(v_a_1832_);
lean_dec(v_a_1832_);
v___y_1626_ = v___x_1869_;
v___y_1627_ = v_interpreted_1829_;
v___y_1628_ = v___y_1821_;
v___y_1629_ = v_self_1828_;
v___y_1630_ = v_ctor_1830_;
v_h_1631_ = v_a_1868_;
v___y_1632_ = v___y_1822_;
v___y_1633_ = v___y_1814_;
v___y_1634_ = v___y_1823_;
v___y_1635_ = v___y_1824_;
v___y_1636_ = v___y_1825_;
v___y_1637_ = v___y_1820_;
v___y_1638_ = v___y_1816_;
v___y_1639_ = v___y_1817_;
v___y_1640_ = v___y_1815_;
v___y_1641_ = v___y_1818_;
goto v___jp_1625_;
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec(v_a_1832_);
lean_dec_ref(v_self_1828_);
lean_dec_ref(v___y_1821_);
lean_dec_ref(v_e_1609_);
v_a_1870_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1867_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1867_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_dec(v_a_1832_);
lean_dec_ref(v_self_1828_);
lean_dec_ref(v___y_1821_);
lean_dec_ref(v_e_1609_);
v_a_1878_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1864_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1864_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec(v_a_1832_);
lean_dec_ref(v_self_1828_);
lean_dec_ref(v___y_1821_);
lean_dec_ref(v_h_1610_);
lean_dec_ref(v_e_1609_);
v_a_1886_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1862_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1862_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_dec_ref(v_self_1828_);
lean_dec_ref(v___y_1821_);
lean_dec_ref(v___y_1819_);
lean_dec_ref(v_h_1610_);
lean_dec_ref(v_e_1609_);
v_a_1895_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1831_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1831_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
v___jp_1903_:
{
lean_object* v___x_1914_; 
lean_inc(v___y_1913_);
lean_inc_ref(v___y_1912_);
lean_inc(v___y_1911_);
lean_inc_ref(v___y_1910_);
lean_inc_ref(v_h_1610_);
v___x_1914_ = lean_infer_type(v_h_1610_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1992_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1917_ = v___x_1914_;
v_isShared_1918_ = v_isSharedCheck_1992_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1914_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1992_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; 
v___x_1919_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_a_1915_);
lean_dec(v_a_1915_);
if (lean_obj_tag(v___x_1919_) == 1)
{
lean_object* v_val_1920_; lean_object* v_snd_1921_; lean_object* v_fst_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1987_; 
lean_del_object(v___x_1917_);
v_val_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_val_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v_snd_1921_ = lean_ctor_get(v_val_1920_, 1);
v_fst_1922_ = lean_ctor_get(v_val_1920_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_val_1920_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1924_ = v_val_1920_;
v_isShared_1925_ = v_isSharedCheck_1987_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_snd_1921_);
lean_inc(v_fst_1922_);
lean_dec(v_val_1920_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1987_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v_fst_1926_; lean_object* v_snd_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1986_; 
v_fst_1926_ = lean_ctor_get(v_snd_1921_, 0);
v_snd_1927_ = lean_ctor_get(v_snd_1921_, 1);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_snd_1921_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1929_ = v_snd_1921_;
v_isShared_1930_ = v_isSharedCheck_1986_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_snd_1927_);
lean_inc(v_fst_1926_);
lean_dec(v_snd_1921_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1986_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_Meta_Sym_shareCommon(v_fst_1926_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1933_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1931_, 1);
v___x_1933_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_a_1932_, v___y_1904_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref_known(v___x_1933_, 1);
if (lean_obj_tag(v_a_1934_) == 1)
{
lean_del_object(v___x_1929_);
lean_del_object(v___x_1924_);
if (lean_obj_tag(v_fst_1922_) == 0)
{
lean_object* v_val_1935_; uint8_t v___x_1936_; 
v_val_1935_ = lean_ctor_get(v_a_1934_, 0);
lean_inc(v_val_1935_);
lean_dec_ref_known(v_a_1934_, 1);
v___x_1936_ = 0;
v___y_1814_ = v___y_1905_;
v___y_1815_ = v___y_1912_;
v___y_1816_ = v___y_1910_;
v___y_1817_ = v___y_1911_;
v___y_1818_ = v___y_1913_;
v___y_1819_ = v_a_1932_;
v___y_1820_ = v___y_1909_;
v___y_1821_ = v_snd_1927_;
v___y_1822_ = v___y_1904_;
v___y_1823_ = v___y_1906_;
v___y_1824_ = v___y_1907_;
v___y_1825_ = v___y_1908_;
v___y_1826_ = v_val_1935_;
v___y_1827_ = v___x_1936_;
goto v___jp_1813_;
}
else
{
lean_object* v_val_1937_; uint8_t v___x_1938_; 
lean_dec_ref_known(v_fst_1922_, 1);
v_val_1937_ = lean_ctor_get(v_a_1934_, 0);
lean_inc(v_val_1937_);
lean_dec_ref_known(v_a_1934_, 1);
v___x_1938_ = 1;
v___y_1814_ = v___y_1905_;
v___y_1815_ = v___y_1912_;
v___y_1816_ = v___y_1910_;
v___y_1817_ = v___y_1911_;
v___y_1818_ = v___y_1913_;
v___y_1819_ = v_a_1932_;
v___y_1820_ = v___y_1909_;
v___y_1821_ = v_snd_1927_;
v___y_1822_ = v___y_1904_;
v___y_1823_ = v___y_1906_;
v___y_1824_ = v___y_1907_;
v___y_1825_ = v___y_1908_;
v___y_1826_ = v_val_1937_;
v___y_1827_ = v___x_1938_;
goto v___jp_1813_;
}
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1942_; 
lean_dec(v_a_1934_);
lean_dec(v_snd_1927_);
lean_dec(v_fst_1922_);
lean_dec_ref(v_h_1610_);
v___x_1939_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1);
v___x_1940_ = l_Lean_indentExpr(v_a_1932_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set_tag(v___x_1929_, 7);
lean_ctor_set(v___x_1929_, 1, v___x_1940_);
lean_ctor_set(v___x_1929_, 0, v___x_1939_);
v___x_1942_ = v___x_1929_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1939_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1943_; lean_object* v___x_1945_; 
v___x_1943_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3);
if (v_isShared_1925_ == 0)
{
lean_ctor_set_tag(v___x_1924_, 7);
lean_ctor_set(v___x_1924_, 1, v___x_1943_);
lean_ctor_set(v___x_1924_, 0, v___x_1942_);
v___x_1945_ = v___x_1924_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1942_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1946_ = l_Lean_indentExpr(v_e_1609_);
v___x_1947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1945_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1908_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; uint8_t v_verbose_1950_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
lean_dec_ref_known(v___x_1948_, 1);
v_verbose_1950_ = lean_ctor_get_uint8(v_a_1949_, 0);
lean_dec(v_a_1949_);
if (v_verbose_1950_ == 0)
{
lean_dec_ref_known(v___x_1947_, 2);
goto v___jp_1622_;
}
else
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_Meta_Sym_reportIssue(v___x_1947_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_dec_ref_known(v___x_1951_, 1);
goto v___jp_1622_;
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1951_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1951_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
lean_dec_ref_known(v___x_1947_, 2);
v_a_1960_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1948_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1948_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec(v_a_1932_);
lean_del_object(v___x_1929_);
lean_dec(v_snd_1927_);
lean_del_object(v___x_1924_);
lean_dec(v_fst_1922_);
lean_dec_ref(v_h_1610_);
lean_dec_ref(v_e_1609_);
v_a_1970_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1933_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1933_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_del_object(v___x_1929_);
lean_dec(v_snd_1927_);
lean_del_object(v___x_1924_);
lean_dec(v_fst_1922_);
lean_dec_ref(v_h_1610_);
lean_dec_ref(v_e_1609_);
v_a_1978_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1931_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1931_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1990_; 
lean_dec(v___x_1919_);
lean_dec_ref(v_h_1610_);
lean_dec_ref(v_e_1609_);
v___x_1988_ = lean_box(0);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 0, v___x_1988_);
v___x_1990_ = v___x_1917_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec_ref(v_h_1610_);
lean_dec_ref(v_e_1609_);
v_a_1993_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1914_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1914_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(lean_object* v_e_2039_, lean_object* v_xs_2040_, lean_object* v___x_2041_, lean_object* v___x_2042_, uint8_t v_a_2043_, lean_object* v_a_2044_, lean_object* v_as_2045_, size_t v_sz_2046_, size_t v_i_2047_, lean_object* v_b_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
uint8_t v___y_2061_; uint8_t v___x_2109_; 
v___x_2109_ = lean_name_eq(v___x_2041_, v___x_2042_);
if (v___x_2109_ == 0)
{
uint8_t v___x_2110_; 
v___x_2110_ = 1;
v___y_2061_ = v___x_2110_;
goto v___jp_2060_;
}
else
{
uint8_t v___x_2111_; 
v___x_2111_ = 0;
v___y_2061_ = v___x_2111_;
goto v___jp_2060_;
}
v___jp_2060_:
{
uint8_t v___x_2062_; 
v___x_2062_ = lean_usize_dec_lt(v_i_2047_, v_sz_2046_);
if (v___x_2062_ == 0)
{
lean_object* v___x_2063_; 
lean_dec_ref(v_a_2044_);
lean_dec_ref(v_e_2039_);
v___x_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2063_, 0, v_b_2048_);
return v___x_2063_;
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v_a_2066_; lean_object* v___x_2067_; 
lean_dec_ref(v_b_2048_);
v___x_2064_ = lean_box(0);
v___x_2065_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_a_2066_ = lean_array_uget_borrowed(v_as_2045_, v_i_2047_);
lean_inc(v_a_2066_);
lean_inc_ref(v_e_2039_);
v___x_2067_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2039_, v_a_2066_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref_known(v___x_2067_, 1);
if (lean_obj_tag(v_a_2068_) == 1)
{
lean_object* v_val_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2097_; 
lean_dec_ref(v_e_2039_);
v_val_2069_ = lean_ctor_get(v_a_2068_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_a_2068_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2071_ = v_a_2068_;
v_isShared_2072_ = v_isSharedCheck_2097_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_val_2069_);
lean_dec(v_a_2068_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2097_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
uint8_t v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = 1;
v___x_2074_ = l_Lean_Meta_mkLambdaFVars(v_xs_2040_, v_val_2069_, v___y_2061_, v_a_2043_, v___y_2061_, v_a_2043_, v___x_2073_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2088_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2077_ = v___x_2074_;
v_isShared_2078_ = v_isSharedCheck_2088_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2088_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2079_ = l_Lean_Expr_app___override(v_a_2044_, v_a_2075_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 0, v___x_2079_);
v___x_2081_ = v___x_2071_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
v___x_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
lean_ctor_set(v___x_2083_, 1, v___x_2064_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2083_);
v___x_2085_ = v___x_2077_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_del_object(v___x_2071_);
lean_dec_ref(v_a_2044_);
v_a_2089_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2074_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2074_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
else
{
size_t v___x_2098_; size_t v___x_2099_; 
lean_dec(v_a_2068_);
v___x_2098_ = ((size_t)1ULL);
v___x_2099_ = lean_usize_add(v_i_2047_, v___x_2098_);
v_i_2047_ = v___x_2099_;
v_b_2048_ = v___x_2065_;
goto _start;
}
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec_ref(v_a_2044_);
lean_dec_ref(v_e_2039_);
v_a_2101_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_2067_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2067_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(lean_object* v_e_2112_, lean_object* v_name_2113_, lean_object* v_name_2114_, uint8_t v_a_2115_, lean_object* v_a_2116_, lean_object* v_xs_2117_, lean_object* v_x_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; size_t v_sz_2132_; size_t v___x_2133_; lean_object* v___x_2134_; 
v___x_2130_ = lean_box(0);
v___x_2131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_sz_2132_ = lean_array_size(v_xs_2117_);
v___x_2133_ = ((size_t)0ULL);
v___x_2134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_2112_, v_xs_2117_, v_name_2113_, v_name_2114_, v_a_2115_, v_a_2116_, v_xs_2117_, v_sz_2132_, v___x_2133_, v___x_2131_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2147_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2137_ = v___x_2134_;
v_isShared_2138_ = v_isSharedCheck_2147_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2134_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2147_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v_fst_2139_; 
v_fst_2139_ = lean_ctor_get(v_a_2135_, 0);
lean_inc(v_fst_2139_);
lean_dec(v_a_2135_);
if (lean_obj_tag(v_fst_2139_) == 0)
{
lean_object* v___x_2141_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2130_);
v___x_2141_ = v___x_2137_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2130_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
else
{
lean_object* v_val_2143_; lean_object* v___x_2145_; 
v_val_2143_ = lean_ctor_get(v_fst_2139_, 0);
lean_inc(v_val_2143_);
lean_dec_ref_known(v_fst_2139_, 1);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v_val_2143_);
v___x_2145_ = v___x_2137_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_val_2143_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
v_a_2148_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2134_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2134_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_e_2156_ = _args[0];
lean_object* v_xs_2157_ = _args[1];
lean_object* v___x_2158_ = _args[2];
lean_object* v___x_2159_ = _args[3];
lean_object* v_a_2160_ = _args[4];
lean_object* v_a_2161_ = _args[5];
lean_object* v_as_2162_ = _args[6];
lean_object* v_sz_2163_ = _args[7];
lean_object* v_i_2164_ = _args[8];
lean_object* v_b_2165_ = _args[9];
lean_object* v___y_2166_ = _args[10];
lean_object* v___y_2167_ = _args[11];
lean_object* v___y_2168_ = _args[12];
lean_object* v___y_2169_ = _args[13];
lean_object* v___y_2170_ = _args[14];
lean_object* v___y_2171_ = _args[15];
lean_object* v___y_2172_ = _args[16];
lean_object* v___y_2173_ = _args[17];
lean_object* v___y_2174_ = _args[18];
lean_object* v___y_2175_ = _args[19];
lean_object* v___y_2176_ = _args[20];
_start:
{
uint8_t v_a_80090__boxed_2177_; size_t v_sz_boxed_2178_; size_t v_i_boxed_2179_; lean_object* v_res_2180_; 
v_a_80090__boxed_2177_ = lean_unbox(v_a_2160_);
v_sz_boxed_2178_ = lean_unbox_usize(v_sz_2163_);
lean_dec(v_sz_2163_);
v_i_boxed_2179_ = lean_unbox_usize(v_i_2164_);
lean_dec(v_i_2164_);
v_res_2180_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_2156_, v_xs_2157_, v___x_2158_, v___x_2159_, v_a_80090__boxed_2177_, v_a_2161_, v_as_2162_, v_sz_boxed_2178_, v_i_boxed_2179_, v_b_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v_as_2162_);
lean_dec(v___x_2159_);
lean_dec(v___x_2158_);
lean_dec_ref(v_xs_2157_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___boxed(lean_object* v_e_2181_, lean_object* v_h_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2181_, v_h_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
lean_dec(v_a_2186_);
lean_dec_ref(v_a_2185_);
lean_dec(v_a_2184_);
lean_dec(v_a_2183_);
return v_res_2194_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__0));
v___x_2197_ = l_Lean_stringToMessageData(v___x_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(lean_object* v_e_2198_, lean_object* v_xs_2199_, uint8_t v___x_2200_, lean_object* v_as_2201_, size_t v_sz_2202_, size_t v_i_2203_, lean_object* v_b_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v_a_2217_; uint8_t v___x_2221_; 
v___x_2221_ = lean_usize_dec_lt(v_i_2203_, v_sz_2202_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2222_; 
lean_dec_ref(v_e_2198_);
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v_b_2204_);
return v___x_2222_;
}
else
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v_a_2226_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___x_2277_; 
lean_dec_ref(v_b_2204_);
v___x_2223_ = lean_box(0);
v___x_2224_ = lean_box(0);
v___x_2225_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_a_2226_ = lean_array_uget_borrowed(v_as_2201_, v_i_2203_);
lean_inc(v___y_2214_);
lean_inc_ref(v___y_2213_);
lean_inc(v___y_2212_);
lean_inc_ref(v___y_2211_);
lean_inc(v_a_2226_);
v___x_2277_ = lean_infer_type(v_a_2226_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2279_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2278_);
lean_dec_ref_known(v___x_2277_, 1);
v___x_2279_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_a_2278_, v___x_2224_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; uint8_t v___x_2281_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v___x_2281_ = lean_unbox(v_a_2280_);
lean_dec(v_a_2280_);
if (v___x_2281_ == 0)
{
lean_dec(v_a_2278_);
v_a_2217_ = v___x_2225_;
goto v___jp_2216_;
}
else
{
lean_object* v_toCold_2282_; lean_object* v_options_2283_; uint8_t v_hasTrace_2284_; 
v_toCold_2282_ = lean_ctor_get(v___y_2213_, 0);
v_options_2283_ = lean_ctor_get(v_toCold_2282_, 2);
v_hasTrace_2284_ = lean_ctor_get_uint8(v_options_2283_, sizeof(void*)*1);
if (v_hasTrace_2284_ == 0)
{
lean_dec(v_a_2278_);
v___y_2228_ = v___y_2205_;
v___y_2229_ = v___y_2206_;
v___y_2230_ = v___y_2207_;
v___y_2231_ = v___y_2208_;
v___y_2232_ = v___y_2209_;
v___y_2233_ = v___y_2210_;
v___y_2234_ = v___y_2211_;
v___y_2235_ = v___y_2212_;
v___y_2236_ = v___y_2213_;
v___y_2237_ = v___y_2214_;
goto v___jp_2227_;
}
else
{
lean_object* v_inheritedTraceOptions_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; uint8_t v___x_2288_; 
v_inheritedTraceOptions_2285_ = lean_ctor_get(v_toCold_2282_, 11);
v___x_2286_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_2287_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_2288_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2285_, v_options_2283_, v___x_2287_);
if (v___x_2288_ == 0)
{
lean_dec(v_a_2278_);
v___y_2228_ = v___y_2205_;
v___y_2229_ = v___y_2206_;
v___y_2230_ = v___y_2207_;
v___y_2231_ = v___y_2208_;
v___y_2232_ = v___y_2209_;
v___y_2233_ = v___y_2210_;
v___y_2234_ = v___y_2211_;
v___y_2235_ = v___y_2212_;
v___y_2236_ = v___y_2213_;
v___y_2237_ = v___y_2214_;
goto v___jp_2227_;
}
else
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_Meta_Grind_updateLastTag(v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
lean_dec_ref_known(v___x_2289_, 1);
v___x_2290_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1);
v___x_2291_ = l_Lean_MessageData_ofExpr(v_a_2278_);
v___x_2292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2290_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_2286_, v___x_2292_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_dec_ref_known(v___x_2293_, 1);
v___y_2228_ = v___y_2205_;
v___y_2229_ = v___y_2206_;
v___y_2230_ = v___y_2207_;
v___y_2231_ = v___y_2208_;
v___y_2232_ = v___y_2209_;
v___y_2233_ = v___y_2210_;
v___y_2234_ = v___y_2211_;
v___y_2235_ = v___y_2212_;
v___y_2236_ = v___y_2213_;
v___y_2237_ = v___y_2214_;
goto v___jp_2227_;
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec_ref(v_e_2198_);
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_dec(v_a_2278_);
lean_dec_ref(v_e_2198_);
v_a_2302_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2289_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2289_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec(v_a_2278_);
lean_dec_ref(v_e_2198_);
v_a_2310_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2279_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2279_);
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
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec_ref(v_e_2198_);
v_a_2318_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2277_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2277_);
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
v___jp_2227_:
{
lean_object* v___x_2238_; 
lean_inc(v_a_2226_);
lean_inc_ref(v_e_2198_);
v___x_2238_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2198_, v_a_2226_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2238_, 1);
if (lean_obj_tag(v_a_2239_) == 1)
{
lean_object* v_val_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2268_; 
lean_dec_ref(v_e_2198_);
v_val_2240_ = lean_ctor_get(v_a_2239_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v_a_2239_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2242_ = v_a_2239_;
v_isShared_2243_ = v_isSharedCheck_2268_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_val_2240_);
lean_dec(v_a_2239_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2268_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
uint8_t v___x_2244_; uint8_t v___x_2245_; lean_object* v___x_2246_; 
v___x_2244_ = 0;
v___x_2245_ = 1;
v___x_2246_ = l_Lean_Meta_mkLambdaFVars(v_xs_2199_, v_val_2240_, v___x_2244_, v___x_2200_, v___x_2244_, v___x_2200_, v___x_2245_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2259_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2249_ = v___x_2246_;
v_isShared_2250_ = v_isSharedCheck_2259_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2246_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2259_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 0, v_a_2247_);
v___x_2252_ = v___x_2242_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
v___x_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
lean_ctor_set(v___x_2254_, 1, v___x_2223_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 0, v___x_2254_);
v___x_2256_ = v___x_2249_;
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
lean_del_object(v___x_2242_);
v_a_2260_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2246_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2246_);
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
else
{
lean_dec(v_a_2239_);
v_a_2217_ = v___x_2225_;
goto v___jp_2216_;
}
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_dec_ref(v_e_2198_);
v_a_2269_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2238_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2238_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
}
v___jp_2216_:
{
size_t v___x_2218_; size_t v___x_2219_; 
v___x_2218_ = ((size_t)1ULL);
v___x_2219_ = lean_usize_add(v_i_2203_, v___x_2218_);
lean_inc_ref(v_a_2217_);
v_i_2203_ = v___x_2219_;
v_b_2204_ = v_a_2217_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_e_2326_ = _args[0];
lean_object* v_xs_2327_ = _args[1];
lean_object* v___x_2328_ = _args[2];
lean_object* v_as_2329_ = _args[3];
lean_object* v_sz_2330_ = _args[4];
lean_object* v_i_2331_ = _args[5];
lean_object* v_b_2332_ = _args[6];
lean_object* v___y_2333_ = _args[7];
lean_object* v___y_2334_ = _args[8];
lean_object* v___y_2335_ = _args[9];
lean_object* v___y_2336_ = _args[10];
lean_object* v___y_2337_ = _args[11];
lean_object* v___y_2338_ = _args[12];
lean_object* v___y_2339_ = _args[13];
lean_object* v___y_2340_ = _args[14];
lean_object* v___y_2341_ = _args[15];
lean_object* v___y_2342_ = _args[16];
lean_object* v___y_2343_ = _args[17];
_start:
{
uint8_t v___x_21114__boxed_2344_; size_t v_sz_boxed_2345_; size_t v_i_boxed_2346_; lean_object* v_res_2347_; 
v___x_21114__boxed_2344_ = lean_unbox(v___x_2328_);
v_sz_boxed_2345_ = lean_unbox_usize(v_sz_2330_);
lean_dec(v_sz_2330_);
v_i_boxed_2346_ = lean_unbox_usize(v_i_2331_);
lean_dec(v_i_2331_);
v_res_2347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2326_, v_xs_2327_, v___x_21114__boxed_2344_, v_as_2329_, v_sz_boxed_2345_, v_i_boxed_2346_, v_b_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v_as_2329_);
lean_dec_ref(v_xs_2327_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(lean_object* v_e_2348_, uint8_t v___x_2349_, lean_object* v_xs_2350_, lean_object* v_x_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; size_t v_sz_2365_; size_t v___x_2366_; lean_object* v___x_2367_; 
v___x_2363_ = lean_box(0);
v___x_2364_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_sz_2365_ = lean_array_size(v_xs_2350_);
v___x_2366_ = ((size_t)0ULL);
v___x_2367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2348_, v_xs_2350_, v___x_2349_, v_xs_2350_, v_sz_2365_, v___x_2366_, v___x_2364_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2380_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2370_ = v___x_2367_;
v_isShared_2371_ = v_isSharedCheck_2380_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2367_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2380_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v_fst_2372_; 
v_fst_2372_ = lean_ctor_get(v_a_2368_, 0);
lean_inc(v_fst_2372_);
lean_dec(v_a_2368_);
if (lean_obj_tag(v_fst_2372_) == 0)
{
lean_object* v___x_2374_; 
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 0, v___x_2363_);
v___x_2374_ = v___x_2370_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2363_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
else
{
lean_object* v_val_2376_; lean_object* v___x_2378_; 
v_val_2376_ = lean_ctor_get(v_fst_2372_, 0);
lean_inc(v_val_2376_);
lean_dec_ref_known(v_fst_2372_, 1);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 0, v_val_2376_);
v___x_2378_ = v___x_2370_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_val_2376_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
v_a_2381_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2367_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2367_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed(lean_object* v_e_2389_, lean_object* v___x_2390_, lean_object* v_xs_2391_, lean_object* v_x_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
uint8_t v___x_21368__boxed_2404_; lean_object* v_res_2405_; 
v___x_21368__boxed_2404_ = lean_unbox(v___x_2390_);
v_res_2405_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(v_e_2389_, v___x_21368__boxed_2404_, v_xs_2391_, v_x_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v_x_2392_);
lean_dec_ref(v_xs_2391_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(lean_object* v_e_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v___x_2421_; 
lean_inc_ref(v_e_2406_);
v___x_2421_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2406_, v_a_2414_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2422_);
lean_dec_ref_known(v___x_2421_, 1);
v___x_2423_ = l_Lean_Expr_cleanupAnnotations(v_a_2422_);
lean_dec(v_a_2422_);
v___x_2424_ = l_Lean_Expr_isApp(v___x_2423_);
if (v___x_2424_ == 0)
{
lean_dec_ref(v___x_2423_);
lean_dec_ref(v_e_2406_);
goto v___jp_2418_;
}
else
{
lean_object* v___x_2425_; lean_object* v___x_2426_; uint8_t v___x_2427_; 
v___x_2425_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2423_);
v___x_2426_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_2427_ = l_Lean_Expr_isConstOf(v___x_2425_, v___x_2426_);
lean_dec_ref(v___x_2425_);
if (v___x_2427_ == 0)
{
lean_dec_ref(v___x_2423_);
lean_dec_ref(v_e_2406_);
goto v___jp_2418_;
}
else
{
lean_object* v_arg_2428_; lean_object* v___x_2429_; lean_object* v___f_2430_; uint8_t v___x_2431_; lean_object* v___x_2432_; 
v_arg_2428_ = lean_ctor_get(v___x_2423_, 1);
lean_inc_ref(v_arg_2428_);
lean_dec_ref(v___x_2423_);
v___x_2429_ = lean_box(v___x_2427_);
v___f_2430_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed), 15, 2);
lean_closure_set(v___f_2430_, 0, v_e_2406_);
lean_closure_set(v___f_2430_, 1, v___x_2429_);
v___x_2431_ = 0;
v___x_2432_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_arg_2428_, v___f_2430_, v___x_2431_, v___x_2431_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
return v___x_2432_;
}
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec_ref(v_e_2406_);
v_a_2433_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2421_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2421_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
v___jp_2418_:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = lean_box(0);
v___x_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
return v___x_2420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___boxed(lean_object* v_e_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
lean_dec(v_a_2449_);
lean_dec_ref(v_a_2448_);
lean_dec(v_a_2447_);
lean_dec_ref(v_a_2446_);
lean_dec(v_a_2445_);
lean_dec_ref(v_a_2444_);
lean_dec(v_a_2443_);
lean_dec(v_a_2442_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(lean_object* v_e_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v___x_2460_; uint8_t v___x_2461_; uint8_t v___x_2462_; 
v___x_2460_ = l_Lean_Expr_getAppFn(v_e_2454_);
v___x_2461_ = l_Lean_Expr_isMVar(v___x_2460_);
lean_dec_ref(v___x_2460_);
v___x_2462_ = 1;
if (v___x_2461_ == 0)
{
lean_object* v___x_2463_; 
lean_inc_ref(v_e_2454_);
v___x_2463_ = l_Lean_Meta_isConstructorApp_x3f(v_e_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2473_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2466_ = v___x_2463_;
v_isShared_2467_ = v_isSharedCheck_2473_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2463_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2473_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
if (lean_obj_tag(v_a_2464_) == 0)
{
lean_object* v___x_2468_; 
lean_del_object(v___x_2466_);
v___x_2468_ = l_Lean_Meta_isLitValue(v_e_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_);
return v___x_2468_;
}
else
{
lean_object* v___x_2469_; lean_object* v___x_2471_; 
lean_dec_ref_known(v_a_2464_, 1);
lean_dec_ref(v_e_2454_);
v___x_2469_ = lean_box(v___x_2462_);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 0, v___x_2469_);
v___x_2471_ = v___x_2466_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2469_);
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
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec_ref(v_e_2454_);
v_a_2474_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2463_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2463_);
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
else
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
lean_dec_ref(v_e_2454_);
v___x_2482_ = lean_box(v___x_2462_);
v___x_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
return v___x_2483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg___boxed(lean_object* v_e_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(v_e_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
lean_dec(v_a_2488_);
lean_dec_ref(v_a_2487_);
lean_dec(v_a_2486_);
lean_dec_ref(v_a_2485_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike(lean_object* v_e_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_){
_start:
{
lean_object* v___x_2503_; 
v___x_2503_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(v_e_2491_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___boxed(lean_object* v_e_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike(v_e_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_);
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
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(lean_object* v_e_2517_, lean_object* v_pat_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v___x_2530_; uint8_t v_modified_2531_; 
v___x_2530_ = l_Lean_Expr_getAppFn(v_pat_2518_);
v_modified_2531_ = l_Lean_Expr_isMVar(v___x_2530_);
lean_dec_ref(v___x_2530_);
if (v_modified_2531_ == 0)
{
lean_object* v___x_2532_; 
lean_inc_ref(v_e_2517_);
v___x_2532_ = l_Lean_Meta_Grind_getRootENode___redArg(v_e_2517_, v_a_2519_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2633_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2535_ = v___x_2532_;
v_isShared_2536_ = v_isSharedCheck_2633_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2532_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2633_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
uint8_t v_ctor_2537_; 
v_ctor_2537_ = lean_ctor_get_uint8(v_a_2533_, sizeof(void*)*12 + 2);
if (v_ctor_2537_ == 0)
{
uint8_t v_interpreted_2538_; 
lean_dec_ref(v_pat_2518_);
v_interpreted_2538_ = lean_ctor_get_uint8(v_a_2533_, sizeof(void*)*12 + 1);
if (v_interpreted_2538_ == 0)
{
lean_object* v___x_2540_; 
lean_dec(v_a_2533_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 0, v_e_2517_);
v___x_2540_ = v___x_2535_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_e_2517_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
else
{
lean_object* v_self_2542_; lean_object* v___x_2544_; 
lean_dec_ref(v_e_2517_);
v_self_2542_ = lean_ctor_get(v_a_2533_, 0);
lean_inc_ref(v_self_2542_);
lean_dec(v_a_2533_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 0, v_self_2542_);
v___x_2544_ = v___x_2535_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_self_2542_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
else
{
lean_object* v_self_2546_; lean_object* v___x_2547_; 
lean_del_object(v___x_2535_);
lean_dec_ref(v_e_2517_);
v_self_2546_ = lean_ctor_get(v_a_2533_, 0);
lean_inc_ref_n(v_self_2546_, 2);
lean_dec(v_a_2533_);
v___x_2547_ = l_Lean_Meta_isConstructorApp_x3f(v_self_2546_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2624_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2550_ = v___x_2547_;
v_isShared_2551_ = v_isSharedCheck_2624_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2547_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2624_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
if (lean_obj_tag(v_a_2548_) == 1)
{
lean_object* v_val_2552_; lean_object* v___x_2553_; 
lean_del_object(v___x_2550_);
v_val_2552_ = lean_ctor_get(v_a_2548_, 0);
lean_inc(v_val_2552_);
lean_dec_ref_known(v_a_2548_, 1);
lean_inc_ref(v_pat_2518_);
v___x_2553_ = l_Lean_Meta_isConstructorApp_x3f(v_pat_2518_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2612_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2556_ = v___x_2553_;
v_isShared_2557_ = v_isSharedCheck_2612_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2553_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2612_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
if (lean_obj_tag(v_a_2554_) == 1)
{
lean_object* v_toConstantVal_2558_; lean_object* v_val_2559_; lean_object* v_toConstantVal_2560_; lean_object* v_numParams_2561_; lean_object* v_numFields_2562_; lean_object* v_name_2563_; lean_object* v_name_2564_; uint8_t v___x_2565_; 
v_toConstantVal_2558_ = lean_ctor_get(v_val_2552_, 0);
lean_inc_ref(v_toConstantVal_2558_);
v_val_2559_ = lean_ctor_get(v_a_2554_, 0);
lean_inc(v_val_2559_);
lean_dec_ref_known(v_a_2554_, 1);
v_toConstantVal_2560_ = lean_ctor_get(v_val_2559_, 0);
lean_inc_ref(v_toConstantVal_2560_);
lean_dec(v_val_2559_);
v_numParams_2561_ = lean_ctor_get(v_val_2552_, 3);
lean_inc(v_numParams_2561_);
v_numFields_2562_ = lean_ctor_get(v_val_2552_, 4);
lean_inc(v_numFields_2562_);
lean_dec(v_val_2552_);
v_name_2563_ = lean_ctor_get(v_toConstantVal_2558_, 0);
lean_inc(v_name_2563_);
lean_dec_ref(v_toConstantVal_2558_);
v_name_2564_ = lean_ctor_get(v_toConstantVal_2560_, 0);
lean_inc(v_name_2564_);
lean_dec_ref(v_toConstantVal_2560_);
v___x_2565_ = lean_name_eq(v_name_2563_, v_name_2564_);
lean_dec(v_name_2564_);
lean_dec(v_name_2563_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2567_; 
lean_dec(v_numFields_2562_);
lean_dec(v_numParams_2561_);
lean_dec_ref(v_pat_2518_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v_self_2546_);
v___x_2567_ = v___x_2556_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_self_2546_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v___x_2569_ = lean_nat_add(v_numParams_2561_, v_numFields_2562_);
lean_dec(v_numFields_2562_);
v___x_2570_ = l_Lean_Expr_getAppNumArgs(v_pat_2518_);
v___x_2571_ = lean_nat_dec_eq(v___x_2570_, v___x_2569_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2573_; 
lean_dec(v___x_2570_);
lean_dec(v___x_2569_);
lean_dec(v_numParams_2561_);
lean_dec_ref(v_pat_2518_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v_self_2546_);
v___x_2573_ = v___x_2556_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_self_2546_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
else
{
lean_object* v_nargs_2575_; lean_object* v_dummy_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
lean_del_object(v___x_2556_);
v_nargs_2575_ = l_Lean_Expr_getAppNumArgs(v_self_2546_);
v_dummy_2576_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0);
lean_inc(v_nargs_2575_);
v___x_2577_ = lean_mk_array(v_nargs_2575_, v_dummy_2576_);
v___x_2578_ = lean_unsigned_to_nat(1u);
v___x_2579_ = lean_nat_sub(v_nargs_2575_, v___x_2578_);
lean_dec(v_nargs_2575_);
lean_inc_ref(v_self_2546_);
v___x_2580_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_2546_, v___x_2577_, v___x_2579_);
v___x_2581_ = lean_box(v_modified_2531_);
v___x_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2580_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
lean_inc(v___x_2570_);
v___x_2583_ = lean_mk_array(v___x_2570_, v_dummy_2576_);
v___x_2584_ = lean_nat_sub(v___x_2570_, v___x_2578_);
lean_dec(v___x_2570_);
v___x_2585_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_pat_2518_, v___x_2583_, v___x_2584_);
v___x_2586_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v___x_2569_, v___x_2585_, v_numParams_2561_, v___x_2582_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
lean_dec_ref(v___x_2585_);
lean_dec(v___x_2569_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2600_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2600_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2600_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v_snd_2591_; uint8_t v___x_2592_; 
v_snd_2591_ = lean_ctor_get(v_a_2587_, 1);
v___x_2592_ = lean_unbox(v_snd_2591_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2594_; 
lean_dec(v_a_2587_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v_self_2546_);
v___x_2594_ = v___x_2589_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_self_2546_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
else
{
lean_object* v_fst_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
lean_del_object(v___x_2589_);
v_fst_2596_ = lean_ctor_get(v_a_2587_, 0);
lean_inc(v_fst_2596_);
lean_dec(v_a_2587_);
v___x_2597_ = l_Lean_Expr_getAppFn(v_self_2546_);
lean_dec_ref(v_self_2546_);
v___x_2598_ = l_Lean_mkAppN(v___x_2597_, v_fst_2596_);
lean_dec(v_fst_2596_);
v___x_2599_ = l_Lean_Meta_Sym_shareCommon(v___x_2598_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
return v___x_2599_;
}
}
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
lean_dec_ref(v_self_2546_);
v_a_2601_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2586_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2586_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
}
}
else
{
lean_object* v___x_2610_; 
lean_dec(v_a_2554_);
lean_dec(v_val_2552_);
lean_dec_ref(v_pat_2518_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v_self_2546_);
v___x_2610_ = v___x_2556_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_self_2546_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec(v_val_2552_);
lean_dec_ref(v_self_2546_);
lean_dec_ref(v_pat_2518_);
v_a_2613_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2553_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2553_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_object* v___x_2622_; 
lean_dec(v_a_2548_);
lean_dec_ref(v_pat_2518_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 0, v_self_2546_);
v___x_2622_ = v___x_2550_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_self_2546_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref(v_self_2546_);
lean_dec_ref(v_pat_2518_);
v_a_2625_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2547_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2547_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
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
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_dec_ref(v_pat_2518_);
lean_dec_ref(v_e_2517_);
v_a_2634_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2532_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2532_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
else
{
lean_object* v___x_2642_; 
lean_dec_ref(v_pat_2518_);
v___x_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2642_, 0, v_e_2517_);
return v___x_2642_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(lean_object* v_upperBound_2643_, lean_object* v___x_2644_, lean_object* v_a_2645_, lean_object* v_b_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v_a_2659_; uint8_t v_modified_2663_; 
v_modified_2663_ = lean_nat_dec_lt(v_a_2645_, v_upperBound_2643_);
if (v_modified_2663_ == 0)
{
lean_object* v___x_2664_; 
lean_dec(v_a_2645_);
v___x_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2664_, 0, v_b_2646_);
return v___x_2664_;
}
else
{
lean_object* v_fst_2665_; lean_object* v_snd_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2694_; 
v_fst_2665_ = lean_ctor_get(v_b_2646_, 0);
v_snd_2666_ = lean_ctor_get(v_b_2646_, 1);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_b_2646_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2668_ = v_b_2646_;
v_isShared_2669_ = v_isSharedCheck_2694_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_snd_2666_);
lean_inc(v_fst_2665_);
lean_dec(v_b_2646_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2694_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2670_ = l_Lean_instInhabitedExpr;
v___x_2671_ = lean_array_get_borrowed(v___x_2670_, v_fst_2665_, v_a_2645_);
v___x_2672_ = lean_array_get_borrowed(v___x_2670_, v___x_2644_, v_a_2645_);
lean_inc(v___x_2672_);
lean_inc(v___x_2671_);
v___x_2673_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v___x_2671_, v___x_2672_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; size_t v___x_2675_; size_t v___x_2676_; uint8_t v___x_2677_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2673_, 1);
v___x_2675_ = lean_ptr_addr(v___x_2671_);
v___x_2676_ = lean_ptr_addr(v_a_2674_);
v___x_2677_ = lean_usize_dec_eq(v___x_2675_, v___x_2676_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2681_; 
lean_dec(v_snd_2666_);
v___x_2678_ = lean_array_set(v_fst_2665_, v_a_2645_, v_a_2674_);
v___x_2679_ = lean_box(v_modified_2663_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 1, v___x_2679_);
lean_ctor_set(v___x_2668_, 0, v___x_2678_);
v___x_2681_ = v___x_2668_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2678_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
v_a_2659_ = v___x_2681_;
goto v___jp_2658_;
}
}
else
{
lean_object* v___x_2684_; 
lean_dec(v_a_2674_);
if (v_isShared_2669_ == 0)
{
v___x_2684_ = v___x_2668_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_fst_2665_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_snd_2666_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
v_a_2659_ = v___x_2684_;
goto v___jp_2658_;
}
}
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_del_object(v___x_2668_);
lean_dec(v_snd_2666_);
lean_dec(v_fst_2665_);
lean_dec(v_a_2645_);
v_a_2686_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2673_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2673_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
}
v___jp_2658_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = lean_unsigned_to_nat(1u);
v___x_2661_ = lean_nat_add(v_a_2645_, v___x_2660_);
lean_dec(v_a_2645_);
v_a_2645_ = v___x_2661_;
v_b_2646_ = v_a_2659_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg___boxed(lean_object* v_upperBound_2695_, lean_object* v___x_2696_, lean_object* v_a_2697_, lean_object* v_b_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2695_, v___x_2696_, v_a_2697_, v_b_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___x_2696_);
lean_dec(v_upperBound_2695_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go___boxed(lean_object* v_e_2711_, lean_object* v_pat_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_e_2711_, v_pat_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_);
lean_dec(v_a_2722_);
lean_dec_ref(v_a_2721_);
lean_dec(v_a_2720_);
lean_dec_ref(v_a_2719_);
lean_dec(v_a_2718_);
lean_dec_ref(v_a_2717_);
lean_dec(v_a_2716_);
lean_dec_ref(v_a_2715_);
lean_dec(v_a_2714_);
lean_dec(v_a_2713_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(lean_object* v_upperBound_2725_, lean_object* v___x_2726_, lean_object* v_inst_2727_, lean_object* v_R_2728_, lean_object* v_a_2729_, lean_object* v_b_2730_, lean_object* v_c_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2725_, v___x_2726_, v_a_2729_, v_b_2730_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_2744_ = _args[0];
lean_object* v___x_2745_ = _args[1];
lean_object* v_inst_2746_ = _args[2];
lean_object* v_R_2747_ = _args[3];
lean_object* v_a_2748_ = _args[4];
lean_object* v_b_2749_ = _args[5];
lean_object* v_c_2750_ = _args[6];
lean_object* v___y_2751_ = _args[7];
lean_object* v___y_2752_ = _args[8];
lean_object* v___y_2753_ = _args[9];
lean_object* v___y_2754_ = _args[10];
lean_object* v___y_2755_ = _args[11];
lean_object* v___y_2756_ = _args[12];
lean_object* v___y_2757_ = _args[13];
lean_object* v___y_2758_ = _args[14];
lean_object* v___y_2759_ = _args[15];
lean_object* v___y_2760_ = _args[16];
lean_object* v___y_2761_ = _args[17];
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(v_upperBound_2744_, v___x_2745_, v_inst_2746_, v_R_2747_, v_a_2748_, v_b_2749_, v_c_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___x_2745_);
lean_dec(v_upperBound_2744_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(lean_object* v_e_2763_, lean_object* v___y_2764_){
_start:
{
uint8_t v___x_2766_; 
v___x_2766_ = l_Lean_Expr_hasMVar(v_e_2763_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; 
v___x_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2767_, 0, v_e_2763_);
return v___x_2767_;
}
else
{
lean_object* v___x_2768_; lean_object* v_mctx_2769_; lean_object* v___x_2770_; lean_object* v_fst_2771_; lean_object* v_snd_2772_; lean_object* v___x_2773_; lean_object* v_cache_2774_; lean_object* v_zetaDeltaFVarIds_2775_; lean_object* v_postponed_2776_; lean_object* v_diag_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2786_; 
v___x_2768_ = lean_st_ref_get(v___y_2764_);
v_mctx_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc_ref(v_mctx_2769_);
lean_dec(v___x_2768_);
v___x_2770_ = l_Lean_instantiateMVarsCore(v_mctx_2769_, v_e_2763_);
v_fst_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_fst_2771_);
v_snd_2772_ = lean_ctor_get(v___x_2770_, 1);
lean_inc(v_snd_2772_);
lean_dec_ref(v___x_2770_);
v___x_2773_ = lean_st_ref_take(v___y_2764_);
v_cache_2774_ = lean_ctor_get(v___x_2773_, 1);
v_zetaDeltaFVarIds_2775_ = lean_ctor_get(v___x_2773_, 2);
v_postponed_2776_ = lean_ctor_get(v___x_2773_, 3);
v_diag_2777_ = lean_ctor_get(v___x_2773_, 4);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2786_ == 0)
{
lean_object* v_unused_2787_; 
v_unused_2787_ = lean_ctor_get(v___x_2773_, 0);
lean_dec(v_unused_2787_);
v___x_2779_ = v___x_2773_;
v_isShared_2780_ = v_isSharedCheck_2786_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_diag_2777_);
lean_inc(v_postponed_2776_);
lean_inc(v_zetaDeltaFVarIds_2775_);
lean_inc(v_cache_2774_);
lean_dec(v___x_2773_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2786_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v_snd_2772_);
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_snd_2772_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v_cache_2774_);
lean_ctor_set(v_reuseFailAlloc_2785_, 2, v_zetaDeltaFVarIds_2775_);
lean_ctor_set(v_reuseFailAlloc_2785_, 3, v_postponed_2776_);
lean_ctor_set(v_reuseFailAlloc_2785_, 4, v_diag_2777_);
v___x_2782_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = lean_st_ref_put(v___y_2764_, v___x_2782_);
v___x_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2784_, 0, v_fst_2771_);
return v___x_2784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg___boxed(lean_object* v_e_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v_e_2788_, v___y_2789_);
lean_dec(v___y_2789_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(lean_object* v_e_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v___x_2804_; 
v___x_2804_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v_e_2792_, v___y_2800_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___boxed(lean_object* v_e_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(v_e_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec(v___y_2806_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0(lean_object* v_k_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v___x_2830_; 
lean_inc(v___y_2824_);
lean_inc_ref(v___y_2823_);
lean_inc(v___y_2822_);
lean_inc_ref(v___y_2821_);
lean_inc(v___y_2820_);
lean_inc(v___y_2819_);
v___x_2830_ = lean_apply_11(v_k_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, lean_box(0));
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0___boxed(lean_object* v_k_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0(v_k_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec(v___y_2832_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(lean_object* v_k_2844_, uint8_t v_allowLevelAssignments_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v___f_2857_; lean_object* v___x_2858_; 
lean_inc(v___y_2851_);
lean_inc_ref(v___y_2850_);
lean_inc(v___y_2849_);
lean_inc_ref(v___y_2848_);
lean_inc(v___y_2847_);
lean_inc(v___y_2846_);
v___f_2857_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_2857_, 0, v_k_2844_);
lean_closure_set(v___f_2857_, 1, v___y_2846_);
lean_closure_set(v___f_2857_, 2, v___y_2847_);
lean_closure_set(v___f_2857_, 3, v___y_2848_);
lean_closure_set(v___f_2857_, 4, v___y_2849_);
lean_closure_set(v___f_2857_, 5, v___y_2850_);
lean_closure_set(v___f_2857_, 6, v___y_2851_);
v___x_2858_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2845_, v___f_2857_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
if (lean_obj_tag(v___x_2858_) == 0)
{
return v___x_2858_;
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v___x_2858_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2858_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2859_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___boxed(lean_object* v_k_2867_, lean_object* v_allowLevelAssignments_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2880_; lean_object* v_res_2881_; 
v_allowLevelAssignments_boxed_2880_ = lean_unbox(v_allowLevelAssignments_2868_);
v_res_2881_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(v_k_2867_, v_allowLevelAssignments_boxed_2880_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec(v___y_2869_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(lean_object* v_00_u03b1_2882_, lean_object* v_k_2883_, uint8_t v_allowLevelAssignments_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v___x_2896_; 
v___x_2896_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(v_k_2883_, v_allowLevelAssignments_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___boxed(lean_object* v_00_u03b1_2897_, lean_object* v_k_2898_, lean_object* v_allowLevelAssignments_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2911_; lean_object* v_res_2912_; 
v_allowLevelAssignments_boxed_2911_ = lean_unbox(v_allowLevelAssignments_2899_);
v_res_2912_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_00_u03b1_2897_, v_k_2898_, v_allowLevelAssignments_boxed_2911_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
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
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0(lean_object* v_cls_2913_, lean_object* v_____do__lift_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v_toCold_2926_; lean_object* v_options_2927_; uint8_t v_hasTrace_2928_; 
v_toCold_2926_ = lean_ctor_get(v___y_2923_, 0);
v_options_2927_ = lean_ctor_get(v_toCold_2926_, 2);
v_hasTrace_2928_ = lean_ctor_get_uint8(v_options_2927_, sizeof(void*)*1);
if (v_hasTrace_2928_ == 0)
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
lean_dec(v_cls_2913_);
v___x_2929_ = lean_box(v_hasTrace_2928_);
v___x_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
return v___x_2930_;
}
else
{
lean_object* v___x_2931_; lean_object* v___x_2932_; uint8_t v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2931_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5));
v___x_2932_ = l_Lean_Name_append(v___x_2931_, v_cls_2913_);
v___x_2933_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2914_, v_options_2927_, v___x_2932_);
lean_dec(v___x_2932_);
v___x_2934_ = lean_box(v___x_2933_);
v___x_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
return v___x_2935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed(lean_object* v_cls_2936_, lean_object* v_____do__lift_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Lean_Meta_Grind_tryToProveFalse___lam__0(v_cls_2936_, v_____do__lift_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v_____do__lift_2937_);
return v_res_2949_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3(void){
_start:
{
lean_object* v_cls_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v_cls_2958_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1));
v___x_2959_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5));
v___x_2960_ = l_Lean_Name_append(v___x_2959_, v_cls_2958_);
return v___x_2960_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5(void){
_start:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__4));
v___x_2963_ = l_Lean_stringToMessageData(v___x_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(lean_object* v_as_2964_, size_t v_sz_2965_, size_t v_i_2966_, lean_object* v_b_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v_a_2980_; uint8_t v___x_2984_; 
v___x_2984_ = lean_usize_dec_lt(v_i_2966_, v_sz_2965_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; 
v___x_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2985_, 0, v_b_2967_);
return v___x_2985_;
}
else
{
lean_object* v_snd_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3241_; 
v_snd_2986_ = lean_ctor_get(v_b_2967_, 1);
v_isSharedCheck_3241_ = !lean_is_exclusive(v_b_2967_);
if (v_isSharedCheck_3241_ == 0)
{
lean_object* v_unused_3242_; 
v_unused_3242_ = lean_ctor_get(v_b_2967_, 0);
lean_dec(v_unused_3242_);
v___x_2988_ = v_b_2967_;
v_isShared_2989_ = v_isSharedCheck_3241_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_snd_2986_);
lean_dec(v_b_2967_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3241_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v_array_2990_; lean_object* v_start_2991_; lean_object* v_stop_2992_; lean_object* v___x_2993_; uint8_t v___x_2994_; 
v_array_2990_ = lean_ctor_get(v_snd_2986_, 0);
v_start_2991_ = lean_ctor_get(v_snd_2986_, 1);
v_stop_2992_ = lean_ctor_get(v_snd_2986_, 2);
v___x_2993_ = lean_box(0);
v___x_2994_ = lean_nat_dec_lt(v_start_2991_, v_stop_2992_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2996_; 
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 0, v___x_2993_);
v___x_2996_ = v___x_2988_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2993_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v_snd_2986_);
v___x_2996_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
lean_object* v___x_2997_; 
v___x_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
return v___x_2997_;
}
}
else
{
lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3237_; 
lean_inc(v_stop_2992_);
lean_inc(v_start_2991_);
lean_inc_ref(v_array_2990_);
v_isSharedCheck_3237_ = !lean_is_exclusive(v_snd_2986_);
if (v_isSharedCheck_3237_ == 0)
{
lean_object* v_unused_3238_; lean_object* v_unused_3239_; lean_object* v_unused_3240_; 
v_unused_3238_ = lean_ctor_get(v_snd_2986_, 2);
lean_dec(v_unused_3238_);
v_unused_3239_ = lean_ctor_get(v_snd_2986_, 1);
lean_dec(v_unused_3239_);
v_unused_3240_ = lean_ctor_get(v_snd_2986_, 0);
lean_dec(v_unused_3240_);
v___x_3000_ = v_snd_2986_;
v_isShared_3001_ = v_isSharedCheck_3237_;
goto v_resetjp_2999_;
}
else
{
lean_dec(v_snd_2986_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3237_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3006_; 
v___x_3002_ = lean_array_fget(v_array_2990_, v_start_2991_);
v___x_3003_ = lean_unsigned_to_nat(1u);
v___x_3004_ = lean_nat_add(v_start_2991_, v___x_3003_);
lean_dec(v_start_2991_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 1, v___x_3004_);
v___x_3006_ = v___x_3000_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_array_2990_);
lean_ctor_set(v_reuseFailAlloc_3236_, 1, v___x_3004_);
lean_ctor_set(v_reuseFailAlloc_3236_, 2, v_stop_2992_);
v___x_3006_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
uint8_t v___x_3007_; 
v___x_3007_ = lean_unbox(v___x_3002_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3009_; 
lean_dec(v___x_3002_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 1, v___x_3006_);
lean_ctor_set(v___x_2988_, 0, v___x_2993_);
v___x_3009_ = v___x_2988_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_2993_);
lean_ctor_set(v_reuseFailAlloc_3010_, 1, v___x_3006_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
v_a_2980_ = v___x_3009_;
goto v___jp_2979_;
}
}
else
{
lean_object* v_cls_3011_; lean_object* v_a_3012_; lean_object* v_____x_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___x_3050_; 
v_cls_3011_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1));
v_a_3012_ = lean_array_uget_borrowed(v_as_2964_, v_i_2966_);
lean_inc(v___y_2977_);
lean_inc_ref(v___y_2976_);
lean_inc(v___y_2975_);
lean_inc_ref(v___y_2974_);
lean_inc(v_a_3012_);
v___x_3050_ = lean_infer_type(v_a_3012_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3227_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3053_ = v___x_3050_;
v_isShared_3054_ = v_isSharedCheck_3227_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3050_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3227_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3055_; 
v___x_3055_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_a_3051_);
lean_dec(v_a_3051_);
if (lean_obj_tag(v___x_3055_) == 1)
{
lean_object* v_val_3056_; lean_object* v_snd_3057_; lean_object* v_fst_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3221_; 
lean_del_object(v___x_3053_);
v_val_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_val_3056_);
lean_dec_ref_known(v___x_3055_, 1);
v_snd_3057_ = lean_ctor_get(v_val_3056_, 1);
v_fst_3058_ = lean_ctor_get(v_val_3056_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v_val_3056_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3060_ = v_val_3056_;
v_isShared_3061_ = v_isSharedCheck_3221_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_snd_3057_);
lean_inc(v_fst_3058_);
lean_dec(v_val_3056_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3221_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v_fst_3062_; lean_object* v_snd_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3220_; 
v_fst_3062_ = lean_ctor_get(v_snd_3057_, 0);
v_snd_3063_ = lean_ctor_get(v_snd_3057_, 1);
v_isSharedCheck_3220_ = !lean_is_exclusive(v_snd_3057_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3065_ = v_snd_3057_;
v_isShared_3066_ = v_isSharedCheck_3220_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_snd_3063_);
lean_inc(v_fst_3062_);
lean_dec(v_snd_3057_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3220_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
uint8_t v___y_3068_; lean_object* v_lhs_x27_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3101_; uint8_t v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3159_; uint8_t v___y_3160_; uint8_t v___y_3195_; 
if (lean_obj_tag(v_fst_3058_) == 0)
{
uint8_t v___x_3218_; 
lean_dec(v___x_3002_);
v___x_3218_ = 0;
v___y_3195_ = v___x_3218_;
goto v___jp_3194_;
}
else
{
uint8_t v___x_3219_; 
lean_dec_ref_known(v_fst_3058_, 1);
v___x_3219_ = lean_unbox(v___x_3002_);
lean_dec(v___x_3002_);
v___y_3195_ = v___x_3219_;
goto v___jp_3194_;
}
v___jp_3067_:
{
if (v___y_3068_ == 0)
{
lean_object* v___x_3080_; 
v___x_3080_ = l_Lean_Meta_Grind_proveEq_x3f(v_fst_3062_, v_lhs_x27_3069_, v___y_3068_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref_known(v___x_3080_, 1);
v_____x_3014_ = v_a_3081_;
v___y_3015_ = v___y_3076_;
v___y_3016_ = v___y_3077_;
v___y_3017_ = v___y_3078_;
v___y_3018_ = v___y_3079_;
goto v___jp_3013_;
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
lean_dec_ref(v___x_3006_);
lean_del_object(v___x_2988_);
v_a_3082_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___x_3080_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3080_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3087_; 
if (v_isShared_3085_ == 0)
{
v___x_3087_ = v___x_3084_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
else
{
lean_object* v___x_3090_; 
v___x_3090_ = l_Lean_Meta_Grind_proveHEq_x3f(v_fst_3062_, v_lhs_x27_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3091_);
lean_dec_ref_known(v___x_3090_, 1);
v_____x_3014_ = v_a_3091_;
v___y_3015_ = v___y_3076_;
v___y_3016_ = v___y_3077_;
v___y_3017_ = v___y_3078_;
v___y_3018_ = v___y_3079_;
goto v___jp_3013_;
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_dec_ref(v___x_3006_);
lean_del_object(v___x_2988_);
v_a_3092_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_3090_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3090_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
}
v___jp_3100_:
{
lean_object* v___x_3114_; 
lean_inc_ref(v___y_3101_);
v___x_3114_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(v___y_3101_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3149_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3117_ = v___x_3114_;
v_isShared_3118_ = v_isSharedCheck_3149_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3114_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3149_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
uint8_t v___x_3119_; 
v___x_3119_ = lean_unbox(v_a_3115_);
lean_dec(v_a_3115_);
if (v___x_3119_ == 0)
{
lean_object* v___x_3120_; lean_object* v___x_3122_; 
lean_dec_ref(v___y_3103_);
lean_dec_ref(v___y_3101_);
lean_dec(v_fst_3062_);
lean_del_object(v___x_2988_);
v___x_3120_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 1, v___x_3006_);
lean_ctor_set(v___x_3065_, 0, v___x_3120_);
v___x_3122_ = v___x_3065_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3120_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v___x_3006_);
v___x_3122_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
lean_object* v___x_3124_; 
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 0, v___x_3122_);
v___x_3124_ = v___x_3117_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
else
{
lean_object* v___x_3127_; 
lean_del_object(v___x_3117_);
lean_inc_ref(v___y_3103_);
v___x_3127_ = l_Lean_Meta_isDefEqD(v___y_3103_, v___y_3101_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3140_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3140_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3140_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
uint8_t v___x_3132_; 
v___x_3132_ = lean_unbox(v_a_3128_);
lean_dec(v_a_3128_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3133_; lean_object* v___x_3135_; 
lean_dec_ref(v___y_3103_);
lean_dec(v_fst_3062_);
lean_del_object(v___x_2988_);
v___x_3133_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 1, v___x_3006_);
lean_ctor_set(v___x_3065_, 0, v___x_3133_);
v___x_3135_ = v___x_3065_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_3133_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v___x_3006_);
v___x_3135_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
lean_object* v___x_3137_; 
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v___x_3135_);
v___x_3137_ = v___x_3130_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
else
{
lean_del_object(v___x_3130_);
lean_del_object(v___x_3065_);
v___y_3068_ = v___y_3102_;
v_lhs_x27_3069_ = v___y_3103_;
v___y_3070_ = v___y_3104_;
v___y_3071_ = v___y_3105_;
v___y_3072_ = v___y_3106_;
v___y_3073_ = v___y_3107_;
v___y_3074_ = v___y_3108_;
v___y_3075_ = v___y_3109_;
v___y_3076_ = v___y_3110_;
v___y_3077_ = v___y_3111_;
v___y_3078_ = v___y_3112_;
v___y_3079_ = v___y_3113_;
goto v___jp_3067_;
}
}
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec_ref(v___y_3103_);
lean_del_object(v___x_3065_);
lean_dec(v_fst_3062_);
lean_dec_ref(v___x_3006_);
lean_del_object(v___x_2988_);
v_a_3141_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3127_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3127_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec_ref(v___y_3103_);
lean_dec_ref(v___y_3101_);
lean_del_object(v___x_3065_);
lean_dec(v_fst_3062_);
lean_dec_ref(v___x_3006_);
lean_del_object(v___x_2988_);
v_a_3150_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3114_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3114_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
v___jp_3158_:
{
lean_object* v___x_3161_; 
lean_inc_ref(v___y_3159_);
lean_inc(v_fst_3062_);
v___x_3161_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_fst_3062_, v___y_3159_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_toCold_3162_; lean_object* v_options_3163_; uint8_t v_hasTrace_3164_; 
v_toCold_3162_ = lean_ctor_get(v___y_2976_, 0);
v_options_3163_ = lean_ctor_get(v_toCold_3162_, 2);
v_hasTrace_3164_ = lean_ctor_get_uint8(v_options_3163_, sizeof(void*)*1);
if (v_hasTrace_3164_ == 0)
{
lean_object* v_a_3165_; 
lean_del_object(v___x_3060_);
v_a_3165_ = lean_ctor_get(v___x_3161_, 0);
lean_inc(v_a_3165_);
lean_dec_ref_known(v___x_3161_, 1);
v___y_3101_ = v___y_3159_;
v___y_3102_ = v___y_3160_;
v___y_3103_ = v_a_3165_;
v___y_3104_ = v___y_2968_;
v___y_3105_ = v___y_2969_;
v___y_3106_ = v___y_2970_;
v___y_3107_ = v___y_2971_;
v___y_3108_ = v___y_2972_;
v___y_3109_ = v___y_2973_;
v___y_3110_ = v___y_2974_;
v___y_3111_ = v___y_2975_;
v___y_3112_ = v___y_2976_;
v___y_3113_ = v___y_2977_;
goto v___jp_3100_;
}
else
{
lean_object* v_a_3166_; lean_object* v_inheritedTraceOptions_3167_; lean_object* v___x_3168_; uint8_t v___x_3169_; 
v_a_3166_ = lean_ctor_get(v___x_3161_, 0);
lean_inc(v_a_3166_);
lean_dec_ref_known(v___x_3161_, 1);
v_inheritedTraceOptions_3167_ = lean_ctor_get(v_toCold_3162_, 11);
v___x_3168_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3);
v___x_3169_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3167_, v_options_3163_, v___x_3168_);
if (v___x_3169_ == 0)
{
lean_del_object(v___x_3060_);
v___y_3101_ = v___y_3159_;
v___y_3102_ = v___y_3160_;
v___y_3103_ = v_a_3166_;
v___y_3104_ = v___y_2968_;
v___y_3105_ = v___y_2969_;
v___y_3106_ = v___y_2970_;
v___y_3107_ = v___y_2971_;
v___y_3108_ = v___y_2972_;
v___y_3109_ = v___y_2973_;
v___y_3110_ = v___y_2974_;
v___y_3111_ = v___y_2975_;
v___y_3112_ = v___y_2976_;
v___y_3113_ = v___y_2977_;
goto v___jp_3100_;
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3173_; 
lean_inc(v_a_3166_);
v___x_3170_ = l_Lean_MessageData_ofExpr(v_a_3166_);
v___x_3171_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5);
if (v_isShared_3061_ == 0)
{
lean_ctor_set_tag(v___x_3060_, 7);
lean_ctor_set(v___x_3060_, 1, v___x_3171_);
lean_ctor_set(v___x_3060_, 0, v___x_3170_);
v___x_3173_ = v___x_3060_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3170_);
lean_ctor_set(v_reuseFailAlloc_3185_, 1, v___x_3171_);
v___x_3173_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
lean_inc_ref(v___y_3159_);
v___x_3174_ = l_Lean_MessageData_ofExpr(v___y_3159_);
v___x_3175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3173_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3011_, v___x_3175_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_dec_ref_known(v___x_3176_, 1);
v___y_3101_ = v___y_3159_;
v___y_3102_ = v___y_3160_;
v___y_3103_ = v_a_3166_;
v___y_3104_ = v___y_2968_;
v___y_3105_ = v___y_2969_;
v___y_3106_ = v___y_2970_;
v___y_3107_ = v___y_2971_;
v___y_3108_ = v___y_2972_;
v___y_3109_ = v___y_2973_;
v___y_3110_ = v___y_2974_;
v___y_3111_ = v___y_2975_;
v___y_3112_ = v___y_2976_;
v___y_3113_ = v___y_2977_;
goto v___jp_3100_;
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec(v_a_3166_);
lean_dec_ref(v___y_3159_);
lean_del_object(v___x_3065_);
lean_dec(v_fst_3062_);
lean_dec_ref(v___x_3006_);
lean_del_object(v___x_2988_);
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3176_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3176_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3193_; 
lean_dec_ref(v___y_3159_);
lean_del_object(v___x_3065_);
lean_dec(v_fst_3062_);
lean_del_object(v___x_3060_);
lean_dec_ref(v___x_3006_);
lean_del_object(v___x_2988_);
v_a_3186_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3188_ = v___x_3161_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3161_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3191_; 
if (v_isShared_3189_ == 0)
{
v___x_3191_ = v___x_3188_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
v___jp_3194_:
{
lean_object* v___x_3196_; 
v___x_3196_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v_snd_3063_, v___y_2975_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; uint8_t v___x_3198_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3197_);
lean_dec_ref_known(v___x_3196_, 1);
v___x_3198_ = l_Lean_Expr_hasExprMVar(v_a_3197_);
if (v___x_3198_ == 0)
{
lean_object* v___x_3199_; 
v___x_3199_ = l_Lean_Meta_Grind_isEqv___redArg(v_fst_3062_, v_a_3197_, v___y_2968_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; uint8_t v___x_3201_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3200_);
lean_dec_ref_known(v___x_3199_, 1);
v___x_3201_ = lean_unbox(v_a_3200_);
lean_dec(v_a_3200_);
if (v___x_3201_ == 0)
{
v___y_3159_ = v_a_3197_;
v___y_3160_ = v___y_3195_;
goto v___jp_3158_;
}
else
{
lean_del_object(v___x_3065_);
lean_del_object(v___x_3060_);
v___y_3068_ = v___y_3195_;
v_lhs_x27_3069_ = v_a_3197_;
v___y_3070_ = v___y_2968_;
v___y_3071_ = v___y_2969_;
v___y_3072_ = v___y_2970_;
v___y_3073_ = v___y_2971_;
v___y_3074_ = v___y_2972_;
v___y_3075_ = v___y_2973_;
v___y_3076_ = v___y_2974_;
v___y_3077_ = v___y_2975_;
v___y_3078_ = v___y_2976_;
v___y_3079_ = v___y_2977_;
goto v___jp_3067_;
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec(v_a_3197_);
lean_del_object(v___x_3065_);
lean_dec(v_fst_3062_);
lean_del_object(v___x_3060_);
lean_dec_ref(v___x_3006_);
lean_del_object(v___x_2988_);
v_a_3202_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3199_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3199_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
else
{
v___y_3159_ = v_a_3197_;
v___y_3160_ = v___y_3195_;
goto v___jp_3158_;
}
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
lean_del_object(v___x_3065_);
lean_dec(v_fst_3062_);
lean_del_object(v___x_3060_);
lean_dec_ref(v___x_3006_);
lean_del_object(v___x_2988_);
v_a_3210_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___x_3196_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3196_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3225_; 
lean_dec(v___x_3055_);
lean_dec(v___x_3002_);
lean_del_object(v___x_2988_);
v___x_3222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
v___x_3223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
lean_ctor_set(v___x_3223_, 1, v___x_3006_);
if (v_isShared_3054_ == 0)
{
lean_ctor_set(v___x_3053_, 0, v___x_3223_);
v___x_3225_ = v___x_3053_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3223_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
else
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
lean_dec_ref(v___x_3006_);
lean_dec(v___x_3002_);
lean_del_object(v___x_2988_);
v_a_3228_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3230_ = v___x_3050_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3050_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3228_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
v___jp_3013_:
{
if (lean_obj_tag(v_____x_3014_) == 1)
{
lean_object* v_val_3019_; lean_object* v___x_3020_; 
v_val_3019_ = lean_ctor_get(v_____x_3014_, 0);
lean_inc(v_val_3019_);
lean_dec_ref_known(v_____x_3014_, 1);
lean_inc(v_a_3012_);
v___x_3020_ = l_Lean_Meta_isExprDefEq(v_a_3012_, v_val_3019_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3036_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3023_ = v___x_3020_;
v_isShared_3024_ = v_isSharedCheck_3036_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_3020_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3036_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
uint8_t v___x_3025_; 
v___x_3025_ = lean_unbox(v_a_3021_);
lean_dec(v_a_3021_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; lean_object* v___x_3028_; 
v___x_3026_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 1, v___x_3006_);
lean_ctor_set(v___x_2988_, 0, v___x_3026_);
v___x_3028_ = v___x_2988_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3026_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v___x_3006_);
v___x_3028_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3030_; 
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 0, v___x_3028_);
v___x_3030_ = v___x_3023_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
else
{
lean_object* v___x_3034_; 
lean_del_object(v___x_3023_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 1, v___x_3006_);
lean_ctor_set(v___x_2988_, 0, v___x_2993_);
v___x_3034_ = v___x_2988_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_2993_);
lean_ctor_set(v_reuseFailAlloc_3035_, 1, v___x_3006_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
v_a_2980_ = v___x_3034_;
goto v___jp_2979_;
}
}
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec_ref(v___x_3006_);
lean_del_object(v___x_2988_);
v_a_3037_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3020_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3020_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
else
{
lean_object* v___x_3045_; lean_object* v___x_3047_; 
lean_dec(v_____x_3014_);
v___x_3045_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 1, v___x_3006_);
lean_ctor_set(v___x_2988_, 0, v___x_3045_);
v___x_3047_ = v___x_2988_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3045_);
lean_ctor_set(v_reuseFailAlloc_3049_, 1, v___x_3006_);
v___x_3047_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
lean_object* v___x_3048_; 
v___x_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
return v___x_3048_;
}
}
}
}
}
}
}
}
}
v___jp_2979_:
{
size_t v___x_2981_; size_t v___x_2982_; 
v___x_2981_ = ((size_t)1ULL);
v___x_2982_ = lean_usize_add(v_i_2966_, v___x_2981_);
v_i_2966_ = v___x_2982_;
v_b_2967_ = v_a_2980_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___boxed(lean_object* v_as_3243_, lean_object* v_sz_3244_, lean_object* v_i_3245_, lean_object* v_b_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
size_t v_sz_boxed_3258_; size_t v_i_boxed_3259_; lean_object* v_res_3260_; 
v_sz_boxed_3258_ = lean_unbox_usize(v_sz_3244_);
lean_dec(v_sz_3244_);
v_i_boxed_3259_ = lean_unbox_usize(v_i_3245_);
lean_dec(v_i_3245_);
v_res_3260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(v_as_3243_, v_sz_boxed_3258_, v_i_boxed_3259_, v_b_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v_as_3243_);
return v_res_3260_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3262_ = ((lean_object*)(l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__0));
v___x_3263_ = l_Lean_stringToMessageData(v___x_3262_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1(lean_object* v_arg_3264_, uint8_t v___x_3265_, lean_object* v_e_3266_, lean_object* v___f_3267_, lean_object* v_cls_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
lean_object* v___x_3280_; 
lean_inc_ref(v_arg_3264_);
v___x_3280_ = l_Lean_Meta_forallMetaTelescope(v_arg_3264_, v___x_3265_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; lean_object* v_fst_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3400_; 
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
lean_inc(v_a_3281_);
lean_dec_ref_known(v___x_3280_, 1);
v_fst_3282_ = lean_ctor_get(v_a_3281_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v_a_3281_);
if (v_isSharedCheck_3400_ == 0)
{
lean_object* v_unused_3401_; 
v_unused_3401_ = lean_ctor_get(v_a_3281_, 1);
lean_dec(v_unused_3401_);
v___x_3284_ = v_a_3281_;
v_isShared_3285_ = v_isSharedCheck_3400_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_fst_3282_);
lean_dec(v_a_3281_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3400_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3292_; 
v___x_3286_ = l_Lean_Meta_mkGenDiseqMask(v_arg_3264_);
lean_dec_ref(v_arg_3264_);
v___x_3287_ = lean_unsigned_to_nat(0u);
v___x_3288_ = lean_array_get_size(v___x_3286_);
v___x_3289_ = l_Array_toSubarray___redArg(v___x_3286_, v___x_3287_, v___x_3288_);
v___x_3290_ = lean_box(0);
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 1, v___x_3289_);
lean_ctor_set(v___x_3284_, 0, v___x_3290_);
v___x_3292_ = v___x_3284_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3290_);
lean_ctor_set(v_reuseFailAlloc_3399_, 1, v___x_3289_);
v___x_3292_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
size_t v_sz_3293_; size_t v___x_3294_; lean_object* v___x_3295_; 
v_sz_3293_ = lean_array_size(v_fst_3282_);
v___x_3294_ = ((size_t)0ULL);
v___x_3295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(v_fst_3282_, v_sz_3293_, v___x_3294_, v___x_3292_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3390_; 
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3298_ = v___x_3295_;
v_isShared_3299_ = v_isSharedCheck_3390_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3295_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3390_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v_fst_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3388_; 
v_fst_3300_ = lean_ctor_get(v_a_3296_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v_a_3296_);
if (v_isSharedCheck_3388_ == 0)
{
lean_object* v_unused_3389_; 
v_unused_3389_ = lean_ctor_get(v_a_3296_, 1);
lean_dec(v_unused_3389_);
v___x_3302_ = v_a_3296_;
v_isShared_3303_ = v_isSharedCheck_3388_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_fst_3300_);
lean_dec(v_a_3296_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3388_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
if (lean_obj_tag(v_fst_3300_) == 0)
{
lean_object* v___x_3304_; 
lean_del_object(v___x_3298_);
lean_inc_ref(v_e_3266_);
v___x_3304_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_3266_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3375_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_a_3305_);
lean_dec_ref_known(v___x_3304_, 1);
v___x_3306_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3266_, v_a_3305_);
v___x_3307_ = l_Lean_mkAppN(v___x_3306_, v_fst_3282_);
lean_dec(v_fst_3282_);
v___x_3308_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v___x_3307_, v___y_3276_);
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3311_ = v___x_3308_;
v_isShared_3312_ = v_isSharedCheck_3375_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3308_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3375_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3318_; 
lean_inc(v_a_3309_);
v___x_3318_ = l_Lean_Meta_hasAssignableMVar(v_a_3309_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3366_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3321_ = v___x_3318_;
v_isShared_3322_ = v_isSharedCheck_3366_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3318_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3366_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
uint8_t v___x_3323_; 
v___x_3323_ = lean_unbox(v_a_3319_);
lean_dec(v_a_3319_);
if (v___x_3323_ == 0)
{
lean_object* v_toCold_3324_; lean_object* v_inheritedTraceOptions_3325_; lean_object* v___x_3326_; 
lean_del_object(v___x_3321_);
v_toCold_3324_ = lean_ctor_get(v___y_3277_, 0);
v_inheritedTraceOptions_3325_ = lean_ctor_get(v_toCold_3324_, 11);
lean_inc(v___y_3278_);
lean_inc_ref(v___y_3277_);
lean_inc(v___y_3276_);
lean_inc_ref(v___y_3275_);
lean_inc(v___y_3274_);
lean_inc_ref(v___y_3273_);
lean_inc(v___y_3272_);
lean_inc_ref(v___y_3271_);
lean_inc(v___y_3270_);
lean_inc(v___y_3269_);
lean_inc_ref(v_inheritedTraceOptions_3325_);
v___x_3326_ = lean_apply_12(v___f_3267_, v_inheritedTraceOptions_3325_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, lean_box(0));
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; uint8_t v___x_3328_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v___x_3326_, 1);
v___x_3328_ = lean_unbox(v_a_3327_);
lean_dec(v_a_3327_);
if (v___x_3328_ == 0)
{
lean_del_object(v___x_3302_);
lean_dec(v_cls_3268_);
goto v___jp_3313_;
}
else
{
lean_object* v___x_3329_; 
lean_inc(v___y_3278_);
lean_inc_ref(v___y_3277_);
lean_inc(v___y_3276_);
lean_inc_ref(v___y_3275_);
lean_inc(v_a_3309_);
v___x_3329_ = lean_infer_type(v_a_3309_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3334_; 
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_a_3330_);
lean_dec_ref_known(v___x_3329_, 1);
lean_inc(v_a_3309_);
v___x_3331_ = l_Lean_MessageData_ofExpr(v_a_3309_);
v___x_3332_ = lean_obj_once(&l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1, &l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1_once, _init_l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1);
if (v_isShared_3303_ == 0)
{
lean_ctor_set_tag(v___x_3302_, 7);
lean_ctor_set(v___x_3302_, 1, v___x_3332_);
lean_ctor_set(v___x_3302_, 0, v___x_3331_);
v___x_3334_ = v___x_3302_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3331_);
lean_ctor_set(v_reuseFailAlloc_3346_, 1, v___x_3332_);
v___x_3334_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3335_ = l_Lean_MessageData_ofExpr(v_a_3330_);
v___x_3336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3334_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
v___x_3337_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3268_, v___x_3336_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_dec_ref_known(v___x_3337_, 1);
goto v___jp_3313_;
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
lean_del_object(v___x_3311_);
lean_dec(v_a_3309_);
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_del_object(v___x_3311_);
lean_dec(v_a_3309_);
lean_del_object(v___x_3302_);
lean_dec(v_cls_3268_);
v_a_3347_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3329_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3329_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
}
else
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3362_; 
lean_del_object(v___x_3311_);
lean_dec(v_a_3309_);
lean_del_object(v___x_3302_);
lean_dec(v_cls_3268_);
v_a_3355_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3357_ = v___x_3326_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3326_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3360_; 
if (v_isShared_3358_ == 0)
{
v___x_3360_ = v___x_3357_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3355_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
else
{
lean_object* v___x_3364_; 
lean_del_object(v___x_3311_);
lean_dec(v_a_3309_);
lean_del_object(v___x_3302_);
lean_dec(v_cls_3268_);
lean_dec_ref(v___f_3267_);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 0, v___x_3290_);
v___x_3364_ = v___x_3321_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3290_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
else
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
lean_del_object(v___x_3311_);
lean_dec(v_a_3309_);
lean_del_object(v___x_3302_);
lean_dec(v_cls_3268_);
lean_dec_ref(v___f_3267_);
v_a_3367_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3318_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3318_);
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
v___jp_3313_:
{
lean_object* v___x_3314_; lean_object* v___x_3316_; 
v___x_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3314_, 0, v_a_3309_);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 0, v___x_3314_);
v___x_3316_ = v___x_3311_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3314_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
lean_del_object(v___x_3302_);
lean_dec(v_fst_3282_);
lean_dec(v_cls_3268_);
lean_dec_ref(v___f_3267_);
lean_dec_ref(v_e_3266_);
v_a_3376_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3304_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3304_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
else
{
lean_object* v_val_3384_; lean_object* v___x_3386_; 
lean_del_object(v___x_3302_);
lean_dec(v_fst_3282_);
lean_dec(v_cls_3268_);
lean_dec_ref(v___f_3267_);
lean_dec_ref(v_e_3266_);
v_val_3384_ = lean_ctor_get(v_fst_3300_, 0);
lean_inc(v_val_3384_);
lean_dec_ref_known(v_fst_3300_, 1);
if (v_isShared_3299_ == 0)
{
lean_ctor_set(v___x_3298_, 0, v_val_3384_);
v___x_3386_ = v___x_3298_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_val_3384_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
lean_dec(v_fst_3282_);
lean_dec(v_cls_3268_);
lean_dec_ref(v___f_3267_);
lean_dec_ref(v_e_3266_);
v_a_3391_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3295_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3295_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
}
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec(v_cls_3268_);
lean_dec_ref(v___f_3267_);
lean_dec_ref(v_e_3266_);
lean_dec_ref(v_arg_3264_);
v_a_3402_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3280_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3280_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1___boxed(lean_object* v_arg_3410_, lean_object* v___x_3411_, lean_object* v_e_3412_, lean_object* v___f_3413_, lean_object* v_cls_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
uint8_t v___x_77358__boxed_3426_; lean_object* v_res_3427_; 
v___x_77358__boxed_3426_ = lean_unbox(v___x_3411_);
v_res_3427_ = l_Lean_Meta_Grind_tryToProveFalse___lam__1(v_arg_3410_, v___x_77358__boxed_3426_, v_e_3412_, v___f_3413_, v_cls_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec(v___y_3415_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse(lean_object* v_e_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_){
_start:
{
lean_object* v_toCold_3445_; lean_object* v_inheritedTraceOptions_3446_; lean_object* v_cls_3447_; lean_object* v___f_3448_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___x_3500_; lean_object* v_a_3501_; uint8_t v___x_3502_; 
v_toCold_3445_ = lean_ctor_get(v_a_3439_, 0);
v_inheritedTraceOptions_3446_ = lean_ctor_get(v_toCold_3445_, 11);
v_cls_3447_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1));
v___f_3448_ = ((lean_object*)(l_Lean_Meta_Grind_tryToProveFalse___closed__0));
v___x_3500_ = l_Lean_Meta_Grind_tryToProveFalse___lam__0(v_cls_3447_, v_inheritedTraceOptions_3446_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_);
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref(v___x_3500_);
v___x_3502_ = lean_unbox(v_a_3501_);
lean_dec(v_a_3501_);
if (v___x_3502_ == 0)
{
v___y_3450_ = v_a_3431_;
v___y_3451_ = v_a_3432_;
v___y_3452_ = v_a_3433_;
v___y_3453_ = v_a_3434_;
v___y_3454_ = v_a_3435_;
v___y_3455_ = v_a_3436_;
v___y_3456_ = v_a_3437_;
v___y_3457_ = v_a_3438_;
v___y_3458_ = v_a_3439_;
v___y_3459_ = v_a_3440_;
goto v___jp_3449_;
}
else
{
lean_object* v___x_3503_; 
v___x_3503_ = l_Lean_Meta_Grind_updateLastTag(v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v___x_3504_; lean_object* v___x_3505_; 
lean_dec_ref_known(v___x_3503_, 1);
lean_inc_ref(v_e_3430_);
v___x_3504_ = l_Lean_MessageData_ofExpr(v_e_3430_);
v___x_3505_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3447_, v___x_3504_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_dec_ref_known(v___x_3505_, 1);
v___y_3450_ = v_a_3431_;
v___y_3451_ = v_a_3432_;
v___y_3452_ = v_a_3433_;
v___y_3453_ = v_a_3434_;
v___y_3454_ = v_a_3435_;
v___y_3455_ = v_a_3436_;
v___y_3456_ = v_a_3437_;
v___y_3457_ = v_a_3438_;
v___y_3458_ = v_a_3439_;
v___y_3459_ = v_a_3440_;
goto v___jp_3449_;
}
else
{
lean_dec_ref(v_e_3430_);
return v___x_3505_;
}
}
else
{
lean_dec_ref(v_e_3430_);
return v___x_3503_;
}
}
v___jp_3442_:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3443_ = lean_box(0);
v___x_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3443_);
return v___x_3444_;
}
v___jp_3449_:
{
lean_object* v___x_3460_; 
lean_inc_ref(v_e_3430_);
v___x_3460_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3430_, v___y_3457_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3462_; uint8_t v___x_3463_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref_known(v___x_3460_, 1);
v___x_3462_ = l_Lean_Expr_cleanupAnnotations(v_a_3461_);
lean_dec(v_a_3461_);
v___x_3463_ = l_Lean_Expr_isApp(v___x_3462_);
if (v___x_3463_ == 0)
{
lean_dec_ref(v___x_3462_);
lean_dec_ref(v_e_3430_);
goto v___jp_3442_;
}
else
{
lean_object* v___x_3464_; lean_object* v___x_3465_; uint8_t v___x_3466_; 
v___x_3464_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3462_);
v___x_3465_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3466_ = l_Lean_Expr_isConstOf(v___x_3464_, v___x_3465_);
lean_dec_ref(v___x_3464_);
if (v___x_3466_ == 0)
{
lean_dec_ref(v___x_3462_);
lean_dec_ref(v_e_3430_);
goto v___jp_3442_;
}
else
{
lean_object* v_arg_3467_; uint8_t v___x_3468_; lean_object* v___x_3469_; lean_object* v___f_3470_; uint8_t v___x_3471_; lean_object* v___x_3472_; 
v_arg_3467_ = lean_ctor_get(v___x_3462_, 1);
lean_inc_ref(v_arg_3467_);
lean_dec_ref(v___x_3462_);
v___x_3468_ = 0;
v___x_3469_ = lean_box(v___x_3468_);
v___f_3470_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_tryToProveFalse___lam__1___boxed), 16, 5);
lean_closure_set(v___f_3470_, 0, v_arg_3467_);
lean_closure_set(v___f_3470_, 1, v___x_3469_);
lean_closure_set(v___f_3470_, 2, v_e_3430_);
lean_closure_set(v___f_3470_, 3, v___f_3448_);
lean_closure_set(v___f_3470_, 4, v_cls_3447_);
v___x_3471_ = 0;
v___x_3472_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(v___f_3470_, v___x_3471_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3483_; 
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3475_ = v___x_3472_;
v_isShared_3476_ = v_isSharedCheck_3483_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3472_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3483_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
if (lean_obj_tag(v_a_3473_) == 1)
{
lean_object* v_val_3477_; lean_object* v___x_3478_; 
lean_del_object(v___x_3475_);
v_val_3477_ = lean_ctor_get(v_a_3473_, 0);
lean_inc(v_val_3477_);
lean_dec_ref_known(v_a_3473_, 1);
v___x_3478_ = l_Lean_Meta_Grind_closeGoal(v_val_3477_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
return v___x_3478_;
}
else
{
lean_object* v___x_3479_; lean_object* v___x_3481_; 
lean_dec(v_a_3473_);
v___x_3479_ = lean_box(0);
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 0, v___x_3479_);
v___x_3481_ = v___x_3475_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3479_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
else
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
v_a_3484_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___x_3472_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3472_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3484_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
}
}
else
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3499_; 
lean_dec_ref(v_e_3430_);
v_a_3492_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3494_ = v___x_3460_;
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3460_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3492_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___boxed(lean_object* v_e_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
lean_dec(v_a_3516_);
lean_dec_ref(v_a_3515_);
lean_dec(v_a_3514_);
lean_dec_ref(v_a_3513_);
lean_dec(v_a_3512_);
lean_dec_ref(v_a_3511_);
lean_dec(v_a_3510_);
lean_dec_ref(v_a_3509_);
lean_dec(v_a_3508_);
lean_dec(v_a_3507_);
return v_res_3518_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1(void){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = ((lean_object*)(l_Lean_Meta_Grind_propagateMatchCondUp___closed__0));
v___x_3521_ = l_Lean_stringToMessageData(v___x_3520_);
return v___x_3521_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3(void){
_start:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3523_ = ((lean_object*)(l_Lean_Meta_Grind_propagateMatchCondUp___closed__2));
v___x_3524_ = l_Lean_stringToMessageData(v___x_3523_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp(lean_object* v_e_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_){
_start:
{
lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v_toCold_3551_; lean_object* v_options_3552_; lean_object* v_inheritedTraceOptions_3553_; uint8_t v_hasTrace_3554_; lean_object* v_cls_3555_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; 
v_toCold_3551_ = lean_ctor_get(v_a_3534_, 0);
v_options_3552_ = lean_ctor_get(v_toCold_3551_, 2);
v_inheritedTraceOptions_3553_ = lean_ctor_get(v_toCold_3551_, 11);
v_hasTrace_3554_ = lean_ctor_get_uint8(v_options_3552_, sizeof(void*)*1);
v_cls_3555_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
if (v_hasTrace_3554_ == 0)
{
v___y_3557_ = v_a_3526_;
v___y_3558_ = v_a_3527_;
v___y_3559_ = v_a_3528_;
v___y_3560_ = v_a_3529_;
v___y_3561_ = v_a_3530_;
v___y_3562_ = v_a_3531_;
v___y_3563_ = v_a_3532_;
v___y_3564_ = v_a_3533_;
v___y_3565_ = v_a_3534_;
v___y_3566_ = v_a_3535_;
goto v___jp_3556_;
}
else
{
lean_object* v___x_3663_; uint8_t v___x_3664_; 
v___x_3663_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_3664_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3553_, v_options_3552_, v___x_3663_);
if (v___x_3664_ == 0)
{
v___y_3557_ = v_a_3526_;
v___y_3558_ = v_a_3527_;
v___y_3559_ = v_a_3528_;
v___y_3560_ = v_a_3529_;
v___y_3561_ = v_a_3530_;
v___y_3562_ = v_a_3531_;
v___y_3563_ = v_a_3532_;
v___y_3564_ = v_a_3533_;
v___y_3565_ = v_a_3534_;
v___y_3566_ = v_a_3535_;
goto v___jp_3556_;
}
else
{
lean_object* v___x_3665_; 
v___x_3665_ = l_Lean_Meta_Grind_updateLastTag(v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
lean_dec_ref_known(v___x_3665_, 1);
v___x_3666_ = lean_obj_once(&l_Lean_Meta_Grind_propagateMatchCondUp___closed__3, &l_Lean_Meta_Grind_propagateMatchCondUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3);
lean_inc_ref(v_e_3525_);
v___x_3667_ = l_Lean_indentExpr(v_e_3525_);
v___x_3668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3666_);
lean_ctor_set(v___x_3668_, 1, v___x_3667_);
v___x_3669_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3555_, v___x_3668_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_dec_ref_known(v___x_3669_, 1);
v___y_3557_ = v_a_3526_;
v___y_3558_ = v_a_3527_;
v___y_3559_ = v_a_3528_;
v___y_3560_ = v_a_3529_;
v___y_3561_ = v_a_3530_;
v___y_3562_ = v_a_3531_;
v___y_3563_ = v_a_3532_;
v___y_3564_ = v_a_3533_;
v___y_3565_ = v_a_3534_;
v___y_3566_ = v_a_3535_;
goto v___jp_3556_;
}
else
{
lean_dec_ref(v_e_3525_);
return v___x_3669_;
}
}
else
{
lean_dec_ref(v_e_3525_);
return v___x_3665_;
}
}
}
v___jp_3537_:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3538_ = lean_box(0);
v___x_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3538_);
return v___x_3539_;
}
v___jp_3540_:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
lean_inc_ref(v_e_3525_);
v___x_3549_ = l_Lean_Meta_mkEqTrueCore(v_e_3525_, v___y_3541_);
v___x_3550_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_3525_, v___x_3549_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
return v___x_3550_;
}
v___jp_3556_:
{
lean_object* v___x_3567_; 
lean_inc_ref(v_e_3525_);
v___x_3567_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3525_, v___y_3557_, v___y_3561_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; uint8_t v___x_3569_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_a_3568_);
lean_dec_ref_known(v___x_3567_, 1);
v___x_3569_ = lean_unbox(v_a_3568_);
lean_dec(v_a_3568_);
if (v___x_3569_ == 0)
{
lean_object* v___x_3570_; 
lean_inc_ref(v_e_3525_);
v___x_3570_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3525_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3626_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3573_ = v___x_3570_;
v_isShared_3574_ = v_isSharedCheck_3626_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3570_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3626_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
uint8_t v___x_3575_; 
v___x_3575_ = lean_unbox(v_a_3571_);
lean_dec(v_a_3571_);
if (v___x_3575_ == 0)
{
lean_object* v___x_3576_; lean_object* v___x_3578_; 
lean_dec_ref(v_e_3525_);
v___x_3576_ = lean_box(0);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v___x_3576_);
v___x_3578_ = v___x_3573_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3576_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
else
{
lean_object* v___x_3580_; 
lean_del_object(v___x_3573_);
lean_inc_ref(v_e_3525_);
v___x_3580_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_3525_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v_a_3581_; 
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_a_3581_);
lean_dec_ref_known(v___x_3580_, 1);
if (lean_obj_tag(v_a_3581_) == 1)
{
lean_object* v_toCold_3582_; lean_object* v_options_3583_; uint8_t v_hasTrace_3584_; 
v_toCold_3582_ = lean_ctor_get(v___y_3565_, 0);
v_options_3583_ = lean_ctor_get(v_toCold_3582_, 2);
v_hasTrace_3584_ = lean_ctor_get_uint8(v_options_3583_, sizeof(void*)*1);
if (v_hasTrace_3584_ == 0)
{
lean_object* v_val_3585_; 
v_val_3585_ = lean_ctor_get(v_a_3581_, 0);
lean_inc(v_val_3585_);
lean_dec_ref_known(v_a_3581_, 1);
v___y_3541_ = v_val_3585_;
v___y_3542_ = v___y_3557_;
v___y_3543_ = v___y_3559_;
v___y_3544_ = v___y_3561_;
v___y_3545_ = v___y_3563_;
v___y_3546_ = v___y_3564_;
v___y_3547_ = v___y_3565_;
v___y_3548_ = v___y_3566_;
goto v___jp_3540_;
}
else
{
lean_object* v_val_3586_; lean_object* v_inheritedTraceOptions_3587_; lean_object* v___x_3588_; uint8_t v___x_3589_; 
v_val_3586_ = lean_ctor_get(v_a_3581_, 0);
lean_inc(v_val_3586_);
lean_dec_ref_known(v_a_3581_, 1);
v_inheritedTraceOptions_3587_ = lean_ctor_get(v_toCold_3582_, 11);
v___x_3588_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_3589_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3587_, v_options_3583_, v___x_3588_);
if (v___x_3589_ == 0)
{
v___y_3541_ = v_val_3586_;
v___y_3542_ = v___y_3557_;
v___y_3543_ = v___y_3559_;
v___y_3544_ = v___y_3561_;
v___y_3545_ = v___y_3563_;
v___y_3546_ = v___y_3564_;
v___y_3547_ = v___y_3565_;
v___y_3548_ = v___y_3566_;
goto v___jp_3540_;
}
else
{
lean_object* v___x_3590_; 
v___x_3590_ = l_Lean_Meta_Grind_updateLastTag(v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v___x_3591_; 
lean_dec_ref_known(v___x_3590_, 1);
lean_inc(v___y_3566_);
lean_inc_ref(v___y_3565_);
lean_inc(v___y_3564_);
lean_inc_ref(v___y_3563_);
lean_inc(v_val_3586_);
v___x_3591_ = lean_infer_type(v_val_3586_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v_a_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_a_3592_);
lean_dec_ref_known(v___x_3591_, 1);
v___x_3593_ = l_Lean_MessageData_ofExpr(v_a_3592_);
v___x_3594_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3555_, v___x_3593_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_dec_ref_known(v___x_3594_, 1);
v___y_3541_ = v_val_3586_;
v___y_3542_ = v___y_3557_;
v___y_3543_ = v___y_3559_;
v___y_3544_ = v___y_3561_;
v___y_3545_ = v___y_3563_;
v___y_3546_ = v___y_3564_;
v___y_3547_ = v___y_3565_;
v___y_3548_ = v___y_3566_;
goto v___jp_3540_;
}
else
{
lean_dec(v_val_3586_);
lean_dec_ref(v_e_3525_);
return v___x_3594_;
}
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
lean_dec(v_val_3586_);
lean_dec_ref(v_e_3525_);
v_a_3595_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3591_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3591_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
else
{
lean_dec(v_val_3586_);
lean_dec_ref(v_e_3525_);
return v___x_3590_;
}
}
}
}
else
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
lean_dec(v_a_3581_);
v___x_3603_ = lean_obj_once(&l_Lean_Meta_Grind_propagateMatchCondUp___closed__1, &l_Lean_Meta_Grind_propagateMatchCondUp___closed__1_once, _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1);
v___x_3604_ = l_Lean_indentExpr(v_e_3525_);
v___x_3605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3603_);
lean_ctor_set(v___x_3605_, 1, v___x_3604_);
v___x_3606_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_3561_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; uint8_t v_verbose_3608_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref_known(v___x_3606_, 1);
v_verbose_3608_ = lean_ctor_get_uint8(v_a_3607_, 0);
lean_dec(v_a_3607_);
if (v_verbose_3608_ == 0)
{
lean_dec_ref_known(v___x_3605_, 2);
goto v___jp_3537_;
}
else
{
lean_object* v___x_3609_; 
v___x_3609_ = l_Lean_Meta_Sym_reportIssue(v___x_3605_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_dec_ref_known(v___x_3609_, 1);
goto v___jp_3537_;
}
else
{
return v___x_3609_;
}
}
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
lean_dec_ref_known(v___x_3605_, 2);
v_a_3610_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3606_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3606_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_dec_ref(v_e_3525_);
v_a_3618_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3580_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3580_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
}
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec_ref(v_e_3525_);
v_a_3627_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3570_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3570_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
else
{
lean_object* v___x_3635_; 
lean_inc_ref(v_e_3525_);
v___x_3635_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3525_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3646_; 
v_a_3636_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3638_ = v___x_3635_;
v_isShared_3639_ = v_isSharedCheck_3646_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3635_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3646_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
uint8_t v___x_3640_; 
v___x_3640_ = lean_unbox(v_a_3636_);
lean_dec(v_a_3636_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3641_; 
lean_del_object(v___x_3638_);
v___x_3641_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3525_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
return v___x_3641_;
}
else
{
lean_object* v___x_3642_; lean_object* v___x_3644_; 
lean_dec_ref(v_e_3525_);
v___x_3642_ = lean_box(0);
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 0, v___x_3642_);
v___x_3644_ = v___x_3638_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3642_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
else
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3654_; 
lean_dec_ref(v_e_3525_);
v_a_3647_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3649_ = v___x_3635_;
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v___x_3635_);
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
}
else
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
lean_dec_ref(v_e_3525_);
v_a_3655_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3567_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3567_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3660_; 
if (v_isShared_3658_ == 0)
{
v___x_3660_ = v___x_3657_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3655_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___boxed(lean_object* v_e_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l_Lean_Meta_Grind_propagateMatchCondUp(v_e_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_);
lean_dec(v_a_3680_);
lean_dec_ref(v_a_3679_);
lean_dec(v_a_3678_);
lean_dec_ref(v_a_3677_);
lean_dec(v_a_3676_);
lean_dec_ref(v_a_3675_);
lean_dec(v_a_3674_);
lean_dec_ref(v_a_3673_);
lean_dec(v_a_3672_);
lean_dec(v_a_3671_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3684_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3685_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondUp___boxed), 12, 0);
v___x_3686_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3684_, v___x_3685_);
return v___x_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_9____boxed(lean_object* v_a_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_9_();
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown(lean_object* v_e_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_){
_start:
{
lean_object* v___x_3701_; 
lean_inc_ref(v_e_3689_);
v___x_3701_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3689_, v_a_3690_, v_a_3694_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3731_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3704_ = v___x_3701_;
v_isShared_3705_ = v_isSharedCheck_3731_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_a_3702_);
lean_dec(v___x_3701_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3731_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
uint8_t v___x_3706_; 
v___x_3706_ = lean_unbox(v_a_3702_);
lean_dec(v_a_3702_);
if (v___x_3706_ == 0)
{
lean_object* v___x_3707_; lean_object* v___x_3709_; 
lean_dec_ref(v_e_3689_);
v___x_3707_ = lean_box(0);
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 0, v___x_3707_);
v___x_3709_ = v___x_3704_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3707_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
else
{
lean_object* v___x_3711_; 
lean_del_object(v___x_3704_);
lean_inc_ref(v_e_3689_);
v___x_3711_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3722_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3714_ = v___x_3711_;
v_isShared_3715_ = v_isSharedCheck_3722_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3711_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3722_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
uint8_t v___x_3716_; 
v___x_3716_ = lean_unbox(v_a_3712_);
lean_dec(v_a_3712_);
if (v___x_3716_ == 0)
{
lean_object* v___x_3717_; 
lean_del_object(v___x_3714_);
v___x_3717_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_);
return v___x_3717_;
}
else
{
lean_object* v___x_3718_; lean_object* v___x_3720_; 
lean_dec_ref(v_e_3689_);
v___x_3718_ = lean_box(0);
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 0, v___x_3718_);
v___x_3720_ = v___x_3714_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3718_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_dec_ref(v_e_3689_);
v_a_3723_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3711_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3711_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec_ref(v_e_3689_);
v_a_3732_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3701_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3701_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___boxed(lean_object* v_e_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_){
_start:
{
lean_object* v_res_3752_; 
v_res_3752_ = l_Lean_Meta_Grind_propagateMatchCondDown(v_e_3740_, v_a_3741_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_);
lean_dec(v_a_3750_);
lean_dec_ref(v_a_3749_);
lean_dec(v_a_3748_);
lean_dec_ref(v_a_3747_);
lean_dec(v_a_3746_);
lean_dec_ref(v_a_3745_);
lean_dec(v_a_3744_);
lean_dec_ref(v_a_3743_);
lean_dec(v_a_3742_);
lean_dec(v_a_3741_);
return v_res_3752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3754_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3755_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondDown___boxed), 12, 0);
v___x_3756_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3754_, v___x_3755_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_9____boxed(lean_object* v_a_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_9_();
return v_res_3758_;
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
