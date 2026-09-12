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
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
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
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_isLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* l_Lean_Meta_normLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_arg_11_; lean_object* v___x_12_; uint8_t v___x_13_; 
v_arg_11_ = lean_ctor_get(v___x_8_, 1);
lean_inc_ref(v_arg_11_);
v___x_12_ = l_Lean_Expr_appFnCleanup___redArg(v___x_8_);
v___x_13_ = l_Lean_Expr_isApp(v___x_12_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; 
lean_dec_ref(v___x_12_);
lean_dec_ref(v_arg_11_);
v___x_14_ = lean_box(0);
return v___x_14_;
}
else
{
lean_object* v_arg_15_; lean_object* v___x_16_; uint8_t v___x_17_; 
v_arg_15_ = lean_ctor_get(v___x_12_, 1);
lean_inc_ref(v_arg_15_);
v___x_16_ = l_Lean_Expr_appFnCleanup___redArg(v___x_12_);
v___x_17_ = l_Lean_Expr_isApp(v___x_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; 
lean_dec_ref(v___x_16_);
lean_dec_ref(v_arg_15_);
lean_dec_ref(v_arg_11_);
v___x_18_ = lean_box(0);
return v___x_18_;
}
else
{
lean_object* v_arg_19_; lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
v_arg_19_ = lean_ctor_get(v___x_16_, 1);
lean_inc_ref(v_arg_19_);
v___x_20_ = l_Lean_Expr_appFnCleanup___redArg(v___x_16_);
v___x_21_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1));
v___x_22_ = l_Lean_Expr_isConstOf(v___x_20_, v___x_21_);
if (v___x_22_ == 0)
{
uint8_t v___x_23_; 
lean_dec_ref(v_arg_15_);
v___x_23_ = l_Lean_Expr_isApp(v___x_20_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; 
lean_dec_ref(v___x_20_);
lean_dec_ref(v_arg_19_);
lean_dec_ref(v_arg_11_);
v___x_24_ = lean_box(0);
return v___x_24_;
}
else
{
lean_object* v_arg_25_; lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v_arg_25_ = lean_ctor_get(v___x_20_, 1);
lean_inc_ref(v_arg_25_);
v___x_26_ = l_Lean_Expr_appFnCleanup___redArg(v___x_20_);
v___x_27_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3));
v___x_28_ = l_Lean_Expr_isConstOf(v___x_26_, v___x_27_);
lean_dec_ref(v___x_26_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; 
lean_dec_ref(v_arg_25_);
lean_dec_ref(v_arg_19_);
lean_dec_ref(v_arg_11_);
v___x_29_ = lean_box(0);
return v___x_29_;
}
else
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_30_, 0, v_arg_25_);
v___x_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_31_, 0, v_arg_19_);
lean_ctor_set(v___x_31_, 1, v_arg_11_);
v___x_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_30_);
lean_ctor_set(v___x_32_, 1, v___x_31_);
v___x_33_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
return v___x_33_;
}
}
}
else
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec_ref(v___x_20_);
lean_dec_ref(v_arg_19_);
v___x_34_ = lean_box(0);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v_arg_15_);
lean_ctor_set(v___x_35_, 1, v_arg_11_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg___lam__0(lean_object* v_body_38_, lean_object* v___x_39_, lean_object* v_____r_40_, lean_object* v_r_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_42_, 0, v_r_41_);
lean_ctor_set(v___x_42_, 1, v_body_38_);
v___x_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_39_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
v___x_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg(lean_object* v_a_45_){
_start:
{
lean_object* v___y_47_; lean_object* v_snd_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_94_; 
v_snd_51_ = lean_ctor_get(v_a_45_, 1);
v_isSharedCheck_94_ = !lean_is_exclusive(v_a_45_);
if (v_isSharedCheck_94_ == 0)
{
lean_object* v_unused_95_; 
v_unused_95_ = lean_ctor_get(v_a_45_, 0);
lean_dec(v_unused_95_);
v___x_53_ = v_a_45_;
v_isShared_54_ = v_isSharedCheck_94_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_snd_51_);
lean_dec(v_a_45_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_94_;
goto v_resetjp_52_;
}
v___jp_46_:
{
if (lean_obj_tag(v___y_47_) == 0)
{
lean_object* v_a_48_; 
v_a_48_ = lean_ctor_get(v___y_47_, 0);
lean_inc(v_a_48_);
lean_dec_ref_known(v___y_47_, 1);
return v_a_48_;
}
else
{
lean_object* v_a_49_; 
v_a_49_ = lean_ctor_get(v___y_47_, 0);
lean_inc(v_a_49_);
lean_dec_ref_known(v___y_47_, 1);
v_a_45_ = v_a_49_;
goto _start;
}
}
v_resetjp_52_:
{
lean_object* v_snd_55_; 
v_snd_55_ = lean_ctor_get(v_snd_51_, 1);
lean_inc(v_snd_55_);
if (lean_obj_tag(v_snd_55_) == 7)
{
lean_object* v_fst_56_; lean_object* v_binderType_57_; lean_object* v_body_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
lean_del_object(v___x_53_);
v_fst_56_ = lean_ctor_get(v_snd_51_, 0);
lean_inc(v_fst_56_);
lean_dec(v_snd_51_);
v_binderType_57_ = lean_ctor_get(v_snd_55_, 1);
lean_inc_ref(v_binderType_57_);
v_body_58_ = lean_ctor_get(v_snd_55_, 2);
lean_inc_ref(v_body_58_);
lean_dec_ref_known(v_snd_55_, 3);
v___x_59_ = lean_box(0);
v___x_60_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_binderType_57_);
if (lean_obj_tag(v___x_60_) == 1)
{
lean_object* v_val_61_; lean_object* v_snd_62_; lean_object* v_fst_63_; lean_object* v_fst_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_77_; 
v_val_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_val_61_);
lean_dec_ref_known(v___x_60_, 1);
v_snd_62_ = lean_ctor_get(v_val_61_, 1);
lean_inc(v_snd_62_);
v_fst_63_ = lean_ctor_get(v_val_61_, 0);
lean_inc(v_fst_63_);
lean_dec(v_val_61_);
v_fst_64_ = lean_ctor_get(v_snd_62_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v_snd_62_);
if (v_isSharedCheck_77_ == 0)
{
lean_object* v_unused_78_; 
v_unused_78_ = lean_ctor_get(v_snd_62_, 1);
lean_dec(v_unused_78_);
v___x_66_ = v_snd_62_;
v_isShared_67_ = v_isSharedCheck_77_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_fst_64_);
lean_dec(v_snd_62_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_77_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
uint8_t v___x_68_; 
v___x_68_ = l_Lean_Expr_hasLooseBVars(v_fst_64_);
if (v___x_68_ == 0)
{
lean_object* v___x_70_; 
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 1, v_fst_63_);
v___x_70_ = v___x_66_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_fst_64_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_fst_63_);
v___x_70_ = v_reuseFailAlloc_74_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = lean_array_push(v_fst_56_, v___x_70_);
v___x_72_ = lean_box(0);
v___x_73_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg___lam__0(v_body_58_, v___x_59_, v___x_72_, v___x_71_);
v___y_47_ = v___x_73_;
goto v___jp_46_;
}
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_del_object(v___x_66_);
lean_dec(v_fst_64_);
lean_dec(v_fst_63_);
v___x_75_ = lean_box(0);
v___x_76_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg___lam__0(v_body_58_, v___x_59_, v___x_75_, v_fst_56_);
v___y_47_ = v___x_76_;
goto v___jp_46_;
}
}
}
else
{
lean_object* v___x_79_; lean_object* v___x_80_; 
lean_dec(v___x_60_);
v___x_79_ = lean_box(0);
v___x_80_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg___lam__0(v_body_58_, v___x_59_, v___x_79_, v_fst_56_);
v___y_47_ = v___x_80_;
goto v___jp_46_;
}
}
else
{
lean_object* v_fst_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_92_; 
v_fst_81_ = lean_ctor_get(v_snd_51_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v_snd_51_);
if (v_isSharedCheck_92_ == 0)
{
lean_object* v_unused_93_; 
v_unused_93_ = lean_ctor_get(v_snd_51_, 1);
lean_dec(v_unused_93_);
v___x_83_ = v_snd_51_;
v_isShared_84_ = v_isSharedCheck_92_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_fst_81_);
lean_dec(v_snd_51_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_92_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; lean_object* v___x_87_; 
lean_inc(v_fst_81_);
v___x_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_85_, 0, v_fst_81_);
if (v_isShared_84_ == 0)
{
v___x_87_ = v___x_83_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_fst_81_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v_snd_55_);
v___x_87_ = v_reuseFailAlloc_91_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_89_; 
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 1, v___x_87_);
lean_ctor_set(v___x_53_, 0, v___x_85_);
v___x_89_ = v___x_53_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_85_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v___x_87_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss(lean_object* v_e_98_){
_start:
{
lean_object* v_r_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v_fst_104_; 
v_r_99_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss___closed__0));
v___x_100_ = lean_box(0);
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v_r_99_);
lean_ctor_set(v___x_101_, 1, v_e_98_);
v___x_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg(v___x_102_);
v_fst_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_fst_104_);
if (lean_obj_tag(v_fst_104_) == 0)
{
lean_object* v_snd_105_; lean_object* v_fst_106_; 
v_snd_105_ = lean_ctor_get(v___x_103_, 1);
lean_inc(v_snd_105_);
lean_dec_ref(v___x_103_);
v_fst_106_ = lean_ctor_get(v_snd_105_, 0);
lean_inc(v_fst_106_);
lean_dec(v_snd_105_);
return v_fst_106_;
}
else
{
lean_object* v_val_107_; 
lean_dec_ref(v___x_103_);
v_val_107_ = lean_ctor_get(v_fst_104_, 0);
lean_inc(v_val_107_);
lean_dec_ref_known(v_fst_104_, 1);
return v_val_107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0(lean_object* v_inst_108_, lean_object* v_a_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg(v_a_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f_spec__0(lean_object* v_msg_111_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = l_Lean_instInhabitedExpr;
v___x_113_ = lean_panic_fn_borrowed(v___x_112_, v_msg_111_);
return v___x_113_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__2));
v___x_118_ = lean_unsigned_to_nat(14u);
v___x_119_ = lean_unsigned_to_nat(22u);
v___x_120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__1));
v___x_121_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__0));
v___x_122_ = l_mkPanicMessageWithDecl(v___x_121_, v___x_120_, v___x_119_, v___x_118_, v___x_117_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f(lean_object* v_e_123_, lean_object* v_lhsNew_124_, lean_object* v_ty_x3f_125_){
_start:
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = l_Lean_Expr_cleanupAnnotations(v_e_123_);
v___x_127_ = l_Lean_Expr_isApp(v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; 
lean_dec_ref(v___x_126_);
lean_dec(v_ty_x3f_125_);
lean_dec_ref(v_lhsNew_124_);
v___x_128_ = lean_box(0);
return v___x_128_;
}
else
{
lean_object* v_arg_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v_arg_129_ = lean_ctor_get(v___x_126_, 1);
lean_inc_ref(v_arg_129_);
v___x_130_ = l_Lean_Expr_appFnCleanup___redArg(v___x_126_);
v___x_131_ = l_Lean_Expr_isApp(v___x_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; 
lean_dec_ref(v___x_130_);
lean_dec_ref(v_arg_129_);
lean_dec(v_ty_x3f_125_);
lean_dec_ref(v_lhsNew_124_);
v___x_132_ = lean_box(0);
return v___x_132_;
}
else
{
lean_object* v_arg_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v_arg_133_ = lean_ctor_get(v___x_130_, 1);
lean_inc_ref(v_arg_133_);
v___x_134_ = l_Lean_Expr_appFnCleanup___redArg(v___x_130_);
v___x_135_ = l_Lean_Expr_isApp(v___x_134_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; 
lean_dec_ref(v___x_134_);
lean_dec_ref(v_arg_133_);
lean_dec_ref(v_arg_129_);
lean_dec(v_ty_x3f_125_);
lean_dec_ref(v_lhsNew_124_);
v___x_136_ = lean_box(0);
return v___x_136_;
}
else
{
lean_object* v_arg_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v_arg_137_ = lean_ctor_get(v___x_134_, 1);
lean_inc_ref(v_arg_137_);
v___x_138_ = l_Lean_Expr_appFnCleanup___redArg(v___x_134_);
v___x_139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1));
v___x_140_ = l_Lean_Expr_isConstOf(v___x_138_, v___x_139_);
if (v___x_140_ == 0)
{
uint8_t v___x_141_; 
v___x_141_ = l_Lean_Expr_isApp(v___x_138_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; 
lean_dec_ref(v___x_138_);
lean_dec_ref(v_arg_137_);
lean_dec_ref(v_arg_133_);
lean_dec_ref(v_arg_129_);
lean_dec(v_ty_x3f_125_);
lean_dec_ref(v_lhsNew_124_);
v___x_142_ = lean_box(0);
return v___x_142_;
}
else
{
lean_object* v___x_143_; lean_object* v___y_145_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_143_ = l_Lean_Expr_appFnCleanup___redArg(v___x_138_);
v___x_148_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3));
v___x_149_ = l_Lean_Expr_isConstOf(v___x_143_, v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; 
lean_dec_ref(v___x_143_);
lean_dec_ref(v_arg_137_);
lean_dec_ref(v_arg_133_);
lean_dec_ref(v_arg_129_);
lean_dec(v_ty_x3f_125_);
lean_dec_ref(v_lhsNew_124_);
v___x_150_ = lean_box(0);
return v___x_150_;
}
else
{
uint8_t v___x_151_; 
v___x_151_ = l_Lean_Expr_hasLooseBVars(v_arg_137_);
lean_dec_ref(v_arg_137_);
if (v___x_151_ == 0)
{
if (lean_obj_tag(v_ty_x3f_125_) == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3);
v___x_153_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f_spec__0(v___x_152_);
v___y_145_ = v___x_153_;
goto v___jp_144_;
}
else
{
lean_object* v_val_154_; 
v_val_154_ = lean_ctor_get(v_ty_x3f_125_, 0);
lean_inc(v_val_154_);
lean_dec_ref_known(v_ty_x3f_125_, 1);
v___y_145_ = v_val_154_;
goto v___jp_144_;
}
}
else
{
lean_object* v___x_155_; 
lean_dec_ref(v___x_143_);
lean_dec_ref(v_arg_133_);
lean_dec_ref(v_arg_129_);
lean_dec(v_ty_x3f_125_);
lean_dec_ref(v_lhsNew_124_);
v___x_155_ = lean_box(0);
return v___x_155_;
}
}
v___jp_144_:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = l_Lean_mkApp4(v___x_143_, v___y_145_, v_lhsNew_124_, v_arg_133_, v_arg_129_);
v___x_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
}
else
{
uint8_t v___x_156_; 
lean_dec(v_ty_x3f_125_);
v___x_156_ = l_Lean_Expr_hasLooseBVars(v_arg_133_);
lean_dec_ref(v_arg_133_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = l_Lean_mkApp3(v___x_138_, v_arg_137_, v_lhsNew_124_, v_arg_129_);
v___x_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
return v___x_158_;
}
else
{
lean_object* v___x_159_; 
lean_dec_ref(v___x_138_);
lean_dec_ref(v_arg_137_);
lean_dec_ref(v_arg_129_);
lean_dec_ref(v_lhsNew_124_);
v___x_159_ = lean_box(0);
return v___x_159_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(lean_object* v_xs_160_, lean_object* v_tys_161_, lean_object* v_e_162_, lean_object* v_i_163_){
_start:
{
if (lean_obj_tag(v_e_162_) == 7)
{
lean_object* v_binderName_164_; lean_object* v_binderType_165_; lean_object* v_body_166_; uint8_t v_binderInfo_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v_binderName_164_ = lean_ctor_get(v_e_162_, 0);
v_binderType_165_ = lean_ctor_get(v_e_162_, 1);
v_body_166_ = lean_ctor_get(v_e_162_, 2);
v_binderInfo_167_ = lean_ctor_get_uint8(v_e_162_, sizeof(void*)*3 + 8);
v___x_168_ = lean_array_get_size(v_xs_160_);
v___x_169_ = lean_nat_dec_lt(v_i_163_, v___x_168_);
if (v___x_169_ == 0)
{
return v_e_162_;
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_170_ = lean_box(0);
v___x_171_ = lean_array_fget_borrowed(v_xs_160_, v_i_163_);
v___x_172_ = lean_array_get_borrowed(v___x_170_, v_tys_161_, v_i_163_);
lean_inc(v___x_172_);
lean_inc(v___x_171_);
lean_inc_ref(v_binderType_165_);
v___x_173_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f(v_binderType_165_, v___x_171_, v___x_172_);
if (lean_obj_tag(v___x_173_) == 1)
{
lean_object* v_val_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; size_t v___x_178_; size_t v___x_179_; uint8_t v___x_180_; 
v_val_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_val_174_);
lean_dec_ref_known(v___x_173_, 1);
v___x_175_ = lean_unsigned_to_nat(1u);
v___x_176_ = lean_nat_add(v_i_163_, v___x_175_);
lean_inc_ref(v_body_166_);
v___x_177_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_160_, v_tys_161_, v_body_166_, v___x_176_);
lean_dec(v___x_176_);
v___x_178_ = lean_ptr_addr(v_binderType_165_);
v___x_179_ = lean_ptr_addr(v_val_174_);
v___x_180_ = lean_usize_dec_eq(v___x_178_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; 
lean_inc(v_binderName_164_);
lean_dec_ref_known(v_e_162_, 3);
v___x_181_ = l_Lean_Expr_forallE___override(v_binderName_164_, v_val_174_, v___x_177_, v_binderInfo_167_);
return v___x_181_;
}
else
{
size_t v___x_182_; size_t v___x_183_; uint8_t v___x_184_; 
v___x_182_ = lean_ptr_addr(v_body_166_);
v___x_183_ = lean_ptr_addr(v___x_177_);
v___x_184_ = lean_usize_dec_eq(v___x_182_, v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; 
lean_inc(v_binderName_164_);
lean_dec_ref_known(v_e_162_, 3);
v___x_185_ = l_Lean_Expr_forallE___override(v_binderName_164_, v_val_174_, v___x_177_, v_binderInfo_167_);
return v___x_185_;
}
else
{
uint8_t v___x_186_; 
v___x_186_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_167_, v_binderInfo_167_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
lean_inc(v_binderName_164_);
lean_dec_ref_known(v_e_162_, 3);
v___x_187_ = l_Lean_Expr_forallE___override(v_binderName_164_, v_val_174_, v___x_177_, v_binderInfo_167_);
return v___x_187_;
}
else
{
lean_dec_ref(v___x_177_);
lean_dec(v_val_174_);
return v_e_162_;
}
}
}
}
else
{
lean_object* v___x_188_; size_t v___x_189_; uint8_t v___x_190_; 
lean_dec(v___x_173_);
lean_inc_ref(v_body_166_);
v___x_188_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_160_, v_tys_161_, v_body_166_, v_i_163_);
v___x_189_ = lean_ptr_addr(v_binderType_165_);
v___x_190_ = lean_usize_dec_eq(v___x_189_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; 
lean_inc_ref(v_binderType_165_);
lean_inc(v_binderName_164_);
lean_dec_ref_known(v_e_162_, 3);
v___x_191_ = l_Lean_Expr_forallE___override(v_binderName_164_, v_binderType_165_, v___x_188_, v_binderInfo_167_);
return v___x_191_;
}
else
{
size_t v___x_192_; size_t v___x_193_; uint8_t v___x_194_; 
v___x_192_ = lean_ptr_addr(v_body_166_);
v___x_193_ = lean_ptr_addr(v___x_188_);
v___x_194_ = lean_usize_dec_eq(v___x_192_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
lean_inc_ref(v_binderType_165_);
lean_inc(v_binderName_164_);
lean_dec_ref_known(v_e_162_, 3);
v___x_195_ = l_Lean_Expr_forallE___override(v_binderName_164_, v_binderType_165_, v___x_188_, v_binderInfo_167_);
return v___x_195_;
}
else
{
uint8_t v___x_196_; 
v___x_196_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_167_, v_binderInfo_167_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; 
lean_inc_ref(v_binderType_165_);
lean_inc(v_binderName_164_);
lean_dec_ref_known(v_e_162_, 3);
v___x_197_ = l_Lean_Expr_forallE___override(v_binderName_164_, v_binderType_165_, v___x_188_, v_binderInfo_167_);
return v___x_197_;
}
else
{
lean_dec_ref(v___x_188_);
return v_e_162_;
}
}
}
}
}
}
else
{
return v_e_162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss___boxed(lean_object* v_xs_198_, lean_object* v_tys_199_, lean_object* v_e_200_, lean_object* v_i_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_198_, v_tys_199_, v_e_200_, v_i_201_);
lean_dec(v_i_201_);
lean_dec_ref(v_tys_199_);
lean_dec_ref(v_xs_198_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0(lean_object* v_k_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v_b_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___x_216_; 
lean_inc(v___y_214_);
lean_inc_ref(v___y_213_);
lean_inc(v___y_212_);
lean_inc_ref(v___y_211_);
lean_inc(v___y_209_);
lean_inc_ref(v___y_208_);
lean_inc(v___y_207_);
lean_inc_ref(v___y_206_);
lean_inc(v___y_205_);
lean_inc(v___y_204_);
v___x_216_ = lean_apply_12(v_k_203_, v_b_210_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, lean_box(0));
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v_b_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0(v_k_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v_b_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec(v___y_218_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(lean_object* v_name_231_, uint8_t v_bi_232_, lean_object* v_type_233_, lean_object* v_k_234_, uint8_t v_kind_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___f_247_; lean_object* v___x_248_; 
lean_inc(v___y_241_);
lean_inc_ref(v___y_240_);
lean_inc(v___y_239_);
lean_inc_ref(v___y_238_);
lean_inc(v___y_237_);
lean_inc(v___y_236_);
v___f_247_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_247_, 0, v_k_234_);
lean_closure_set(v___f_247_, 1, v___y_236_);
lean_closure_set(v___f_247_, 2, v___y_237_);
lean_closure_set(v___f_247_, 3, v___y_238_);
lean_closure_set(v___f_247_, 4, v___y_239_);
lean_closure_set(v___f_247_, 5, v___y_240_);
lean_closure_set(v___f_247_, 6, v___y_241_);
v___x_248_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_231_, v_bi_232_, v_type_233_, v___f_247_, v_kind_235_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
if (lean_obj_tag(v___x_248_) == 0)
{
return v___x_248_;
}
else
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_248_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___boxed(lean_object* v_name_257_, lean_object* v_bi_258_, lean_object* v_type_259_, lean_object* v_k_260_, lean_object* v_kind_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
uint8_t v_bi_boxed_273_; uint8_t v_kind_boxed_274_; lean_object* v_res_275_; 
v_bi_boxed_273_ = lean_unbox(v_bi_258_);
v_kind_boxed_274_ = lean_unbox(v_kind_261_);
v_res_275_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_257_, v_bi_boxed_273_, v_type_259_, v_k_260_, v_kind_boxed_274_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec(v___y_262_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(lean_object* v_name_276_, lean_object* v_type_277_, lean_object* v_k_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
uint8_t v___x_290_; uint8_t v___x_291_; lean_object* v___x_292_; 
v___x_290_ = 0;
v___x_291_ = 0;
v___x_292_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_276_, v___x_290_, v_type_277_, v_k_278_, v___x_291_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg___boxed(lean_object* v_name_293_, lean_object* v_type_294_, lean_object* v_k_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v_name_293_, v_type_294_, v_k_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec(v___y_296_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed(lean_object** _args){
lean_object* v_i_311_ = _args[0];
lean_object* v_xs_312_ = _args[1];
lean_object* v_tys_313_ = _args[2];
lean_object* v_tysxs_314_ = _args[3];
lean_object* v_args_315_ = _args[4];
lean_object* v_val_316_ = _args[5];
lean_object* v_fst_317_ = _args[6];
lean_object* v_e_318_ = _args[7];
lean_object* v_lhss_u03b1s_319_ = _args[8];
lean_object* v_ty_320_ = _args[9];
lean_object* v___y_321_ = _args[10];
lean_object* v___y_322_ = _args[11];
lean_object* v___y_323_ = _args[12];
lean_object* v___y_324_ = _args[13];
lean_object* v___y_325_ = _args[14];
lean_object* v___y_326_ = _args[15];
lean_object* v___y_327_ = _args[16];
lean_object* v___y_328_ = _args[17];
lean_object* v___y_329_ = _args[18];
lean_object* v___y_330_ = _args[19];
lean_object* v___y_331_ = _args[20];
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(v_i_311_, v_xs_312_, v_tys_313_, v_tysxs_314_, v_args_315_, v_val_316_, v_fst_317_, v_e_318_, v_lhss_u03b1s_319_, v_ty_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec(v___y_321_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(lean_object* v_i_336_, lean_object* v_xs_337_, lean_object* v_tys_338_, lean_object* v_tysxs_339_, lean_object* v_args_340_, lean_object* v_fst_341_, lean_object* v_e_342_, lean_object* v_lhss_u03b1s_343_, lean_object* v_x_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_356_ = lean_unsigned_to_nat(1u);
v___x_357_ = lean_nat_add(v_i_336_, v___x_356_);
lean_inc_ref(v_x_344_);
v___x_358_ = lean_array_push(v_xs_337_, v_x_344_);
v___x_359_ = lean_box(0);
v___x_360_ = lean_array_push(v_tys_338_, v___x_359_);
v___x_361_ = lean_array_push(v_tysxs_339_, v_x_344_);
v___x_362_ = lean_array_push(v_args_340_, v_fst_341_);
v___x_363_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_342_, v_lhss_u03b1s_343_, v___x_357_, v___x_358_, v___x_360_, v___x_361_, v___x_362_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed(lean_object** _args){
lean_object* v_i_364_ = _args[0];
lean_object* v_xs_365_ = _args[1];
lean_object* v_tys_366_ = _args[2];
lean_object* v_tysxs_367_ = _args[3];
lean_object* v_args_368_ = _args[4];
lean_object* v_fst_369_ = _args[5];
lean_object* v_e_370_ = _args[6];
lean_object* v_lhss_u03b1s_371_ = _args[7];
lean_object* v_x_372_ = _args[8];
lean_object* v___y_373_ = _args[9];
lean_object* v___y_374_ = _args[10];
lean_object* v___y_375_ = _args[11];
lean_object* v___y_376_ = _args[12];
lean_object* v___y_377_ = _args[13];
lean_object* v___y_378_ = _args[14];
lean_object* v___y_379_ = _args[15];
lean_object* v___y_380_ = _args[16];
lean_object* v___y_381_ = _args[17];
lean_object* v___y_382_ = _args[18];
lean_object* v___y_383_ = _args[19];
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(v_i_364_, v_xs_365_, v_tys_366_, v_tysxs_367_, v_args_368_, v_fst_369_, v_e_370_, v_lhss_u03b1s_371_, v_x_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec(v___y_373_);
lean_dec(v_i_364_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(lean_object* v_e_385_, lean_object* v_lhss_u03b1s_386_, lean_object* v_i_387_, lean_object* v_xs_388_, lean_object* v_tys_389_, lean_object* v_tysxs_390_, lean_object* v_args_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = lean_array_get_size(v_lhss_u03b1s_386_);
v___x_404_ = lean_nat_dec_lt(v_i_387_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; lean_object* v_eAbst_406_; uint8_t v___x_407_; uint8_t v___x_408_; lean_object* v___x_409_; 
lean_dec(v_i_387_);
lean_dec_ref(v_lhss_u03b1s_386_);
v___x_405_ = lean_unsigned_to_nat(0u);
v_eAbst_406_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_388_, v_tys_389_, v_e_385_, v___x_405_);
lean_dec_ref(v_tys_389_);
lean_dec_ref(v_xs_388_);
v___x_407_ = 1;
v___x_408_ = 1;
v___x_409_ = l_Lean_Meta_mkLambdaFVars(v_tysxs_390_, v_eAbst_406_, v___x_404_, v___x_407_, v___x_404_, v___x_407_, v___x_408_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
lean_dec_ref(v_tysxs_390_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
lean_dec_ref_known(v___x_409_, 1);
v___x_411_ = l_Lean_mkAppN(v_a_410_, v_args_391_);
v___x_412_ = l_Lean_Meta_Sym_shareCommon(v___x_411_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_421_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_421_ == 0)
{
v___x_415_ = v___x_412_;
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v_args_391_);
lean_ctor_set(v___x_417_, 1, v_a_413_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 0, v___x_417_);
v___x_419_ = v___x_415_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec_ref(v_args_391_);
v_a_422_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_412_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_412_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec_ref(v_args_391_);
v_a_430_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_409_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_409_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
else
{
lean_object* v___x_438_; lean_object* v_snd_439_; 
v___x_438_ = lean_array_fget_borrowed(v_lhss_u03b1s_386_, v_i_387_);
v_snd_439_ = lean_ctor_get(v___x_438_, 1);
if (lean_obj_tag(v_snd_439_) == 1)
{
lean_object* v_fst_440_; lean_object* v_val_441_; lean_object* v___f_442_; lean_object* v___x_443_; 
v_fst_440_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_fst_440_);
v_val_441_ = lean_ctor_get(v_snd_439_, 0);
lean_inc_n(v_val_441_, 2);
lean_inc(v_i_387_);
v___f_442_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed), 21, 9);
lean_closure_set(v___f_442_, 0, v_i_387_);
lean_closure_set(v___f_442_, 1, v_xs_388_);
lean_closure_set(v___f_442_, 2, v_tys_389_);
lean_closure_set(v___f_442_, 3, v_tysxs_390_);
lean_closure_set(v___f_442_, 4, v_args_391_);
lean_closure_set(v___f_442_, 5, v_val_441_);
lean_closure_set(v___f_442_, 6, v_fst_440_);
lean_closure_set(v___f_442_, 7, v_e_385_);
lean_closure_set(v___f_442_, 8, v_lhss_u03b1s_386_);
lean_inc(v_a_401_);
lean_inc_ref(v_a_400_);
lean_inc(v_a_399_);
lean_inc_ref(v_a_398_);
v___x_443_ = lean_infer_type(v_val_441_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref_known(v___x_443_, 1);
v___x_445_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__1));
v___x_446_ = lean_name_append_index_after(v___x_445_, v_i_387_);
v___x_447_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v___x_446_, v_a_444_, v___f_442_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
return v___x_447_;
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_dec_ref(v___f_442_);
lean_dec(v_i_387_);
v_a_448_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_443_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_443_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
else
{
lean_object* v_fst_456_; lean_object* v___f_457_; lean_object* v___x_458_; 
v_fst_456_ = lean_ctor_get(v___x_438_, 0);
lean_inc_n(v_fst_456_, 2);
lean_inc(v_i_387_);
v___f_457_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed), 20, 8);
lean_closure_set(v___f_457_, 0, v_i_387_);
lean_closure_set(v___f_457_, 1, v_xs_388_);
lean_closure_set(v___f_457_, 2, v_tys_389_);
lean_closure_set(v___f_457_, 3, v_tysxs_390_);
lean_closure_set(v___f_457_, 4, v_args_391_);
lean_closure_set(v___f_457_, 5, v_fst_456_);
lean_closure_set(v___f_457_, 6, v_e_385_);
lean_closure_set(v___f_457_, 7, v_lhss_u03b1s_386_);
lean_inc(v_a_401_);
lean_inc_ref(v_a_400_);
lean_inc(v_a_399_);
lean_inc_ref(v_a_398_);
v___x_458_ = lean_infer_type(v_fst_456_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_458_, 1);
v___x_460_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1));
v___x_461_ = lean_name_append_index_after(v___x_460_, v_i_387_);
v___x_462_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v___x_461_, v_a_459_, v___f_457_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
return v___x_462_;
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec_ref(v___f_457_);
lean_dec(v_i_387_);
v_a_463_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_458_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_458_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(lean_object* v_i_471_, lean_object* v_xs_472_, lean_object* v_ty_473_, lean_object* v_tys_474_, lean_object* v_tysxs_475_, lean_object* v_args_476_, lean_object* v_val_477_, lean_object* v_fst_478_, lean_object* v_e_479_, lean_object* v_lhss_u03b1s_480_, lean_object* v_x_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_493_ = lean_unsigned_to_nat(1u);
v___x_494_ = lean_nat_add(v_i_471_, v___x_493_);
lean_inc_ref(v_x_481_);
v___x_495_ = lean_array_push(v_xs_472_, v_x_481_);
lean_inc_ref(v_ty_473_);
v___x_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_496_, 0, v_ty_473_);
v___x_497_ = lean_array_push(v_tys_474_, v___x_496_);
v___x_498_ = lean_array_push(v_tysxs_475_, v_ty_473_);
v___x_499_ = lean_array_push(v___x_498_, v_x_481_);
v___x_500_ = lean_array_push(v_args_476_, v_val_477_);
v___x_501_ = lean_array_push(v___x_500_, v_fst_478_);
v___x_502_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_479_, v_lhss_u03b1s_480_, v___x_494_, v___x_495_, v___x_497_, v___x_499_, v___x_501_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0___boxed(lean_object** _args){
lean_object* v_i_503_ = _args[0];
lean_object* v_xs_504_ = _args[1];
lean_object* v_ty_505_ = _args[2];
lean_object* v_tys_506_ = _args[3];
lean_object* v_tysxs_507_ = _args[4];
lean_object* v_args_508_ = _args[5];
lean_object* v_val_509_ = _args[6];
lean_object* v_fst_510_ = _args[7];
lean_object* v_e_511_ = _args[8];
lean_object* v_lhss_u03b1s_512_ = _args[9];
lean_object* v_x_513_ = _args[10];
lean_object* v___y_514_ = _args[11];
lean_object* v___y_515_ = _args[12];
lean_object* v___y_516_ = _args[13];
lean_object* v___y_517_ = _args[14];
lean_object* v___y_518_ = _args[15];
lean_object* v___y_519_ = _args[16];
lean_object* v___y_520_ = _args[17];
lean_object* v___y_521_ = _args[18];
lean_object* v___y_522_ = _args[19];
lean_object* v___y_523_ = _args[20];
lean_object* v___y_524_ = _args[21];
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(v_i_503_, v_xs_504_, v_ty_505_, v_tys_506_, v_tysxs_507_, v_args_508_, v_val_509_, v_fst_510_, v_e_511_, v_lhss_u03b1s_512_, v_x_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec(v___y_514_);
lean_dec(v_i_503_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(lean_object* v_i_526_, lean_object* v_xs_527_, lean_object* v_tys_528_, lean_object* v_tysxs_529_, lean_object* v_args_530_, lean_object* v_val_531_, lean_object* v_fst_532_, lean_object* v_e_533_, lean_object* v_lhss_u03b1s_534_, lean_object* v_ty_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v___f_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
lean_inc_ref(v_ty_535_);
lean_inc(v_i_526_);
v___f_547_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0___boxed), 22, 10);
lean_closure_set(v___f_547_, 0, v_i_526_);
lean_closure_set(v___f_547_, 1, v_xs_527_);
lean_closure_set(v___f_547_, 2, v_ty_535_);
lean_closure_set(v___f_547_, 3, v_tys_528_);
lean_closure_set(v___f_547_, 4, v_tysxs_529_);
lean_closure_set(v___f_547_, 5, v_args_530_);
lean_closure_set(v___f_547_, 6, v_val_531_);
lean_closure_set(v___f_547_, 7, v_fst_532_);
lean_closure_set(v___f_547_, 8, v_e_533_);
lean_closure_set(v___f_547_, 9, v_lhss_u03b1s_534_);
v___x_548_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1));
v___x_549_ = lean_name_append_index_after(v___x_548_, v_i_526_);
v___x_550_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v___x_549_, v_ty_535_, v___f_547_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___boxed(lean_object** _args){
lean_object* v_e_551_ = _args[0];
lean_object* v_lhss_u03b1s_552_ = _args[1];
lean_object* v_i_553_ = _args[2];
lean_object* v_xs_554_ = _args[3];
lean_object* v_tys_555_ = _args[4];
lean_object* v_tysxs_556_ = _args[5];
lean_object* v_args_557_ = _args[6];
lean_object* v_a_558_ = _args[7];
lean_object* v_a_559_ = _args[8];
lean_object* v_a_560_ = _args[9];
lean_object* v_a_561_ = _args[10];
lean_object* v_a_562_ = _args[11];
lean_object* v_a_563_ = _args[12];
lean_object* v_a_564_ = _args[13];
lean_object* v_a_565_ = _args[14];
lean_object* v_a_566_ = _args[15];
lean_object* v_a_567_ = _args[16];
lean_object* v_a_568_ = _args[17];
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_551_, v_lhss_u03b1s_552_, v_i_553_, v_xs_554_, v_tys_555_, v_tysxs_556_, v_args_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec(v_a_558_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0(lean_object* v_00_u03b1_570_, lean_object* v_name_571_, uint8_t v_bi_572_, lean_object* v_type_573_, lean_object* v_k_574_, uint8_t v_kind_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_571_, v_bi_572_, v_type_573_, v_k_574_, v_kind_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_588_ = _args[0];
lean_object* v_name_589_ = _args[1];
lean_object* v_bi_590_ = _args[2];
lean_object* v_type_591_ = _args[3];
lean_object* v_k_592_ = _args[4];
lean_object* v_kind_593_ = _args[5];
lean_object* v___y_594_ = _args[6];
lean_object* v___y_595_ = _args[7];
lean_object* v___y_596_ = _args[8];
lean_object* v___y_597_ = _args[9];
lean_object* v___y_598_ = _args[10];
lean_object* v___y_599_ = _args[11];
lean_object* v___y_600_ = _args[12];
lean_object* v___y_601_ = _args[13];
lean_object* v___y_602_ = _args[14];
lean_object* v___y_603_ = _args[15];
lean_object* v___y_604_ = _args[16];
_start:
{
uint8_t v_bi_boxed_605_; uint8_t v_kind_boxed_606_; lean_object* v_res_607_; 
v_bi_boxed_605_ = lean_unbox(v_bi_590_);
v_kind_boxed_606_ = lean_unbox(v_kind_593_);
v_res_607_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0(v_00_u03b1_588_, v_name_589_, v_bi_boxed_605_, v_type_591_, v_k_592_, v_kind_boxed_606_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec(v___y_594_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0(lean_object* v_00_u03b1_608_, lean_object* v_name_609_, lean_object* v_type_610_, lean_object* v_k_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v_name_609_, v_type_610_, v_k_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___boxed(lean_object* v_00_u03b1_624_, lean_object* v_name_625_, lean_object* v_type_626_, lean_object* v_k_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0(v_00_u03b1_624_, v_name_625_, v_type_626_, v_k_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
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
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter___redArg(lean_object* v_x_640_, lean_object* v_h__1_641_){
_start:
{
lean_object* v_fst_642_; lean_object* v_snd_643_; lean_object* v___x_644_; 
v_fst_642_ = lean_ctor_get(v_x_640_, 0);
lean_inc(v_fst_642_);
v_snd_643_ = lean_ctor_get(v_x_640_, 1);
lean_inc(v_snd_643_);
lean_dec_ref(v_x_640_);
v___x_644_ = lean_apply_2(v_h__1_641_, v_fst_642_, v_snd_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter(lean_object* v_motive_645_, lean_object* v_x_646_, lean_object* v_h__1_647_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter___redArg(lean_object* v_00_u03b1_x3f_651_, lean_object* v_h__1_652_, lean_object* v_h__2_653_){
_start:
{
if (lean_obj_tag(v_00_u03b1_x3f_651_) == 1)
{
lean_object* v_val_654_; lean_object* v___x_655_; 
lean_dec(v_h__2_653_);
v_val_654_ = lean_ctor_get(v_00_u03b1_x3f_651_, 0);
lean_inc(v_val_654_);
lean_dec_ref_known(v_00_u03b1_x3f_651_, 1);
v___x_655_ = lean_apply_1(v_h__1_652_, v_val_654_);
return v___x_655_;
}
else
{
lean_object* v___x_656_; 
lean_dec(v_h__1_652_);
v___x_656_ = lean_apply_2(v_h__2_653_, v_00_u03b1_x3f_651_, lean_box(0));
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter(lean_object* v_motive_657_, lean_object* v_00_u03b1_x3f_658_, lean_object* v_h__1_659_, lean_object* v_h__2_660_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(lean_object* v_matchCond_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v___x_689_; uint8_t v___x_690_; 
lean_inc_ref(v_matchCond_673_);
v___x_689_ = l_Lean_Expr_cleanupAnnotations(v_matchCond_673_);
v___x_690_ = l_Lean_Expr_isApp(v___x_689_);
if (v___x_690_ == 0)
{
lean_dec_ref(v___x_689_);
goto v___jp_685_;
}
else
{
lean_object* v_arg_691_; lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v_arg_691_ = lean_ctor_get(v___x_689_, 1);
lean_inc_ref(v_arg_691_);
v___x_692_ = l_Lean_Expr_appFnCleanup___redArg(v___x_689_);
v___x_693_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_694_ = l_Lean_Expr_isConstOf(v___x_692_, v___x_693_);
lean_dec_ref(v___x_692_);
if (v___x_694_ == 0)
{
lean_dec_ref(v_arg_691_);
goto v___jp_685_;
}
else
{
lean_object* v_lhss_u03b1s_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
lean_dec_ref(v_matchCond_673_);
lean_inc_ref(v_arg_691_);
v_lhss_u03b1s_695_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss(v_arg_691_);
v___x_696_ = lean_unsigned_to_nat(0u);
v___x_697_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0));
v___x_698_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_arg_691_, v_lhss_u03b1s_695_, v___x_696_, v___x_697_, v___x_697_, v___x_697_, v___x_697_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
return v___x_698_;
}
}
v___jp_685_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_686_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0));
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v_matchCond_673_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___boxed(lean_object* v_matchCond_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(v_matchCond_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
lean_dec(v_a_701_);
lean_dec(v_a_700_);
return v_res_711_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0(void){
_start:
{
lean_object* v___x_715_; lean_object* v_dummy_716_; 
v___x_715_ = lean_box(0);
v_dummy_716_ = l_Lean_Expr_sort___override(v___x_715_);
return v_dummy_716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(lean_object* v_lhs_717_, lean_object* v_rhs_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
uint8_t v___x_730_; 
v___x_730_ = l_Lean_Expr_hasLooseBVars(v_lhs_717_);
if (v___x_730_ == 0)
{
uint8_t v___x_731_; lean_object* v___x_732_; 
v___x_731_ = 1;
v___x_732_ = l_Lean_Meta_Grind_getRootENode___redArg(v_lhs_717_, v_a_719_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_873_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_873_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_873_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_873_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
uint8_t v_ctor_737_; 
v_ctor_737_ = lean_ctor_get_uint8(v_a_733_, sizeof(void*)*12 + 2);
if (v_ctor_737_ == 0)
{
uint8_t v_interpreted_738_; 
v_interpreted_738_ = lean_ctor_get_uint8(v_a_733_, sizeof(void*)*12 + 1);
if (v_interpreted_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_741_; 
lean_dec(v_a_733_);
lean_dec_ref(v_rhs_718_);
v___x_739_ = lean_box(v_interpreted_738_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_739_);
v___x_741_ = v___x_735_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
else
{
lean_object* v_self_743_; uint8_t v___x_744_; 
v_self_743_ = lean_ctor_get(v_a_733_, 0);
lean_inc_ref(v_self_743_);
lean_dec(v_a_733_);
v___x_744_ = l_Lean_Expr_hasLooseBVars(v_rhs_718_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; 
lean_del_object(v___x_735_);
lean_inc_ref(v_rhs_718_);
v___x_745_ = l_Lean_Meta_isLitValue(v_rhs_718_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; uint8_t v___x_747_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_746_);
v___x_747_ = lean_unbox(v_a_746_);
if (v___x_747_ == 0)
{
lean_dec(v_a_746_);
lean_dec_ref(v_self_743_);
lean_dec_ref(v_rhs_718_);
return v___x_745_;
}
else
{
lean_object* v___x_748_; 
lean_dec_ref_known(v___x_745_, 1);
v___x_748_ = l_Lean_Meta_normLitValue(v_self_743_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_750_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_748_, 1);
v___x_750_ = l_Lean_Meta_normLitValue(v_rhs_718_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_763_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_763_ == 0)
{
v___x_753_ = v___x_750_;
v_isShared_754_ = v_isSharedCheck_763_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_763_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
uint8_t v___x_755_; 
v___x_755_ = lean_expr_eqv(v_a_749_, v_a_751_);
lean_dec(v_a_751_);
lean_dec(v_a_749_);
if (v___x_755_ == 0)
{
lean_object* v___x_757_; 
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v_a_746_);
v___x_757_ = v___x_753_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_746_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
else
{
lean_object* v___x_759_; lean_object* v___x_761_; 
lean_dec(v_a_746_);
v___x_759_ = lean_box(v___x_744_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_759_);
v___x_761_ = v___x_753_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec(v_a_749_);
lean_dec(v_a_746_);
v_a_764_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_750_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_750_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec(v_a_746_);
lean_dec_ref(v_rhs_718_);
v_a_772_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_748_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_748_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
else
{
lean_dec_ref(v_self_743_);
lean_dec_ref(v_rhs_718_);
return v___x_745_;
}
}
else
{
lean_object* v___x_780_; lean_object* v___x_782_; 
lean_dec_ref(v_self_743_);
lean_dec_ref(v_rhs_718_);
v___x_780_ = lean_box(v_ctor_737_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_780_);
v___x_782_ = v___x_735_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_object* v_self_784_; lean_object* v___x_785_; 
lean_del_object(v___x_735_);
v_self_784_ = lean_ctor_get(v_a_733_, 0);
lean_inc_ref_n(v_self_784_, 2);
lean_dec(v_a_733_);
v___x_785_ = l_Lean_Meta_isConstructorApp_x3f(v_self_784_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_864_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_864_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_864_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_864_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
if (lean_obj_tag(v_a_786_) == 1)
{
lean_object* v_val_790_; lean_object* v___x_791_; 
lean_del_object(v___x_788_);
v_val_790_ = lean_ctor_get(v_a_786_, 0);
lean_inc(v_val_790_);
lean_dec_ref_known(v_a_786_, 1);
lean_inc_ref(v_rhs_718_);
v___x_791_ = l_Lean_Meta_isConstructorApp_x3f(v_rhs_718_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_851_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_851_ == 0)
{
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_851_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_851_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
if (lean_obj_tag(v_a_792_) == 1)
{
lean_object* v_toConstantVal_796_; lean_object* v_val_797_; lean_object* v_toConstantVal_798_; lean_object* v_numParams_799_; lean_object* v_numFields_800_; lean_object* v_name_801_; lean_object* v_name_802_; uint8_t v___x_803_; 
v_toConstantVal_796_ = lean_ctor_get(v_val_790_, 0);
lean_inc_ref(v_toConstantVal_796_);
v_val_797_ = lean_ctor_get(v_a_792_, 0);
lean_inc(v_val_797_);
lean_dec_ref_known(v_a_792_, 1);
v_toConstantVal_798_ = lean_ctor_get(v_val_797_, 0);
lean_inc_ref(v_toConstantVal_798_);
lean_dec(v_val_797_);
v_numParams_799_ = lean_ctor_get(v_val_790_, 3);
lean_inc(v_numParams_799_);
v_numFields_800_ = lean_ctor_get(v_val_790_, 4);
lean_inc(v_numFields_800_);
lean_dec(v_val_790_);
v_name_801_ = lean_ctor_get(v_toConstantVal_796_, 0);
lean_inc(v_name_801_);
lean_dec_ref(v_toConstantVal_796_);
v_name_802_ = lean_ctor_get(v_toConstantVal_798_, 0);
lean_inc(v_name_802_);
lean_dec_ref(v_toConstantVal_798_);
v___x_803_ = lean_name_eq(v_name_801_, v_name_802_);
lean_dec(v_name_802_);
lean_dec(v_name_801_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_806_; 
lean_dec(v_numFields_800_);
lean_dec(v_numParams_799_);
lean_dec_ref(v_self_784_);
lean_dec_ref(v_rhs_718_);
v___x_804_ = lean_box(v___x_731_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_804_);
v___x_806_ = v___x_794_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
else
{
if (v___x_730_ == 0)
{
lean_object* v_nargs_808_; lean_object* v_nargs_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v_dummy_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
lean_del_object(v___x_794_);
v_nargs_808_ = l_Lean_Expr_getAppNumArgs(v_self_784_);
v_nargs_809_ = l_Lean_Expr_getAppNumArgs(v_rhs_718_);
v___x_810_ = lean_nat_add(v_numParams_799_, v_numFields_800_);
lean_dec(v_numFields_800_);
v___x_811_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0));
v_dummy_812_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0);
lean_inc(v_nargs_808_);
v___x_813_ = lean_mk_array(v_nargs_808_, v_dummy_812_);
v___x_814_ = lean_unsigned_to_nat(1u);
v___x_815_ = lean_nat_sub(v_nargs_808_, v___x_814_);
lean_dec(v_nargs_808_);
v___x_816_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_784_, v___x_813_, v___x_815_);
lean_inc(v_nargs_809_);
v___x_817_ = lean_mk_array(v_nargs_809_, v_dummy_812_);
v___x_818_ = lean_nat_sub(v_nargs_809_, v___x_814_);
lean_dec(v_nargs_809_);
v___x_819_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_rhs_718_, v___x_817_, v___x_818_);
v___x_820_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v___x_810_, v___x_816_, v___x_819_, v_numParams_799_, v___x_811_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
lean_dec_ref(v___x_819_);
lean_dec_ref(v___x_816_);
lean_dec(v___x_810_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_834_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_834_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_834_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_834_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v_fst_825_; 
v_fst_825_ = lean_ctor_get(v_a_821_, 0);
lean_inc(v_fst_825_);
lean_dec(v_a_821_);
if (lean_obj_tag(v_fst_825_) == 0)
{
lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_826_ = lean_box(v___x_730_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_826_);
v___x_828_ = v___x_823_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
else
{
lean_object* v_val_830_; lean_object* v___x_832_; 
v_val_830_ = lean_ctor_get(v_fst_825_, 0);
lean_inc(v_val_830_);
lean_dec_ref_known(v_fst_825_, 1);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v_val_830_);
v___x_832_ = v___x_823_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_val_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
v_a_835_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_820_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_820_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
else
{
lean_object* v___x_843_; lean_object* v___x_845_; 
lean_dec(v_numFields_800_);
lean_dec(v_numParams_799_);
lean_dec_ref(v_self_784_);
lean_dec_ref(v_rhs_718_);
v___x_843_ = lean_box(v___x_731_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_843_);
v___x_845_ = v___x_794_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
else
{
lean_object* v___x_847_; lean_object* v___x_849_; 
lean_dec(v_a_792_);
lean_dec(v_val_790_);
lean_dec_ref(v_self_784_);
lean_dec_ref(v_rhs_718_);
v___x_847_ = lean_box(v___x_730_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_847_);
v___x_849_ = v___x_794_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec(v_val_790_);
lean_dec_ref(v_self_784_);
lean_dec_ref(v_rhs_718_);
v_a_852_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_791_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_791_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
else
{
lean_object* v___x_860_; lean_object* v___x_862_; 
lean_dec(v_a_786_);
lean_dec_ref(v_self_784_);
lean_dec_ref(v_rhs_718_);
v___x_860_ = lean_box(v___x_730_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_860_);
v___x_862_ = v___x_788_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec_ref(v_self_784_);
lean_dec_ref(v_rhs_718_);
v_a_865_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_785_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_785_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec_ref(v_rhs_718_);
v_a_874_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_732_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_732_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
else
{
uint8_t v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
lean_dec_ref(v_rhs_718_);
lean_dec_ref(v_lhs_717_);
v___x_882_ = 0;
v___x_883_ = lean_box(v___x_882_);
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
return v___x_884_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(lean_object* v_upperBound_885_, lean_object* v___x_886_, lean_object* v___x_887_, lean_object* v_a_888_, lean_object* v_b_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
uint8_t v___x_901_; 
v___x_901_ = lean_nat_dec_lt(v_a_888_, v_upperBound_885_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; 
lean_dec(v_a_888_);
v___x_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_902_, 0, v_b_889_);
return v___x_902_;
}
else
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
lean_dec_ref(v_b_889_);
v___x_903_ = l_Lean_instInhabitedExpr;
v___x_904_ = lean_box(0);
v___x_905_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0));
v___x_906_ = lean_array_get_borrowed(v___x_903_, v___x_886_, v_a_888_);
v___x_907_ = lean_array_get_borrowed(v___x_903_, v___x_887_, v_a_888_);
lean_inc(v___x_907_);
lean_inc(v___x_906_);
v___x_908_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v___x_906_, v___x_907_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_923_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_923_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_923_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_923_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
uint8_t v___x_913_; 
v___x_913_ = lean_unbox(v_a_909_);
lean_dec(v_a_909_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; lean_object* v___x_915_; 
lean_del_object(v___x_911_);
v___x_914_ = lean_unsigned_to_nat(1u);
v___x_915_ = lean_nat_add(v_a_888_, v___x_914_);
lean_dec(v_a_888_);
v_a_888_ = v___x_915_;
v_b_889_ = v___x_905_;
goto _start;
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
lean_dec(v_a_888_);
v___x_917_ = lean_box(v___x_901_);
v___x_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
lean_ctor_set(v___x_919_, 1, v___x_904_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_919_);
v___x_921_ = v___x_911_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v_a_888_);
v_a_924_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_908_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_908_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___boxed(lean_object* v_upperBound_932_, lean_object* v___x_933_, lean_object* v___x_934_, lean_object* v_a_935_, lean_object* v_b_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v_upperBound_932_, v___x_933_, v___x_934_, v_a_935_, v_b_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___x_934_);
lean_dec_ref(v___x_933_);
lean_dec(v_upperBound_932_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___boxed(lean_object* v_lhs_949_, lean_object* v_rhs_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v_lhs_949_, v_rhs_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec(v_a_951_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(lean_object* v_upperBound_963_, lean_object* v___x_964_, lean_object* v___x_965_, lean_object* v_inst_966_, lean_object* v_R_967_, lean_object* v_a_968_, lean_object* v_b_969_, lean_object* v_c_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v_upperBound_963_, v___x_964_, v___x_965_, v_a_968_, v_b_969_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_983_ = _args[0];
lean_object* v___x_984_ = _args[1];
lean_object* v___x_985_ = _args[2];
lean_object* v_inst_986_ = _args[3];
lean_object* v_R_987_ = _args[4];
lean_object* v_a_988_ = _args[5];
lean_object* v_b_989_ = _args[6];
lean_object* v_c_990_ = _args[7];
lean_object* v___y_991_ = _args[8];
lean_object* v___y_992_ = _args[9];
lean_object* v___y_993_ = _args[10];
lean_object* v___y_994_ = _args[11];
lean_object* v___y_995_ = _args[12];
lean_object* v___y_996_ = _args[13];
lean_object* v___y_997_ = _args[14];
lean_object* v___y_998_ = _args[15];
lean_object* v___y_999_ = _args[16];
lean_object* v___y_1000_ = _args[17];
lean_object* v___y_1001_ = _args[18];
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(v_upperBound_983_, v___x_984_, v___x_985_, v_inst_986_, v_R_987_, v_a_988_, v_b_989_, v_c_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___x_985_);
lean_dec_ref(v___x_984_);
lean_dec(v_upperBound_983_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(lean_object* v_e_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_e_1003_);
if (lean_obj_tag(v___x_1015_) == 1)
{
lean_object* v_val_1016_; lean_object* v_snd_1017_; lean_object* v_fst_1018_; lean_object* v_snd_1019_; lean_object* v___x_1020_; 
v_val_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_val_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v_snd_1017_ = lean_ctor_get(v_val_1016_, 1);
lean_inc(v_snd_1017_);
lean_dec(v_val_1016_);
v_fst_1018_ = lean_ctor_get(v_snd_1017_, 0);
lean_inc(v_fst_1018_);
v_snd_1019_ = lean_ctor_get(v_snd_1017_, 1);
lean_inc(v_snd_1019_);
lean_dec(v_snd_1017_);
v___x_1020_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v_fst_1018_, v_snd_1019_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
return v___x_1020_;
}
else
{
uint8_t v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
lean_dec(v___x_1015_);
v___x_1021_ = 0;
v___x_1022_ = lean_box(v___x_1021_);
v___x_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
return v___x_1023_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp___boxed(lean_object* v_e_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_e_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
lean_dec(v_a_1026_);
lean_dec(v_a_1025_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(uint8_t v___x_1037_, lean_object* v_snd_1038_, lean_object* v_____r_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1051_ = lean_box(v___x_1037_);
v___x_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v_snd_1038_);
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0___boxed(lean_object* v___x_1056_, lean_object* v_snd_1057_, lean_object* v_____r_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
uint8_t v___x_23311__boxed_1070_; lean_object* v_res_1071_; 
v___x_23311__boxed_1070_ = lean_unbox(v___x_1056_);
v_res_1071_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_23311__boxed_1070_, v_snd_1057_, v_____r_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec(v___y_1059_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(lean_object* v_msgData_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v___x_1078_; lean_object* v_env_1079_; lean_object* v___x_1080_; lean_object* v_toCold_1081_; lean_object* v_mctx_1082_; lean_object* v_lctx_1083_; lean_object* v_options_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1078_ = lean_st_ref_get(v___y_1076_);
v_env_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc_ref(v_env_1079_);
lean_dec(v___x_1078_);
v___x_1080_ = lean_st_ref_get(v___y_1074_);
v_toCold_1081_ = lean_ctor_get(v___y_1075_, 0);
v_mctx_1082_ = lean_ctor_get(v___x_1080_, 0);
lean_inc_ref(v_mctx_1082_);
lean_dec(v___x_1080_);
v_lctx_1083_ = lean_ctor_get(v___y_1073_, 2);
v_options_1084_ = lean_ctor_get(v_toCold_1081_, 2);
lean_inc_ref(v_options_1084_);
lean_inc_ref(v_lctx_1083_);
v___x_1085_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1085_, 0, v_env_1079_);
lean_ctor_set(v___x_1085_, 1, v_mctx_1082_);
lean_ctor_set(v___x_1085_, 2, v_lctx_1083_);
lean_ctor_set(v___x_1085_, 3, v_options_1084_);
v___x_1086_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
lean_ctor_set(v___x_1086_, 1, v_msgData_1072_);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0___boxed(lean_object* v_msgData_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(v_msgData_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
return v_res_1094_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1095_; double v___x_1096_; 
v___x_1095_ = lean_unsigned_to_nat(0u);
v___x_1096_ = lean_float_of_nat(v___x_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(lean_object* v_cls_1100_, lean_object* v_msg_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_ref_1107_; lean_object* v___x_1108_; lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1153_; 
v_ref_1107_ = lean_ctor_get(v___y_1104_, 2);
v___x_1108_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(v_msg_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1153_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1153_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v_traceState_1114_; lean_object* v_env_1115_; lean_object* v_nextMacroScope_1116_; lean_object* v_ngen_1117_; lean_object* v_auxDeclNGen_1118_; lean_object* v_cache_1119_; lean_object* v_messages_1120_; lean_object* v_infoState_1121_; lean_object* v_snapshotTasks_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1152_; 
v___x_1113_ = lean_st_ref_take(v___y_1105_);
v_traceState_1114_ = lean_ctor_get(v___x_1113_, 4);
v_env_1115_ = lean_ctor_get(v___x_1113_, 0);
v_nextMacroScope_1116_ = lean_ctor_get(v___x_1113_, 1);
v_ngen_1117_ = lean_ctor_get(v___x_1113_, 2);
v_auxDeclNGen_1118_ = lean_ctor_get(v___x_1113_, 3);
v_cache_1119_ = lean_ctor_get(v___x_1113_, 5);
v_messages_1120_ = lean_ctor_get(v___x_1113_, 6);
v_infoState_1121_ = lean_ctor_get(v___x_1113_, 7);
v_snapshotTasks_1122_ = lean_ctor_get(v___x_1113_, 8);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1124_ = v___x_1113_;
v_isShared_1125_ = v_isSharedCheck_1152_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_snapshotTasks_1122_);
lean_inc(v_infoState_1121_);
lean_inc(v_messages_1120_);
lean_inc(v_cache_1119_);
lean_inc(v_traceState_1114_);
lean_inc(v_auxDeclNGen_1118_);
lean_inc(v_ngen_1117_);
lean_inc(v_nextMacroScope_1116_);
lean_inc(v_env_1115_);
lean_dec(v___x_1113_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1152_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
uint64_t v_tid_1126_; lean_object* v_traces_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1151_; 
v_tid_1126_ = lean_ctor_get_uint64(v_traceState_1114_, sizeof(void*)*1);
v_traces_1127_ = lean_ctor_get(v_traceState_1114_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_traceState_1114_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1129_ = v_traceState_1114_;
v_isShared_1130_ = v_isSharedCheck_1151_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_traces_1127_);
lean_dec(v_traceState_1114_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1151_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; double v___x_1133_; uint8_t v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1131_ = lean_box(0);
v___x_1132_ = lean_box(0);
v___x_1133_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0);
v___x_1134_ = 0;
v___x_1135_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1));
v___x_1136_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1136_, 0, v_cls_1100_);
lean_ctor_set(v___x_1136_, 1, v___x_1132_);
lean_ctor_set(v___x_1136_, 2, v___x_1135_);
lean_ctor_set_float(v___x_1136_, sizeof(void*)*3, v___x_1133_);
lean_ctor_set_float(v___x_1136_, sizeof(void*)*3 + 8, v___x_1133_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*3 + 16, v___x_1134_);
v___x_1137_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__2));
v___x_1138_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1136_);
lean_ctor_set(v___x_1138_, 1, v_a_1109_);
lean_ctor_set(v___x_1138_, 2, v___x_1137_);
lean_inc(v_ref_1107_);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_ref_1107_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = l_Lean_PersistentArray_push___redArg(v_traces_1127_, v___x_1139_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1140_);
v___x_1142_ = v___x_1129_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1140_);
lean_ctor_set_uint64(v_reuseFailAlloc_1150_, sizeof(void*)*1, v_tid_1126_);
v___x_1142_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1144_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 4, v___x_1142_);
v___x_1144_ = v___x_1124_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_env_1115_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_nextMacroScope_1116_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_ngen_1117_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_auxDeclNGen_1118_);
lean_ctor_set(v_reuseFailAlloc_1149_, 4, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1149_, 5, v_cache_1119_);
lean_ctor_set(v_reuseFailAlloc_1149_, 6, v_messages_1120_);
lean_ctor_set(v_reuseFailAlloc_1149_, 7, v_infoState_1121_);
lean_ctor_set(v_reuseFailAlloc_1149_, 8, v_snapshotTasks_1122_);
v___x_1144_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1145_ = lean_st_ref_put(v___y_1105_, v___x_1144_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1131_);
v___x_1147_ = v___x_1111_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1131_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___boxed(lean_object* v_cls_1154_, lean_object* v_msg_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1154_, v_msg_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
return v_res_1161_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_1173_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5));
v___x_1174_ = l_Lean_Name_append(v___x_1173_, v___x_1172_);
return v___x_1174_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__7));
v___x_1177_ = l_Lean_stringToMessageData(v___x_1176_);
return v___x_1177_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__9));
v___x_1180_ = l_Lean_stringToMessageData(v___x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(uint8_t v___x_1181_, lean_object* v_a_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___y_1195_; lean_object* v_snd_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1278_; 
v_snd_1215_ = lean_ctor_get(v_a_1182_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_a_1182_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; 
v_unused_1279_ = lean_ctor_get(v_a_1182_, 0);
lean_dec(v_unused_1279_);
v___x_1217_ = v_a_1182_;
v_isShared_1218_ = v_isSharedCheck_1278_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_snd_1215_);
lean_dec(v_a_1182_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1278_;
goto v_resetjp_1216_;
}
v___jp_1194_:
{
if (lean_obj_tag(v___y_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1206_; 
v_a_1196_ = lean_ctor_get(v___y_1195_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___y_1195_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1198_ = v___y_1195_;
v_isShared_1199_ = v_isSharedCheck_1206_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___y_1195_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1206_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
if (lean_obj_tag(v_a_1196_) == 0)
{
lean_object* v_a_1200_; lean_object* v___x_1202_; 
v_a_1200_ = lean_ctor_get(v_a_1196_, 0);
lean_inc(v_a_1200_);
lean_dec_ref_known(v_a_1196_, 1);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v_a_1200_);
v___x_1202_ = v___x_1198_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
else
{
lean_object* v_a_1204_; 
lean_del_object(v___x_1198_);
v_a_1204_ = lean_ctor_get(v_a_1196_, 0);
lean_inc(v_a_1204_);
lean_dec_ref_known(v_a_1196_, 1);
v_a_1182_ = v_a_1204_;
goto _start;
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
v_a_1207_ = lean_ctor_get(v___y_1195_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___y_1195_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___y_1195_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___y_1195_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_box(0);
if (lean_obj_tag(v_snd_1215_) == 7)
{
lean_object* v_binderType_1220_; lean_object* v_body_1221_; lean_object* v___x_1225_; 
v_binderType_1220_ = lean_ctor_get(v_snd_1215_, 1);
v_body_1221_ = lean_ctor_get(v_snd_1215_, 2);
lean_inc_ref(v_binderType_1220_);
v___x_1225_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_binderType_1220_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; uint8_t v___x_1227_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref_known(v___x_1225_, 1);
v___x_1227_ = lean_unbox(v_a_1226_);
lean_dec(v_a_1226_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1229_; 
lean_inc_ref(v_body_1221_);
lean_dec_ref_known(v_snd_1215_, 3);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 1, v_body_1221_);
lean_ctor_set(v___x_1217_, 0, v___x_1219_);
v___x_1229_ = v___x_1217_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_body_1221_);
v___x_1229_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
v_a_1182_ = v___x_1229_;
goto _start;
}
}
else
{
lean_object* v_toCold_1232_; lean_object* v_options_1233_; uint8_t v_hasTrace_1234_; 
lean_del_object(v___x_1217_);
v_toCold_1232_ = lean_ctor_get(v___y_1191_, 0);
v_options_1233_ = lean_ctor_get(v_toCold_1232_, 2);
v_hasTrace_1234_ = lean_ctor_get_uint8(v_options_1233_, sizeof(void*)*1);
if (v_hasTrace_1234_ == 0)
{
goto v___jp_1222_;
}
else
{
lean_object* v_inheritedTraceOptions_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v_inheritedTraceOptions_1235_ = lean_ctor_get(v_toCold_1232_, 11);
v___x_1236_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_1237_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_1238_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1235_, v_options_1233_, v___x_1237_);
if (v___x_1238_ == 0)
{
goto v___jp_1222_;
}
else
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_Meta_Grind_updateLastTag(v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
lean_dec_ref_known(v___x_1239_, 1);
v___x_1240_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8);
lean_inc_ref(v_snd_1215_);
v___x_1241_ = l_Lean_indentExpr(v_snd_1215_);
v___x_1242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1240_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10);
v___x_1244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1242_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
lean_inc_ref(v_binderType_1220_);
v___x_1245_ = l_Lean_indentExpr(v_binderType_1220_);
v___x_1246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1244_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_1236_, v___x_1246_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1249_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref_known(v___x_1247_, 1);
v___x_1249_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_1181_, v_snd_1215_, v_a_1248_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
v___y_1195_ = v___x_1249_;
goto v___jp_1194_;
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec_ref_known(v_snd_1215_, 3);
v_a_1250_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1247_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1247_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec_ref_known(v_snd_1215_, 3);
v_a_1258_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1239_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1239_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref_known(v_snd_1215_, 3);
lean_del_object(v___x_1217_);
v_a_1266_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1225_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1225_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
v___jp_1222_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_box(0);
v___x_1224_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_1181_, v_snd_1215_, v___x_1223_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
v___y_1195_ = v___x_1224_;
goto v___jp_1194_;
}
}
else
{
lean_object* v___x_1275_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1219_);
v___x_1275_ = v___x_1217_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_snd_1215_);
v___x_1275_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
return v___x_1276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___boxed(lean_object* v___x_1280_, lean_object* v_a_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
uint8_t v___x_23524__boxed_1293_; lean_object* v_res_1294_; 
v___x_23524__boxed_1293_ = lean_unbox(v___x_1280_);
v_res_1294_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_23524__boxed_1293_, v_a_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec(v___y_1282_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(lean_object* v_e_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1295_, v_a_1303_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref_known(v___x_1311_, 1);
v___x_1313_ = l_Lean_Expr_cleanupAnnotations(v_a_1312_);
v___x_1314_ = l_Lean_Expr_isApp(v___x_1313_);
if (v___x_1314_ == 0)
{
lean_dec_ref(v___x_1313_);
goto v___jp_1307_;
}
else
{
lean_object* v_arg_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v_arg_1315_ = lean_ctor_get(v___x_1313_, 1);
lean_inc_ref(v_arg_1315_);
v___x_1316_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1313_);
v___x_1317_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_1318_ = l_Lean_Expr_isConstOf(v___x_1316_, v___x_1317_);
lean_dec_ref(v___x_1316_);
if (v___x_1318_ == 0)
{
lean_dec_ref(v_arg_1315_);
goto v___jp_1307_;
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = lean_box(0);
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v_arg_1315_);
v___x_1321_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_1318_, v___x_1320_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1336_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1336_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1336_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v_fst_1326_; 
v_fst_1326_ = lean_ctor_get(v_a_1322_, 0);
lean_inc(v_fst_1326_);
lean_dec(v_a_1322_);
if (lean_obj_tag(v_fst_1326_) == 0)
{
uint8_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1327_ = 0;
v___x_1328_ = lean_box(v___x_1327_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1328_);
v___x_1330_ = v___x_1324_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
else
{
lean_object* v_val_1332_; lean_object* v___x_1334_; 
v_val_1332_ = lean_ctor_get(v_fst_1326_, 0);
lean_inc(v_val_1332_);
lean_dec_ref_known(v_fst_1326_, 1);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v_val_1332_);
v___x_1334_ = v___x_1324_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_val_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
v_a_1337_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1321_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1321_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
v_a_1345_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1311_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1311_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
v___jp_1307_:
{
uint8_t v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1308_ = 0;
v___x_1309_ = lean_box(v___x_1308_);
v___x_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
return v___x_1310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied___boxed(lean_object* v_e_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_a_1356_);
lean_dec(v_a_1355_);
lean_dec(v_a_1354_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(lean_object* v_cls_1366_, lean_object* v_msg_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1366_, v_msg_1367_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___boxed(lean_object* v_cls_1380_, lean_object* v_msg_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(v_cls_1380_, v_msg_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec(v___y_1382_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(uint8_t v___x_1394_, lean_object* v_inst_1395_, lean_object* v_a_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_1394_, v_a_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___boxed(lean_object* v___x_1409_, lean_object* v_inst_1410_, lean_object* v_a_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
uint8_t v___x_23883__boxed_1423_; lean_object* v_res_1424_; 
v___x_23883__boxed_1423_ = lean_unbox(v___x_1409_);
v_res_1424_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(v___x_23883__boxed_1423_, v_inst_1410_, v_a_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec(v___y_1412_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(lean_object* v_k_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v_b_1432_, lean_object* v_c_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v___x_1439_; 
lean_inc(v___y_1437_);
lean_inc_ref(v___y_1436_);
lean_inc(v___y_1435_);
lean_inc_ref(v___y_1434_);
lean_inc(v___y_1431_);
lean_inc_ref(v___y_1430_);
lean_inc(v___y_1429_);
lean_inc_ref(v___y_1428_);
lean_inc(v___y_1427_);
lean_inc(v___y_1426_);
v___x_1439_ = lean_apply_13(v_k_1425_, v_b_1432_, v_c_1433_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, lean_box(0));
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed(lean_object* v_k_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v_b_1447_, lean_object* v_c_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(v_k_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v_b_1447_, v_c_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec(v___y_1441_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(lean_object* v_type_1455_, lean_object* v_k_1456_, uint8_t v_cleanupAnnotations_1457_, uint8_t v_whnfType_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v___f_1470_; lean_object* v___x_1471_; 
lean_inc(v___y_1464_);
lean_inc_ref(v___y_1463_);
lean_inc(v___y_1462_);
lean_inc_ref(v___y_1461_);
lean_inc(v___y_1460_);
lean_inc(v___y_1459_);
v___f_1470_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1470_, 0, v_k_1456_);
lean_closure_set(v___f_1470_, 1, v___y_1459_);
lean_closure_set(v___f_1470_, 2, v___y_1460_);
lean_closure_set(v___f_1470_, 3, v___y_1461_);
lean_closure_set(v___f_1470_, 4, v___y_1462_);
lean_closure_set(v___f_1470_, 5, v___y_1463_);
lean_closure_set(v___f_1470_, 6, v___y_1464_);
v___x_1471_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1455_, v___f_1470_, v_cleanupAnnotations_1457_, v_whnfType_1458_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1471_) == 0)
{
return v___x_1471_;
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1471_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1471_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___boxed(lean_object* v_type_1480_, lean_object* v_k_1481_, lean_object* v_cleanupAnnotations_1482_, lean_object* v_whnfType_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1495_; uint8_t v_whnfType_boxed_1496_; lean_object* v_res_1497_; 
v_cleanupAnnotations_boxed_1495_ = lean_unbox(v_cleanupAnnotations_1482_);
v_whnfType_boxed_1496_ = lean_unbox(v_whnfType_1483_);
v_res_1497_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_1480_, v_k_1481_, v_cleanupAnnotations_boxed_1495_, v_whnfType_boxed_1496_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec(v___y_1484_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(lean_object* v_00_u03b1_1498_, lean_object* v_type_1499_, lean_object* v_k_1500_, uint8_t v_cleanupAnnotations_1501_, uint8_t v_whnfType_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_1499_, v_k_1500_, v_cleanupAnnotations_1501_, v_whnfType_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___boxed(lean_object* v_00_u03b1_1515_, lean_object* v_type_1516_, lean_object* v_k_1517_, lean_object* v_cleanupAnnotations_1518_, lean_object* v_whnfType_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1531_; uint8_t v_whnfType_boxed_1532_; lean_object* v_res_1533_; 
v_cleanupAnnotations_boxed_1531_ = lean_unbox(v_cleanupAnnotations_1518_);
v_whnfType_boxed_1532_ = lean_unbox(v_whnfType_1519_);
v_res_1533_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(v_00_u03b1_1515_, v_type_1516_, v_k_1517_, v_cleanupAnnotations_boxed_1531_, v_whnfType_boxed_1532_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec(v___y_1520_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed(lean_object** _args){
lean_object* v_e_1537_ = _args[0];
lean_object* v_name_1538_ = _args[1];
lean_object* v_name_1539_ = _args[2];
lean_object* v_a_1540_ = _args[3];
lean_object* v_a_1541_ = _args[4];
lean_object* v_xs_1542_ = _args[5];
lean_object* v_x_1543_ = _args[6];
lean_object* v___y_1544_ = _args[7];
lean_object* v___y_1545_ = _args[8];
lean_object* v___y_1546_ = _args[9];
lean_object* v___y_1547_ = _args[10];
lean_object* v___y_1548_ = _args[11];
lean_object* v___y_1549_ = _args[12];
lean_object* v___y_1550_ = _args[13];
lean_object* v___y_1551_ = _args[14];
lean_object* v___y_1552_ = _args[15];
lean_object* v___y_1553_ = _args[16];
lean_object* v___y_1554_ = _args[17];
_start:
{
uint8_t v_a_80023__boxed_1555_; lean_object* v_res_1556_; 
v_a_80023__boxed_1555_ = lean_unbox(v_a_1540_);
v_res_1556_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(v_e_1537_, v_name_1538_, v_name_1539_, v_a_80023__boxed_1555_, v_a_1541_, v_xs_1542_, v_x_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec_ref(v_x_1543_);
lean_dec_ref(v_xs_1542_);
lean_dec(v_name_1539_);
lean_dec(v_name_1538_);
return v_res_1556_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__0));
v___x_1559_ = l_Lean_stringToMessageData(v___x_1558_);
return v___x_1559_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__2));
v___x_1562_ = l_Lean_stringToMessageData(v___x_1561_);
return v___x_1562_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__4));
v___x_1565_ = l_Lean_stringToMessageData(v___x_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(lean_object* v_e_1566_, lean_object* v_h_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
uint8_t v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; uint8_t v___y_1586_; uint8_t v___y_1587_; lean_object* v_h_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; uint8_t v___y_1784_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v_toCold_1958_; lean_object* v_options_1959_; uint8_t v_hasTrace_1960_; 
v_toCold_1958_ = lean_ctor_get(v_a_1576_, 0);
v_options_1959_ = lean_ctor_get(v_toCold_1958_, 2);
v_hasTrace_1960_ = lean_ctor_get_uint8(v_options_1959_, sizeof(void*)*1);
if (v_hasTrace_1960_ == 0)
{
v___y_1861_ = v_a_1568_;
v___y_1862_ = v_a_1569_;
v___y_1863_ = v_a_1570_;
v___y_1864_ = v_a_1571_;
v___y_1865_ = v_a_1572_;
v___y_1866_ = v_a_1573_;
v___y_1867_ = v_a_1574_;
v___y_1868_ = v_a_1575_;
v___y_1869_ = v_a_1576_;
v___y_1870_ = v_a_1577_;
goto v___jp_1860_;
}
else
{
lean_object* v_inheritedTraceOptions_1961_; lean_object* v_cls_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; 
v_inheritedTraceOptions_1961_ = lean_ctor_get(v_toCold_1958_, 11);
v_cls_1962_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_1963_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_1964_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1961_, v_options_1959_, v___x_1963_);
if (v___x_1964_ == 0)
{
v___y_1861_ = v_a_1568_;
v___y_1862_ = v_a_1569_;
v___y_1863_ = v_a_1570_;
v___y_1864_ = v_a_1571_;
v___y_1865_ = v_a_1572_;
v___y_1866_ = v_a_1573_;
v___y_1867_ = v_a_1574_;
v___y_1868_ = v_a_1575_;
v___y_1869_ = v_a_1576_;
v___y_1870_ = v_a_1577_;
goto v___jp_1860_;
}
else
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_Meta_Grind_updateLastTag(v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v___x_1966_; 
lean_dec_ref_known(v___x_1965_, 1);
lean_inc(v_a_1577_);
lean_inc_ref(v_a_1576_);
lean_inc(v_a_1575_);
lean_inc_ref(v_a_1574_);
lean_inc_ref(v_h_1567_);
v___x_1966_ = lean_infer_type(v_h_1567_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
v___x_1968_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5);
v___x_1969_ = l_Lean_MessageData_ofExpr(v_a_1967_);
v___x_1970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1968_);
lean_ctor_set(v___x_1970_, 1, v___x_1969_);
v___x_1971_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1962_, v___x_1970_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_dec_ref_known(v___x_1971_, 1);
v___y_1861_ = v_a_1568_;
v___y_1862_ = v_a_1569_;
v___y_1863_ = v_a_1570_;
v___y_1864_ = v_a_1571_;
v___y_1865_ = v_a_1572_;
v___y_1866_ = v_a_1573_;
v___y_1867_ = v_a_1574_;
v___y_1868_ = v_a_1575_;
v___y_1869_ = v_a_1576_;
v___y_1870_ = v_a_1577_;
goto v___jp_1860_;
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec_ref(v_h_1567_);
lean_dec_ref(v_e_1566_);
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
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref(v_h_1567_);
lean_dec_ref(v_e_1566_);
v_a_1980_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1966_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1966_);
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
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec_ref(v_h_1567_);
lean_dec_ref(v_e_1566_);
v_a_1988_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1965_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1965_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
v___jp_1579_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_box(0);
v___x_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
return v___x_1581_;
}
v___jp_1582_:
{
if (v___y_1587_ == 0)
{
lean_dec_ref(v_e_1566_);
if (v___y_1586_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
lean_dec_ref(v_h_1588_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v___y_1584_);
v___x_1599_ = lean_box(0);
v___x_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
return v___x_1600_;
}
else
{
lean_object* v___x_1601_; 
lean_inc_ref(v___y_1585_);
v___x_1601_ = l_Lean_Meta_normLitValue(v___y_1585_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1603_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
lean_inc_ref(v___y_1584_);
v___x_1603_ = l_Lean_Meta_normLitValue(v___y_1584_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1643_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1643_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1643_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
uint8_t v___x_1608_; 
v___x_1608_ = lean_expr_eqv(v_a_1602_, v_a_1604_);
lean_dec(v_a_1604_);
lean_dec(v_a_1602_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; 
lean_del_object(v___x_1606_);
v___x_1609_ = l_Lean_Meta_mkEq(v___y_1585_, v___y_1584_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
v___x_1611_ = l_Lean_mkNot(v_a_1610_);
v___x_1612_ = l_Lean_Meta_mkDecideProof(v___x_1611_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1622_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1615_ = v___x_1612_;
v_isShared_1616_ = v_isSharedCheck_1622_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1612_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1622_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1617_ = l_Lean_Expr_app___override(v_a_1613_, v_h_1588_);
v___x_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 0, v___x_1618_);
v___x_1620_ = v___x_1615_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec_ref(v_h_1588_);
v_a_1623_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1612_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1612_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec_ref(v_h_1588_);
v_a_1631_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1609_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1609_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
lean_dec_ref(v_h_1588_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v___y_1584_);
v___x_1639_ = lean_box(0);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1639_);
v___x_1641_ = v___x_1606_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec(v_a_1602_);
lean_dec_ref(v_h_1588_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v___y_1584_);
v_a_1644_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1603_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1603_);
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
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v_h_1588_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v___y_1584_);
v_a_1652_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1601_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1601_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
else
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Lean_Meta_isConstructorApp_x3f(v___y_1585_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1761_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1761_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1761_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
if (lean_obj_tag(v_a_1661_) == 1)
{
lean_object* v_val_1665_; lean_object* v___x_1666_; 
lean_del_object(v___x_1663_);
v_val_1665_ = lean_ctor_get(v_a_1661_, 0);
lean_inc(v_val_1665_);
lean_dec_ref_known(v_a_1661_, 1);
v___x_1666_ = l_Lean_Meta_isConstructorApp_x3f(v___y_1584_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1748_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1748_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1748_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
if (lean_obj_tag(v_a_1667_) == 1)
{
lean_object* v_val_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1743_; 
lean_del_object(v___x_1669_);
v_val_1671_ = lean_ctor_get(v_a_1667_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_a_1667_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1673_ = v_a_1667_;
v_isShared_1674_ = v_isSharedCheck_1743_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_val_1671_);
lean_dec(v_a_1667_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1743_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_1593_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1677_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref_known(v___x_1675_, 1);
v___x_1677_ = l_Lean_Meta_mkNoConfusion(v_a_1676_, v_h_1588_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_toConstantVal_1678_; lean_object* v_toConstantVal_1679_; lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1726_; 
v_toConstantVal_1678_ = lean_ctor_get(v_val_1665_, 0);
lean_inc_ref(v_toConstantVal_1678_);
lean_dec(v_val_1665_);
v_toConstantVal_1679_ = lean_ctor_get(v_val_1671_, 0);
lean_inc_ref(v_toConstantVal_1679_);
lean_dec(v_val_1671_);
v_a_1680_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1682_ = v___x_1677_;
v_isShared_1683_ = v_isSharedCheck_1726_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1677_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1726_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v_name_1684_; lean_object* v_name_1685_; uint8_t v___x_1686_; 
v_name_1684_ = lean_ctor_get(v_toConstantVal_1678_, 0);
lean_inc(v_name_1684_);
lean_dec_ref(v_toConstantVal_1678_);
v_name_1685_ = lean_ctor_get(v_toConstantVal_1679_, 0);
lean_inc(v_name_1685_);
lean_dec_ref(v_toConstantVal_1679_);
v___x_1686_ = lean_name_eq(v_name_1684_, v_name_1685_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1688_; 
lean_dec(v_name_1685_);
lean_dec(v_name_1684_);
lean_dec_ref(v_e_1566_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v_a_1680_);
v___x_1688_ = v___x_1673_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1680_);
v___x_1688_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1690_; 
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 0, v___x_1688_);
v___x_1690_ = v___x_1682_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
else
{
lean_object* v___x_1693_; lean_object* v___f_1694_; uint8_t v___x_1695_; lean_object* v___x_1696_; 
lean_del_object(v___x_1682_);
lean_del_object(v___x_1673_);
v___x_1693_ = lean_box(v___y_1583_);
lean_inc(v_a_1680_);
v___f_1694_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed), 18, 5);
lean_closure_set(v___f_1694_, 0, v_e_1566_);
lean_closure_set(v___f_1694_, 1, v_name_1684_);
lean_closure_set(v___f_1694_, 2, v_name_1685_);
lean_closure_set(v___f_1694_, 3, v___x_1693_);
lean_closure_set(v___f_1694_, 4, v_a_1680_);
v___x_1695_ = 0;
lean_inc(v___y_1598_);
lean_inc_ref(v___y_1597_);
lean_inc(v___y_1596_);
lean_inc_ref(v___y_1595_);
v___x_1696_ = lean_infer_type(v_a_1680_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v___x_1698_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1696_, 1);
v___x_1698_ = l_Lean_Meta_whnfD(v_a_1697_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1709_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1709_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1709_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
if (lean_obj_tag(v_a_1699_) == 7)
{
lean_object* v_binderType_1703_; lean_object* v___x_1704_; 
lean_del_object(v___x_1701_);
v_binderType_1703_ = lean_ctor_get(v_a_1699_, 1);
lean_inc_ref(v_binderType_1703_);
lean_dec_ref_known(v_a_1699_, 3);
v___x_1704_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_binderType_1703_, v___f_1694_, v___x_1695_, v___x_1695_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
return v___x_1704_;
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1707_; 
lean_dec(v_a_1699_);
lean_dec_ref(v___f_1694_);
v___x_1705_ = lean_box(0);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1705_);
v___x_1707_ = v___x_1701_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec_ref(v___f_1694_);
v_a_1710_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1698_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1698_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec_ref(v___f_1694_);
v_a_1718_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1696_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1696_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_del_object(v___x_1673_);
lean_dec(v_val_1671_);
lean_dec(v_val_1665_);
lean_dec_ref(v_e_1566_);
v_a_1727_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1677_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1677_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_del_object(v___x_1673_);
lean_dec(v_val_1671_);
lean_dec(v_val_1665_);
lean_dec_ref(v_h_1588_);
lean_dec_ref(v_e_1566_);
v_a_1735_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1675_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1675_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1746_; 
lean_dec(v_a_1667_);
lean_dec(v_val_1665_);
lean_dec_ref(v_h_1588_);
lean_dec_ref(v_e_1566_);
v___x_1744_ = lean_box(0);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v___x_1744_);
v___x_1746_ = v___x_1669_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1744_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
lean_dec(v_val_1665_);
lean_dec_ref(v_h_1588_);
lean_dec_ref(v_e_1566_);
v_a_1749_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1666_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1666_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1759_; 
lean_dec(v_a_1661_);
lean_dec_ref(v_h_1588_);
lean_dec_ref(v___y_1584_);
lean_dec_ref(v_e_1566_);
v___x_1757_ = lean_box(0);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v___x_1757_);
v___x_1759_ = v___x_1663_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1757_);
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
lean_dec_ref(v_h_1588_);
lean_dec_ref(v___y_1584_);
lean_dec_ref(v_e_1566_);
v_a_1762_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1660_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1660_);
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
v___jp_1770_:
{
lean_object* v_self_1785_; uint8_t v_interpreted_1786_; uint8_t v_ctor_1787_; lean_object* v___x_1788_; 
v_self_1785_ = lean_ctor_get(v___y_1779_, 0);
lean_inc_ref_n(v_self_1785_, 2);
v_interpreted_1786_ = lean_ctor_get_uint8(v___y_1779_, sizeof(void*)*12 + 1);
v_ctor_1787_ = lean_ctor_get_uint8(v___y_1779_, sizeof(void*)*12 + 2);
lean_dec_ref(v___y_1779_);
lean_inc_ref(v___y_1771_);
v___x_1788_ = l_Lean_Meta_Grind_hasSameType(v_self_1785_, v___y_1771_, v___y_1781_, v___y_1782_, v___y_1778_, v___y_1780_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1851_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1851_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1851_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
uint8_t v___x_1793_; 
v___x_1793_ = lean_unbox(v_a_1789_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1796_; 
lean_dec(v_a_1789_);
lean_dec_ref(v_self_1785_);
lean_dec_ref(v___y_1777_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v_h_1567_);
lean_dec_ref(v_e_1566_);
v___x_1794_ = lean_box(0);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v___x_1794_);
v___x_1796_ = v___x_1791_;
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
else
{
lean_del_object(v___x_1791_);
if (v___y_1784_ == 0)
{
lean_object* v___x_1798_; 
lean_inc(v___y_1780_);
lean_inc_ref(v___y_1778_);
lean_inc(v___y_1782_);
lean_inc_ref(v___y_1781_);
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1775_);
lean_inc(v___y_1773_);
lean_inc_ref(v___y_1774_);
lean_inc(v___y_1776_);
lean_inc(v___y_1772_);
lean_inc_ref(v_self_1785_);
v___x_1798_ = lean_grind_mk_eq_proof(v_self_1785_, v___y_1777_, v___y_1772_, v___y_1776_, v___y_1774_, v___y_1773_, v___y_1775_, v___y_1783_, v___y_1781_, v___y_1782_, v___y_1778_, v___y_1780_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1800_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_a_1799_);
lean_dec_ref_known(v___x_1798_, 1);
v___x_1800_ = l_Lean_Meta_mkEqTrans(v_a_1799_, v_h_1567_, v___y_1781_, v___y_1782_, v___y_1778_, v___y_1780_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; uint8_t v___x_1802_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1801_);
lean_dec_ref_known(v___x_1800_, 1);
v___x_1802_ = lean_unbox(v_a_1789_);
lean_dec(v_a_1789_);
v___y_1583_ = v___x_1802_;
v___y_1584_ = v___y_1771_;
v___y_1585_ = v_self_1785_;
v___y_1586_ = v_interpreted_1786_;
v___y_1587_ = v_ctor_1787_;
v_h_1588_ = v_a_1801_;
v___y_1589_ = v___y_1772_;
v___y_1590_ = v___y_1776_;
v___y_1591_ = v___y_1774_;
v___y_1592_ = v___y_1773_;
v___y_1593_ = v___y_1775_;
v___y_1594_ = v___y_1783_;
v___y_1595_ = v___y_1781_;
v___y_1596_ = v___y_1782_;
v___y_1597_ = v___y_1778_;
v___y_1598_ = v___y_1780_;
goto v___jp_1582_;
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec(v_a_1789_);
lean_dec_ref(v_self_1785_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v_e_1566_);
v_a_1803_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1800_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1800_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec(v_a_1789_);
lean_dec_ref(v_self_1785_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v_h_1567_);
lean_dec_ref(v_e_1566_);
v_a_1811_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1798_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1798_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
else
{
lean_object* v___x_1819_; 
lean_inc(v___y_1780_);
lean_inc_ref(v___y_1778_);
lean_inc(v___y_1782_);
lean_inc_ref(v___y_1781_);
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1775_);
lean_inc(v___y_1773_);
lean_inc_ref(v___y_1774_);
lean_inc(v___y_1776_);
lean_inc(v___y_1772_);
lean_inc_ref(v_self_1785_);
v___x_1819_ = lean_grind_mk_heq_proof(v_self_1785_, v___y_1777_, v___y_1772_, v___y_1776_, v___y_1774_, v___y_1773_, v___y_1775_, v___y_1783_, v___y_1781_, v___y_1782_, v___y_1778_, v___y_1780_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1821_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref_known(v___x_1819_, 1);
v___x_1821_ = l_Lean_Meta_mkHEqTrans(v_a_1820_, v_h_1567_, v___y_1781_, v___y_1782_, v___y_1778_, v___y_1780_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; uint8_t v___x_1823_; lean_object* v___x_1824_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1822_);
lean_dec_ref_known(v___x_1821_, 1);
v___x_1823_ = 0;
v___x_1824_ = l_Lean_Meta_mkEqOfHEq(v_a_1822_, v___x_1823_, v___y_1781_, v___y_1782_, v___y_1778_, v___y_1780_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; uint8_t v___x_1826_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_a_1825_);
lean_dec_ref_known(v___x_1824_, 1);
v___x_1826_ = lean_unbox(v_a_1789_);
lean_dec(v_a_1789_);
v___y_1583_ = v___x_1826_;
v___y_1584_ = v___y_1771_;
v___y_1585_ = v_self_1785_;
v___y_1586_ = v_interpreted_1786_;
v___y_1587_ = v_ctor_1787_;
v_h_1588_ = v_a_1825_;
v___y_1589_ = v___y_1772_;
v___y_1590_ = v___y_1776_;
v___y_1591_ = v___y_1774_;
v___y_1592_ = v___y_1773_;
v___y_1593_ = v___y_1775_;
v___y_1594_ = v___y_1783_;
v___y_1595_ = v___y_1781_;
v___y_1596_ = v___y_1782_;
v___y_1597_ = v___y_1778_;
v___y_1598_ = v___y_1780_;
goto v___jp_1582_;
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
lean_dec(v_a_1789_);
lean_dec_ref(v_self_1785_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v_e_1566_);
v_a_1827_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1824_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1824_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_dec(v_a_1789_);
lean_dec_ref(v_self_1785_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v_e_1566_);
v_a_1835_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1821_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1821_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec(v_a_1789_);
lean_dec_ref(v_self_1785_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v_h_1567_);
lean_dec_ref(v_e_1566_);
v_a_1843_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1819_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1819_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec_ref(v_self_1785_);
lean_dec_ref(v___y_1777_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v_h_1567_);
lean_dec_ref(v_e_1566_);
v_a_1852_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1788_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1788_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
v___jp_1860_:
{
lean_object* v___x_1871_; 
lean_inc(v___y_1870_);
lean_inc_ref(v___y_1869_);
lean_inc(v___y_1868_);
lean_inc_ref(v___y_1867_);
lean_inc_ref(v_h_1567_);
v___x_1871_ = lean_infer_type(v_h_1567_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1949_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1949_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1949_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; 
v___x_1876_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_a_1872_);
if (lean_obj_tag(v___x_1876_) == 1)
{
lean_object* v_val_1877_; lean_object* v_snd_1878_; lean_object* v_fst_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1944_; 
lean_del_object(v___x_1874_);
v_val_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_val_1877_);
lean_dec_ref_known(v___x_1876_, 1);
v_snd_1878_ = lean_ctor_get(v_val_1877_, 1);
v_fst_1879_ = lean_ctor_get(v_val_1877_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v_val_1877_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1881_ = v_val_1877_;
v_isShared_1882_ = v_isSharedCheck_1944_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_snd_1878_);
lean_inc(v_fst_1879_);
lean_dec(v_val_1877_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1944_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v_fst_1883_; lean_object* v_snd_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1943_; 
v_fst_1883_ = lean_ctor_get(v_snd_1878_, 0);
v_snd_1884_ = lean_ctor_get(v_snd_1878_, 1);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_snd_1878_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1886_ = v_snd_1878_;
v_isShared_1887_ = v_isSharedCheck_1943_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_snd_1884_);
lean_inc(v_fst_1883_);
lean_dec(v_snd_1878_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1943_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lean_Meta_Sym_shareCommon(v_fst_1883_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1890_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref_known(v___x_1888_, 1);
v___x_1890_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_a_1889_, v___y_1861_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc(v_a_1891_);
lean_dec_ref_known(v___x_1890_, 1);
if (lean_obj_tag(v_a_1891_) == 1)
{
lean_del_object(v___x_1886_);
lean_del_object(v___x_1881_);
if (lean_obj_tag(v_fst_1879_) == 0)
{
lean_object* v_val_1892_; uint8_t v___x_1893_; 
v_val_1892_ = lean_ctor_get(v_a_1891_, 0);
lean_inc(v_val_1892_);
lean_dec_ref_known(v_a_1891_, 1);
v___x_1893_ = 0;
v___y_1771_ = v_snd_1884_;
v___y_1772_ = v___y_1861_;
v___y_1773_ = v___y_1864_;
v___y_1774_ = v___y_1863_;
v___y_1775_ = v___y_1865_;
v___y_1776_ = v___y_1862_;
v___y_1777_ = v_a_1889_;
v___y_1778_ = v___y_1869_;
v___y_1779_ = v_val_1892_;
v___y_1780_ = v___y_1870_;
v___y_1781_ = v___y_1867_;
v___y_1782_ = v___y_1868_;
v___y_1783_ = v___y_1866_;
v___y_1784_ = v___x_1893_;
goto v___jp_1770_;
}
else
{
lean_object* v_val_1894_; uint8_t v___x_1895_; 
lean_dec_ref_known(v_fst_1879_, 1);
v_val_1894_ = lean_ctor_get(v_a_1891_, 0);
lean_inc(v_val_1894_);
lean_dec_ref_known(v_a_1891_, 1);
v___x_1895_ = 1;
v___y_1771_ = v_snd_1884_;
v___y_1772_ = v___y_1861_;
v___y_1773_ = v___y_1864_;
v___y_1774_ = v___y_1863_;
v___y_1775_ = v___y_1865_;
v___y_1776_ = v___y_1862_;
v___y_1777_ = v_a_1889_;
v___y_1778_ = v___y_1869_;
v___y_1779_ = v_val_1894_;
v___y_1780_ = v___y_1870_;
v___y_1781_ = v___y_1867_;
v___y_1782_ = v___y_1868_;
v___y_1783_ = v___y_1866_;
v___y_1784_ = v___x_1895_;
goto v___jp_1770_;
}
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1899_; 
lean_dec(v_a_1891_);
lean_dec(v_snd_1884_);
lean_dec(v_fst_1879_);
lean_dec_ref(v_h_1567_);
v___x_1896_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1);
v___x_1897_ = l_Lean_indentExpr(v_a_1889_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set_tag(v___x_1886_, 7);
lean_ctor_set(v___x_1886_, 1, v___x_1897_);
lean_ctor_set(v___x_1886_, 0, v___x_1896_);
v___x_1899_ = v___x_1886_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1900_; lean_object* v___x_1902_; 
v___x_1900_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3);
if (v_isShared_1882_ == 0)
{
lean_ctor_set_tag(v___x_1881_, 7);
lean_ctor_set(v___x_1881_, 1, v___x_1900_);
lean_ctor_set(v___x_1881_, 0, v___x_1899_);
v___x_1902_ = v___x_1881_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1899_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v___x_1900_);
v___x_1902_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1903_ = l_Lean_indentExpr(v_e_1566_);
v___x_1904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1902_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1865_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; uint8_t v_verbose_1907_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref_known(v___x_1905_, 1);
v_verbose_1907_ = lean_ctor_get_uint8(v_a_1906_, 0);
lean_dec(v_a_1906_);
if (v_verbose_1907_ == 0)
{
lean_dec_ref_known(v___x_1904_, 2);
goto v___jp_1579_;
}
else
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_Meta_Sym_reportIssue(v___x_1904_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_dec_ref_known(v___x_1908_, 1);
goto v___jp_1579_;
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1908_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec_ref_known(v___x_1904_, 2);
v_a_1917_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1905_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1905_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_dec(v_a_1889_);
lean_del_object(v___x_1886_);
lean_dec(v_snd_1884_);
lean_del_object(v___x_1881_);
lean_dec(v_fst_1879_);
lean_dec_ref(v_h_1567_);
lean_dec_ref(v_e_1566_);
v_a_1927_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1890_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1890_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_del_object(v___x_1886_);
lean_dec(v_snd_1884_);
lean_del_object(v___x_1881_);
lean_dec(v_fst_1879_);
lean_dec_ref(v_h_1567_);
lean_dec_ref(v_e_1566_);
v_a_1935_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1888_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1888_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
}
}
else
{
lean_object* v___x_1945_; lean_object* v___x_1947_; 
lean_dec(v___x_1876_);
lean_dec_ref(v_h_1567_);
lean_dec_ref(v_e_1566_);
v___x_1945_ = lean_box(0);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1945_);
v___x_1947_ = v___x_1874_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec_ref(v_h_1567_);
lean_dec_ref(v_e_1566_);
v_a_1950_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1871_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1871_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(lean_object* v_e_1996_, lean_object* v_xs_1997_, lean_object* v___x_1998_, lean_object* v___x_1999_, uint8_t v_a_2000_, lean_object* v_a_2001_, lean_object* v_as_2002_, size_t v_sz_2003_, size_t v_i_2004_, lean_object* v_b_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
uint8_t v___y_2018_; uint8_t v___x_2066_; 
v___x_2066_ = lean_name_eq(v___x_1998_, v___x_1999_);
if (v___x_2066_ == 0)
{
uint8_t v___x_2067_; 
v___x_2067_ = 1;
v___y_2018_ = v___x_2067_;
goto v___jp_2017_;
}
else
{
uint8_t v___x_2068_; 
v___x_2068_ = 0;
v___y_2018_ = v___x_2068_;
goto v___jp_2017_;
}
v___jp_2017_:
{
uint8_t v___x_2019_; 
v___x_2019_ = lean_usize_dec_lt(v_i_2004_, v_sz_2003_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; 
lean_dec_ref(v_a_2001_);
lean_dec_ref(v_e_1996_);
v___x_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2020_, 0, v_b_2005_);
return v___x_2020_;
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v_a_2023_; lean_object* v___x_2024_; 
lean_dec_ref(v_b_2005_);
v___x_2021_ = lean_box(0);
v___x_2022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_a_2023_ = lean_array_uget_borrowed(v_as_2002_, v_i_2004_);
lean_inc(v_a_2023_);
lean_inc_ref(v_e_1996_);
v___x_2024_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_1996_, v_a_2023_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2024_, 1);
if (lean_obj_tag(v_a_2025_) == 1)
{
lean_object* v_val_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2054_; 
lean_dec_ref(v_e_1996_);
v_val_2026_ = lean_ctor_get(v_a_2025_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_a_2025_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2028_ = v_a_2025_;
v_isShared_2029_ = v_isSharedCheck_2054_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_val_2026_);
lean_dec(v_a_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2054_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
uint8_t v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = 1;
v___x_2031_ = l_Lean_Meta_mkLambdaFVars(v_xs_1997_, v_val_2026_, v___y_2018_, v_a_2000_, v___y_2018_, v_a_2000_, v___x_2030_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2045_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2034_ = v___x_2031_;
v_isShared_2035_ = v_isSharedCheck_2045_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2045_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2036_ = l_Lean_Expr_app___override(v_a_2001_, v_a_2032_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v___x_2036_);
v___x_2038_ = v___x_2028_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2042_; 
v___x_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
v___x_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
lean_ctor_set(v___x_2040_, 1, v___x_2021_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v___x_2040_);
v___x_2042_ = v___x_2034_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_del_object(v___x_2028_);
lean_dec_ref(v_a_2001_);
v_a_2046_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_2031_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2031_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
}
else
{
size_t v___x_2055_; size_t v___x_2056_; 
lean_dec(v_a_2025_);
v___x_2055_ = ((size_t)1ULL);
v___x_2056_ = lean_usize_add(v_i_2004_, v___x_2055_);
v_i_2004_ = v___x_2056_;
v_b_2005_ = v___x_2022_;
goto _start;
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec_ref(v_a_2001_);
lean_dec_ref(v_e_1996_);
v_a_2058_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2024_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2024_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(lean_object* v_e_2069_, lean_object* v_name_2070_, lean_object* v_name_2071_, uint8_t v_a_2072_, lean_object* v_a_2073_, lean_object* v_xs_2074_, lean_object* v_x_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; size_t v_sz_2089_; size_t v___x_2090_; lean_object* v___x_2091_; 
v___x_2087_ = lean_box(0);
v___x_2088_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_sz_2089_ = lean_array_size(v_xs_2074_);
v___x_2090_ = ((size_t)0ULL);
v___x_2091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_2069_, v_xs_2074_, v_name_2070_, v_name_2071_, v_a_2072_, v_a_2073_, v_xs_2074_, v_sz_2089_, v___x_2090_, v___x_2088_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2104_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2094_ = v___x_2091_;
v_isShared_2095_ = v_isSharedCheck_2104_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2091_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2104_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v_fst_2096_; 
v_fst_2096_ = lean_ctor_get(v_a_2092_, 0);
lean_inc(v_fst_2096_);
lean_dec(v_a_2092_);
if (lean_obj_tag(v_fst_2096_) == 0)
{
lean_object* v___x_2098_; 
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2087_);
v___x_2098_ = v___x_2094_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2087_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
else
{
lean_object* v_val_2100_; lean_object* v___x_2102_; 
v_val_2100_ = lean_ctor_get(v_fst_2096_, 0);
lean_inc(v_val_2100_);
lean_dec_ref_known(v_fst_2096_, 1);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v_val_2100_);
v___x_2102_ = v___x_2094_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_val_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
v_a_2105_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2091_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2091_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_e_2113_ = _args[0];
lean_object* v_xs_2114_ = _args[1];
lean_object* v___x_2115_ = _args[2];
lean_object* v___x_2116_ = _args[3];
lean_object* v_a_2117_ = _args[4];
lean_object* v_a_2118_ = _args[5];
lean_object* v_as_2119_ = _args[6];
lean_object* v_sz_2120_ = _args[7];
lean_object* v_i_2121_ = _args[8];
lean_object* v_b_2122_ = _args[9];
lean_object* v___y_2123_ = _args[10];
lean_object* v___y_2124_ = _args[11];
lean_object* v___y_2125_ = _args[12];
lean_object* v___y_2126_ = _args[13];
lean_object* v___y_2127_ = _args[14];
lean_object* v___y_2128_ = _args[15];
lean_object* v___y_2129_ = _args[16];
lean_object* v___y_2130_ = _args[17];
lean_object* v___y_2131_ = _args[18];
lean_object* v___y_2132_ = _args[19];
lean_object* v___y_2133_ = _args[20];
_start:
{
uint8_t v_a_80049__boxed_2134_; size_t v_sz_boxed_2135_; size_t v_i_boxed_2136_; lean_object* v_res_2137_; 
v_a_80049__boxed_2134_ = lean_unbox(v_a_2117_);
v_sz_boxed_2135_ = lean_unbox_usize(v_sz_2120_);
lean_dec(v_sz_2120_);
v_i_boxed_2136_ = lean_unbox_usize(v_i_2121_);
lean_dec(v_i_2121_);
v_res_2137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_2113_, v_xs_2114_, v___x_2115_, v___x_2116_, v_a_80049__boxed_2134_, v_a_2118_, v_as_2119_, v_sz_boxed_2135_, v_i_boxed_2136_, v_b_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v_as_2119_);
lean_dec(v___x_2116_);
lean_dec(v___x_2115_);
lean_dec_ref(v_xs_2114_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___boxed(lean_object* v_e_2138_, lean_object* v_h_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2138_, v_h_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
lean_dec(v_a_2147_);
lean_dec_ref(v_a_2146_);
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
lean_dec(v_a_2143_);
lean_dec_ref(v_a_2142_);
lean_dec(v_a_2141_);
lean_dec(v_a_2140_);
return v_res_2151_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__0));
v___x_2154_ = l_Lean_stringToMessageData(v___x_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(lean_object* v_e_2155_, lean_object* v_xs_2156_, uint8_t v___x_2157_, lean_object* v_as_2158_, size_t v_sz_2159_, size_t v_i_2160_, lean_object* v_b_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_a_2174_; uint8_t v___x_2178_; 
v___x_2178_ = lean_usize_dec_lt(v_i_2160_, v_sz_2159_);
if (v___x_2178_ == 0)
{
lean_object* v___x_2179_; 
lean_dec_ref(v_e_2155_);
v___x_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2179_, 0, v_b_2161_);
return v___x_2179_;
}
else
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v_a_2182_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___x_2233_; 
lean_dec_ref(v_b_2161_);
v___x_2180_ = lean_box(0);
v___x_2181_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_a_2182_ = lean_array_uget_borrowed(v_as_2158_, v_i_2160_);
lean_inc(v___y_2171_);
lean_inc_ref(v___y_2170_);
lean_inc(v___y_2169_);
lean_inc_ref(v___y_2168_);
lean_inc(v_a_2182_);
v___x_2233_ = lean_infer_type(v_a_2182_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2235_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc_n(v_a_2234_, 2);
lean_dec_ref_known(v___x_2233_, 1);
v___x_2235_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_a_2234_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; uint8_t v___x_2237_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v___x_2235_, 1);
v___x_2237_ = lean_unbox(v_a_2236_);
lean_dec(v_a_2236_);
if (v___x_2237_ == 0)
{
lean_dec(v_a_2234_);
v_a_2174_ = v___x_2181_;
goto v___jp_2173_;
}
else
{
lean_object* v_toCold_2238_; lean_object* v_options_2239_; uint8_t v_hasTrace_2240_; 
v_toCold_2238_ = lean_ctor_get(v___y_2170_, 0);
v_options_2239_ = lean_ctor_get(v_toCold_2238_, 2);
v_hasTrace_2240_ = lean_ctor_get_uint8(v_options_2239_, sizeof(void*)*1);
if (v_hasTrace_2240_ == 0)
{
lean_dec(v_a_2234_);
v___y_2184_ = v___y_2162_;
v___y_2185_ = v___y_2163_;
v___y_2186_ = v___y_2164_;
v___y_2187_ = v___y_2165_;
v___y_2188_ = v___y_2166_;
v___y_2189_ = v___y_2167_;
v___y_2190_ = v___y_2168_;
v___y_2191_ = v___y_2169_;
v___y_2192_ = v___y_2170_;
v___y_2193_ = v___y_2171_;
goto v___jp_2183_;
}
else
{
lean_object* v_inheritedTraceOptions_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; uint8_t v___x_2244_; 
v_inheritedTraceOptions_2241_ = lean_ctor_get(v_toCold_2238_, 11);
v___x_2242_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_2243_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_2244_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2241_, v_options_2239_, v___x_2243_);
if (v___x_2244_ == 0)
{
lean_dec(v_a_2234_);
v___y_2184_ = v___y_2162_;
v___y_2185_ = v___y_2163_;
v___y_2186_ = v___y_2164_;
v___y_2187_ = v___y_2165_;
v___y_2188_ = v___y_2166_;
v___y_2189_ = v___y_2167_;
v___y_2190_ = v___y_2168_;
v___y_2191_ = v___y_2169_;
v___y_2192_ = v___y_2170_;
v___y_2193_ = v___y_2171_;
goto v___jp_2183_;
}
else
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Lean_Meta_Grind_updateLastTag(v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
lean_dec_ref_known(v___x_2245_, 1);
v___x_2246_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1);
v___x_2247_ = l_Lean_MessageData_ofExpr(v_a_2234_);
v___x_2248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2246_);
lean_ctor_set(v___x_2248_, 1, v___x_2247_);
v___x_2249_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_2242_, v___x_2248_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_dec_ref_known(v___x_2249_, 1);
v___y_2184_ = v___y_2162_;
v___y_2185_ = v___y_2163_;
v___y_2186_ = v___y_2164_;
v___y_2187_ = v___y_2165_;
v___y_2188_ = v___y_2166_;
v___y_2189_ = v___y_2167_;
v___y_2190_ = v___y_2168_;
v___y_2191_ = v___y_2169_;
v___y_2192_ = v___y_2170_;
v___y_2193_ = v___y_2171_;
goto v___jp_2183_;
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec_ref(v_e_2155_);
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2249_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2249_);
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
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
lean_dec(v_a_2234_);
lean_dec_ref(v_e_2155_);
v_a_2258_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2245_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2245_);
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
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec(v_a_2234_);
lean_dec_ref(v_e_2155_);
v_a_2266_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2235_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2235_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec_ref(v_e_2155_);
v_a_2274_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2233_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2233_);
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
v___jp_2183_:
{
lean_object* v___x_2194_; 
lean_inc(v_a_2182_);
lean_inc_ref(v_e_2155_);
v___x_2194_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2155_, v_a_2182_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
if (lean_obj_tag(v_a_2195_) == 1)
{
lean_object* v_val_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2224_; 
lean_dec_ref(v_e_2155_);
v_val_2196_ = lean_ctor_get(v_a_2195_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_a_2195_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2198_ = v_a_2195_;
v_isShared_2199_ = v_isSharedCheck_2224_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_val_2196_);
lean_dec(v_a_2195_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2224_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
uint8_t v___x_2200_; uint8_t v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = 0;
v___x_2201_ = 1;
v___x_2202_ = l_Lean_Meta_mkLambdaFVars(v_xs_2156_, v_val_2196_, v___x_2200_, v___x_2157_, v___x_2200_, v___x_2157_, v___x_2201_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2215_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2215_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2215_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 0, v_a_2203_);
v___x_2208_ = v___x_2198_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
v___x_2210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
lean_ctor_set(v___x_2210_, 1, v___x_2180_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2210_);
v___x_2212_ = v___x_2205_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_del_object(v___x_2198_);
v_a_2216_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2202_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2202_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
}
else
{
lean_dec(v_a_2195_);
v_a_2174_ = v___x_2181_;
goto v___jp_2173_;
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec_ref(v_e_2155_);
v_a_2225_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2194_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2194_);
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
}
v___jp_2173_:
{
size_t v___x_2175_; size_t v___x_2176_; 
v___x_2175_ = ((size_t)1ULL);
v___x_2176_ = lean_usize_add(v_i_2160_, v___x_2175_);
lean_inc_ref(v_a_2174_);
v_i_2160_ = v___x_2176_;
v_b_2161_ = v_a_2174_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_e_2282_ = _args[0];
lean_object* v_xs_2283_ = _args[1];
lean_object* v___x_2284_ = _args[2];
lean_object* v_as_2285_ = _args[3];
lean_object* v_sz_2286_ = _args[4];
lean_object* v_i_2287_ = _args[5];
lean_object* v_b_2288_ = _args[6];
lean_object* v___y_2289_ = _args[7];
lean_object* v___y_2290_ = _args[8];
lean_object* v___y_2291_ = _args[9];
lean_object* v___y_2292_ = _args[10];
lean_object* v___y_2293_ = _args[11];
lean_object* v___y_2294_ = _args[12];
lean_object* v___y_2295_ = _args[13];
lean_object* v___y_2296_ = _args[14];
lean_object* v___y_2297_ = _args[15];
lean_object* v___y_2298_ = _args[16];
lean_object* v___y_2299_ = _args[17];
_start:
{
uint8_t v___x_21058__boxed_2300_; size_t v_sz_boxed_2301_; size_t v_i_boxed_2302_; lean_object* v_res_2303_; 
v___x_21058__boxed_2300_ = lean_unbox(v___x_2284_);
v_sz_boxed_2301_ = lean_unbox_usize(v_sz_2286_);
lean_dec(v_sz_2286_);
v_i_boxed_2302_ = lean_unbox_usize(v_i_2287_);
lean_dec(v_i_2287_);
v_res_2303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2282_, v_xs_2283_, v___x_21058__boxed_2300_, v_as_2285_, v_sz_boxed_2301_, v_i_boxed_2302_, v_b_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v_as_2285_);
lean_dec_ref(v_xs_2283_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(lean_object* v_e_2304_, uint8_t v___x_2305_, lean_object* v_xs_2306_, lean_object* v_x_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; size_t v_sz_2321_; size_t v___x_2322_; lean_object* v___x_2323_; 
v___x_2319_ = lean_box(0);
v___x_2320_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_sz_2321_ = lean_array_size(v_xs_2306_);
v___x_2322_ = ((size_t)0ULL);
v___x_2323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2304_, v_xs_2306_, v___x_2305_, v_xs_2306_, v_sz_2321_, v___x_2322_, v___x_2320_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2336_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2326_ = v___x_2323_;
v_isShared_2327_ = v_isSharedCheck_2336_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2323_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2336_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v_fst_2328_; 
v_fst_2328_ = lean_ctor_get(v_a_2324_, 0);
lean_inc(v_fst_2328_);
lean_dec(v_a_2324_);
if (lean_obj_tag(v_fst_2328_) == 0)
{
lean_object* v___x_2330_; 
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2319_);
v___x_2330_ = v___x_2326_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2319_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
else
{
lean_object* v_val_2332_; lean_object* v___x_2334_; 
v_val_2332_ = lean_ctor_get(v_fst_2328_, 0);
lean_inc(v_val_2332_);
lean_dec_ref_known(v_fst_2328_, 1);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v_val_2332_);
v___x_2334_ = v___x_2326_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_val_2332_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
v_a_2337_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2323_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2323_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed(lean_object* v_e_2345_, lean_object* v___x_2346_, lean_object* v_xs_2347_, lean_object* v_x_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
uint8_t v___x_21310__boxed_2360_; lean_object* v_res_2361_; 
v___x_21310__boxed_2360_ = lean_unbox(v___x_2346_);
v_res_2361_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(v_e_2345_, v___x_21310__boxed_2360_, v_xs_2347_, v_x_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v_x_2348_);
lean_dec_ref(v_xs_2347_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(lean_object* v_e_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v___x_2377_; 
lean_inc_ref(v_e_2362_);
v___x_2377_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2362_, v_a_2370_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2378_);
lean_dec_ref_known(v___x_2377_, 1);
v___x_2379_ = l_Lean_Expr_cleanupAnnotations(v_a_2378_);
v___x_2380_ = l_Lean_Expr_isApp(v___x_2379_);
if (v___x_2380_ == 0)
{
lean_dec_ref(v___x_2379_);
lean_dec_ref(v_e_2362_);
goto v___jp_2374_;
}
else
{
lean_object* v_arg_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; uint8_t v___x_2384_; 
v_arg_2381_ = lean_ctor_get(v___x_2379_, 1);
lean_inc_ref(v_arg_2381_);
v___x_2382_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2379_);
v___x_2383_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_2384_ = l_Lean_Expr_isConstOf(v___x_2382_, v___x_2383_);
lean_dec_ref(v___x_2382_);
if (v___x_2384_ == 0)
{
lean_dec_ref(v_arg_2381_);
lean_dec_ref(v_e_2362_);
goto v___jp_2374_;
}
else
{
lean_object* v___x_2385_; lean_object* v___f_2386_; uint8_t v___x_2387_; lean_object* v___x_2388_; 
v___x_2385_ = lean_box(v___x_2384_);
v___f_2386_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed), 15, 2);
lean_closure_set(v___f_2386_, 0, v_e_2362_);
lean_closure_set(v___f_2386_, 1, v___x_2385_);
v___x_2387_ = 0;
v___x_2388_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_arg_2381_, v___f_2386_, v___x_2387_, v___x_2387_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
return v___x_2388_;
}
}
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec_ref(v_e_2362_);
v_a_2389_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2377_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2377_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
v___jp_2374_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = lean_box(0);
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
return v___x_2376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___boxed(lean_object* v_e_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
lean_dec(v_a_2401_);
lean_dec_ref(v_a_2400_);
lean_dec(v_a_2399_);
lean_dec(v_a_2398_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(lean_object* v_e_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v___x_2416_; uint8_t v___x_2417_; uint8_t v___x_2418_; 
v___x_2416_ = l_Lean_Expr_getAppFn(v_e_2410_);
v___x_2417_ = l_Lean_Expr_isMVar(v___x_2416_);
lean_dec_ref(v___x_2416_);
v___x_2418_ = 1;
if (v___x_2417_ == 0)
{
lean_object* v___x_2419_; 
lean_inc_ref(v_e_2410_);
v___x_2419_ = l_Lean_Meta_isConstructorApp_x3f(v_e_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2433_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2422_ = v___x_2419_;
v_isShared_2423_ = v_isSharedCheck_2433_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2419_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2433_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
if (lean_obj_tag(v_a_2420_) == 0)
{
if (v___x_2417_ == 0)
{
lean_object* v___x_2424_; 
lean_del_object(v___x_2422_);
v___x_2424_ = l_Lean_Meta_isLitValue(v_e_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_);
return v___x_2424_;
}
else
{
lean_object* v___x_2425_; lean_object* v___x_2427_; 
lean_dec_ref(v_e_2410_);
v___x_2425_ = lean_box(v___x_2418_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2425_);
v___x_2427_ = v___x_2422_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
else
{
lean_object* v___x_2429_; lean_object* v___x_2431_; 
lean_dec_ref_known(v_a_2420_, 1);
lean_dec_ref(v_e_2410_);
v___x_2429_ = lean_box(v___x_2418_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2429_);
v___x_2431_ = v___x_2422_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2429_);
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
lean_dec_ref(v_e_2410_);
v_a_2434_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2419_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2419_);
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
lean_object* v___x_2442_; lean_object* v___x_2443_; 
lean_dec_ref(v_e_2410_);
v___x_2442_ = lean_box(v___x_2418_);
v___x_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
return v___x_2443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg___boxed(lean_object* v_e_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(v_e_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
lean_dec(v_a_2448_);
lean_dec_ref(v_a_2447_);
lean_dec(v_a_2446_);
lean_dec_ref(v_a_2445_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike(lean_object* v_e_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(v_e_2451_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___boxed(lean_object* v_e_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike(v_e_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
lean_dec(v_a_2470_);
lean_dec_ref(v_a_2469_);
lean_dec(v_a_2468_);
lean_dec_ref(v_a_2467_);
lean_dec(v_a_2466_);
lean_dec(v_a_2465_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(lean_object* v_e_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v___x_2489_; 
lean_inc_ref(v_e_2477_);
v___x_2489_ = l_Lean_Meta_Grind_getRootENode___redArg(v_e_2477_, v_a_2478_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2557_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2492_ = v___x_2489_;
v_isShared_2493_ = v_isSharedCheck_2557_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2489_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2557_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
uint8_t v_ctor_2494_; 
v_ctor_2494_ = lean_ctor_get_uint8(v_a_2490_, sizeof(void*)*12 + 2);
if (v_ctor_2494_ == 0)
{
uint8_t v_interpreted_2495_; 
v_interpreted_2495_ = lean_ctor_get_uint8(v_a_2490_, sizeof(void*)*12 + 1);
if (v_interpreted_2495_ == 0)
{
lean_object* v___x_2497_; 
lean_dec(v_a_2490_);
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 0, v_e_2477_);
v___x_2497_ = v___x_2492_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_e_2477_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
else
{
lean_object* v_self_2499_; lean_object* v___x_2501_; 
lean_dec_ref(v_e_2477_);
v_self_2499_ = lean_ctor_get(v_a_2490_, 0);
lean_inc_ref(v_self_2499_);
lean_dec(v_a_2490_);
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 0, v_self_2499_);
v___x_2501_ = v___x_2492_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_self_2499_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
else
{
lean_object* v_self_2503_; lean_object* v___x_2504_; 
lean_del_object(v___x_2492_);
lean_dec_ref(v_e_2477_);
v_self_2503_ = lean_ctor_get(v_a_2490_, 0);
lean_inc_ref_n(v_self_2503_, 2);
lean_dec(v_a_2490_);
v___x_2504_ = l_Lean_Meta_isConstructorApp_x3f(v_self_2503_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2548_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2507_ = v___x_2504_;
v_isShared_2508_ = v_isSharedCheck_2548_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2548_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
if (lean_obj_tag(v_a_2505_) == 1)
{
lean_object* v_val_2509_; lean_object* v_numParams_2510_; lean_object* v_numFields_2511_; lean_object* v_nargs_2512_; lean_object* v___x_2513_; lean_object* v_dummy_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
lean_del_object(v___x_2507_);
v_val_2509_ = lean_ctor_get(v_a_2505_, 0);
lean_inc(v_val_2509_);
lean_dec_ref_known(v_a_2505_, 1);
v_numParams_2510_ = lean_ctor_get(v_val_2509_, 3);
lean_inc(v_numParams_2510_);
v_numFields_2511_ = lean_ctor_get(v_val_2509_, 4);
lean_inc(v_numFields_2511_);
lean_dec(v_val_2509_);
v_nargs_2512_ = l_Lean_Expr_getAppNumArgs(v_self_2503_);
v___x_2513_ = lean_nat_add(v_numParams_2510_, v_numFields_2511_);
lean_dec(v_numFields_2511_);
v_dummy_2514_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0);
lean_inc(v_nargs_2512_);
v___x_2515_ = lean_mk_array(v_nargs_2512_, v_dummy_2514_);
v___x_2516_ = lean_unsigned_to_nat(1u);
v___x_2517_ = lean_nat_sub(v_nargs_2512_, v___x_2516_);
lean_dec(v_nargs_2512_);
lean_inc_ref(v_self_2503_);
v___x_2518_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_2503_, v___x_2515_, v___x_2517_);
v___x_2519_ = 0;
v___x_2520_ = lean_box(v___x_2519_);
v___x_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2518_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
v___x_2522_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v___x_2513_, v_ctor_2494_, v_numParams_2510_, v___x_2521_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_);
lean_dec(v___x_2513_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2536_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2525_ = v___x_2522_;
v_isShared_2526_ = v_isSharedCheck_2536_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2522_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2536_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v_snd_2527_; uint8_t v___x_2528_; 
v_snd_2527_ = lean_ctor_get(v_a_2523_, 1);
v___x_2528_ = lean_unbox(v_snd_2527_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2530_; 
lean_dec(v_a_2523_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v_self_2503_);
v___x_2530_ = v___x_2525_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_self_2503_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
else
{
lean_object* v_fst_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
lean_del_object(v___x_2525_);
v_fst_2532_ = lean_ctor_get(v_a_2523_, 0);
lean_inc(v_fst_2532_);
lean_dec(v_a_2523_);
v___x_2533_ = l_Lean_Expr_getAppFn(v_self_2503_);
lean_dec_ref(v_self_2503_);
v___x_2534_ = l_Lean_mkAppN(v___x_2533_, v_fst_2532_);
lean_dec(v_fst_2532_);
v___x_2535_ = l_Lean_Meta_Sym_shareCommon(v___x_2534_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_);
return v___x_2535_;
}
}
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec_ref(v_self_2503_);
v_a_2537_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2522_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2522_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
else
{
lean_object* v___x_2546_; 
lean_dec(v_a_2505_);
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 0, v_self_2503_);
v___x_2546_ = v___x_2507_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_self_2503_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec_ref(v_self_2503_);
v_a_2549_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2504_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2504_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
lean_dec_ref(v_e_2477_);
v_a_2558_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2489_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2489_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(lean_object* v_upperBound_2566_, uint8_t v___x_2567_, lean_object* v_a_2568_, lean_object* v_b_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v_a_2582_; uint8_t v___x_2586_; 
v___x_2586_ = lean_nat_dec_lt(v_a_2568_, v_upperBound_2566_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; 
lean_dec(v_a_2568_);
v___x_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2587_, 0, v_b_2569_);
return v___x_2587_;
}
else
{
lean_object* v_fst_2588_; lean_object* v_snd_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2616_; 
v_fst_2588_ = lean_ctor_get(v_b_2569_, 0);
v_snd_2589_ = lean_ctor_get(v_b_2569_, 1);
v_isSharedCheck_2616_ = !lean_is_exclusive(v_b_2569_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2591_ = v_b_2569_;
v_isShared_2592_ = v_isSharedCheck_2616_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_snd_2589_);
lean_inc(v_fst_2588_);
lean_dec(v_b_2569_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2616_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = l_Lean_instInhabitedExpr;
v___x_2594_ = lean_array_get_borrowed(v___x_2593_, v_fst_2588_, v_a_2568_);
lean_inc(v___x_2594_);
v___x_2595_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v___x_2594_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; size_t v___x_2597_; size_t v___x_2598_; uint8_t v___x_2599_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v___x_2595_, 1);
v___x_2597_ = lean_ptr_addr(v___x_2594_);
v___x_2598_ = lean_ptr_addr(v_a_2596_);
v___x_2599_ = lean_usize_dec_eq(v___x_2597_, v___x_2598_);
if (v___x_2599_ == 0)
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2603_; 
lean_dec(v_snd_2589_);
v___x_2600_ = lean_array_set(v_fst_2588_, v_a_2568_, v_a_2596_);
v___x_2601_ = lean_box(v___x_2567_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 1, v___x_2601_);
lean_ctor_set(v___x_2591_, 0, v___x_2600_);
v___x_2603_ = v___x_2591_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
v_a_2582_ = v___x_2603_;
goto v___jp_2581_;
}
}
else
{
lean_object* v___x_2606_; 
lean_dec(v_a_2596_);
if (v_isShared_2592_ == 0)
{
v___x_2606_ = v___x_2591_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_fst_2588_);
lean_ctor_set(v_reuseFailAlloc_2607_, 1, v_snd_2589_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
v_a_2582_ = v___x_2606_;
goto v___jp_2581_;
}
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_del_object(v___x_2591_);
lean_dec(v_snd_2589_);
lean_dec(v_fst_2588_);
lean_dec(v_a_2568_);
v_a_2608_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2595_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2595_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
v___jp_2581_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = lean_unsigned_to_nat(1u);
v___x_2584_ = lean_nat_add(v_a_2568_, v___x_2583_);
lean_dec(v_a_2568_);
v_a_2568_ = v___x_2584_;
v_b_2569_ = v_a_2582_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg___boxed(lean_object* v_upperBound_2617_, lean_object* v___x_2618_, lean_object* v_a_2619_, lean_object* v_b_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
uint8_t v___x_13705__boxed_2632_; lean_object* v_res_2633_; 
v___x_13705__boxed_2632_ = lean_unbox(v___x_2618_);
v_res_2633_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2617_, v___x_13705__boxed_2632_, v_a_2619_, v_b_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec(v_upperBound_2617_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go___boxed(lean_object* v_e_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_e_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
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
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(lean_object* v_upperBound_2647_, uint8_t v___x_2648_, lean_object* v_inst_2649_, lean_object* v_R_2650_, lean_object* v_a_2651_, lean_object* v_b_2652_, lean_object* v_c_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2647_, v___x_2648_, v_a_2651_, v_b_2652_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_2666_ = _args[0];
lean_object* v___x_2667_ = _args[1];
lean_object* v_inst_2668_ = _args[2];
lean_object* v_R_2669_ = _args[3];
lean_object* v_a_2670_ = _args[4];
lean_object* v_b_2671_ = _args[5];
lean_object* v_c_2672_ = _args[6];
lean_object* v___y_2673_ = _args[7];
lean_object* v___y_2674_ = _args[8];
lean_object* v___y_2675_ = _args[9];
lean_object* v___y_2676_ = _args[10];
lean_object* v___y_2677_ = _args[11];
lean_object* v___y_2678_ = _args[12];
lean_object* v___y_2679_ = _args[13];
lean_object* v___y_2680_ = _args[14];
lean_object* v___y_2681_ = _args[15];
lean_object* v___y_2682_ = _args[16];
lean_object* v___y_2683_ = _args[17];
_start:
{
uint8_t v___x_13950__boxed_2684_; lean_object* v_res_2685_; 
v___x_13950__boxed_2684_ = lean_unbox(v___x_2667_);
v_res_2685_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(v_upperBound_2666_, v___x_13950__boxed_2684_, v_inst_2668_, v_R_2669_, v_a_2670_, v_b_2671_, v_c_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec(v_upperBound_2666_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(lean_object* v_e_2686_, lean_object* v___y_2687_){
_start:
{
uint8_t v___x_2689_; 
v___x_2689_ = l_Lean_Expr_hasMVar(v_e_2686_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2690_; 
v___x_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2690_, 0, v_e_2686_);
return v___x_2690_;
}
else
{
lean_object* v___x_2691_; lean_object* v_mctx_2692_; lean_object* v___x_2693_; lean_object* v_fst_2694_; lean_object* v_snd_2695_; lean_object* v___x_2696_; lean_object* v_cache_2697_; lean_object* v_zetaDeltaFVarIds_2698_; lean_object* v_postponed_2699_; lean_object* v_diag_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2709_; 
v___x_2691_ = lean_st_ref_get(v___y_2687_);
v_mctx_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc_ref(v_mctx_2692_);
lean_dec(v___x_2691_);
v___x_2693_ = l_Lean_instantiateMVarsCore(v_mctx_2692_, v_e_2686_);
v_fst_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_fst_2694_);
v_snd_2695_ = lean_ctor_get(v___x_2693_, 1);
lean_inc(v_snd_2695_);
lean_dec_ref(v___x_2693_);
v___x_2696_ = lean_st_ref_take(v___y_2687_);
v_cache_2697_ = lean_ctor_get(v___x_2696_, 1);
v_zetaDeltaFVarIds_2698_ = lean_ctor_get(v___x_2696_, 2);
v_postponed_2699_ = lean_ctor_get(v___x_2696_, 3);
v_diag_2700_ = lean_ctor_get(v___x_2696_, 4);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2709_ == 0)
{
lean_object* v_unused_2710_; 
v_unused_2710_ = lean_ctor_get(v___x_2696_, 0);
lean_dec(v_unused_2710_);
v___x_2702_ = v___x_2696_;
v_isShared_2703_ = v_isSharedCheck_2709_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_diag_2700_);
lean_inc(v_postponed_2699_);
lean_inc(v_zetaDeltaFVarIds_2698_);
lean_inc(v_cache_2697_);
lean_dec(v___x_2696_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2709_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 0, v_snd_2695_);
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_snd_2695_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_cache_2697_);
lean_ctor_set(v_reuseFailAlloc_2708_, 2, v_zetaDeltaFVarIds_2698_);
lean_ctor_set(v_reuseFailAlloc_2708_, 3, v_postponed_2699_);
lean_ctor_set(v_reuseFailAlloc_2708_, 4, v_diag_2700_);
v___x_2705_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = lean_st_ref_put(v___y_2687_, v___x_2705_);
v___x_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2707_, 0, v_fst_2694_);
return v___x_2707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg___boxed(lean_object* v_e_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v_e_2711_, v___y_2712_);
lean_dec(v___y_2712_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(lean_object* v_e_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v_e_2715_, v___y_2723_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___boxed(lean_object* v_e_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(v_e_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec(v___y_2729_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0(lean_object* v_k_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v___x_2753_; 
lean_inc(v___y_2747_);
lean_inc_ref(v___y_2746_);
lean_inc(v___y_2745_);
lean_inc_ref(v___y_2744_);
lean_inc(v___y_2743_);
lean_inc(v___y_2742_);
v___x_2753_ = lean_apply_11(v_k_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, lean_box(0));
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0___boxed(lean_object* v_k_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0(v_k_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec(v___y_2755_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(lean_object* v_k_2767_, uint8_t v_allowLevelAssignments_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v___f_2780_; lean_object* v___x_2781_; 
lean_inc(v___y_2774_);
lean_inc_ref(v___y_2773_);
lean_inc(v___y_2772_);
lean_inc_ref(v___y_2771_);
lean_inc(v___y_2770_);
lean_inc(v___y_2769_);
v___f_2780_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_2780_, 0, v_k_2767_);
lean_closure_set(v___f_2780_, 1, v___y_2769_);
lean_closure_set(v___f_2780_, 2, v___y_2770_);
lean_closure_set(v___f_2780_, 3, v___y_2771_);
lean_closure_set(v___f_2780_, 4, v___y_2772_);
lean_closure_set(v___f_2780_, 5, v___y_2773_);
lean_closure_set(v___f_2780_, 6, v___y_2774_);
v___x_2781_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2768_, v___f_2780_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
if (lean_obj_tag(v___x_2781_) == 0)
{
return v___x_2781_;
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2781_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2781_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___boxed(lean_object* v_k_2790_, lean_object* v_allowLevelAssignments_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2803_; lean_object* v_res_2804_; 
v_allowLevelAssignments_boxed_2803_ = lean_unbox(v_allowLevelAssignments_2791_);
v_res_2804_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(v_k_2790_, v_allowLevelAssignments_boxed_2803_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec(v___y_2792_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(lean_object* v_00_u03b1_2805_, lean_object* v_k_2806_, uint8_t v_allowLevelAssignments_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v___x_2819_; 
v___x_2819_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(v_k_2806_, v_allowLevelAssignments_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___boxed(lean_object* v_00_u03b1_2820_, lean_object* v_k_2821_, lean_object* v_allowLevelAssignments_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2834_; lean_object* v_res_2835_; 
v_allowLevelAssignments_boxed_2834_ = lean_unbox(v_allowLevelAssignments_2822_);
v_res_2835_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_00_u03b1_2820_, v_k_2821_, v_allowLevelAssignments_boxed_2834_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec(v___y_2823_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0(lean_object* v_cls_2836_, lean_object* v_____do__lift_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v_toCold_2849_; lean_object* v_options_2850_; uint8_t v_hasTrace_2851_; 
v_toCold_2849_ = lean_ctor_get(v___y_2846_, 0);
v_options_2850_ = lean_ctor_get(v_toCold_2849_, 2);
v_hasTrace_2851_ = lean_ctor_get_uint8(v_options_2850_, sizeof(void*)*1);
if (v_hasTrace_2851_ == 0)
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
lean_dec(v_cls_2836_);
v___x_2852_ = lean_box(v_hasTrace_2851_);
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
return v___x_2853_;
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2855_; uint8_t v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2854_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5));
v___x_2855_ = l_Lean_Name_append(v___x_2854_, v_cls_2836_);
v___x_2856_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2837_, v_options_2850_, v___x_2855_);
lean_dec(v___x_2855_);
v___x_2857_ = lean_box(v___x_2856_);
v___x_2858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2857_);
return v___x_2858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed(lean_object* v_cls_2859_, lean_object* v_____do__lift_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Lean_Meta_Grind_tryToProveFalse___lam__0(v_cls_2859_, v_____do__lift_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v_____do__lift_2860_);
return v_res_2872_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3(void){
_start:
{
lean_object* v_cls_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v_cls_2881_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1));
v___x_2882_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5));
v___x_2883_ = l_Lean_Name_append(v___x_2882_, v_cls_2881_);
return v___x_2883_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5(void){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2885_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__4));
v___x_2886_ = l_Lean_stringToMessageData(v___x_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(lean_object* v_as_2887_, size_t v_sz_2888_, size_t v_i_2889_, lean_object* v_b_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v_a_2903_; uint8_t v___x_2907_; 
v___x_2907_ = lean_usize_dec_lt(v_i_2889_, v_sz_2888_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; 
v___x_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2908_, 0, v_b_2890_);
return v___x_2908_;
}
else
{
lean_object* v_snd_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_3165_; 
v_snd_2909_ = lean_ctor_get(v_b_2890_, 1);
v_isSharedCheck_3165_ = !lean_is_exclusive(v_b_2890_);
if (v_isSharedCheck_3165_ == 0)
{
lean_object* v_unused_3166_; 
v_unused_3166_ = lean_ctor_get(v_b_2890_, 0);
lean_dec(v_unused_3166_);
v___x_2911_ = v_b_2890_;
v_isShared_2912_ = v_isSharedCheck_3165_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_snd_2909_);
lean_dec(v_b_2890_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_3165_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v_array_2913_; lean_object* v_start_2914_; lean_object* v_stop_2915_; lean_object* v___x_2916_; uint8_t v___x_2917_; 
v_array_2913_ = lean_ctor_get(v_snd_2909_, 0);
v_start_2914_ = lean_ctor_get(v_snd_2909_, 1);
v_stop_2915_ = lean_ctor_get(v_snd_2909_, 2);
v___x_2916_ = lean_box(0);
v___x_2917_ = lean_nat_dec_lt(v_start_2914_, v_stop_2915_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2919_; 
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 0, v___x_2916_);
v___x_2919_ = v___x_2911_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_2921_, 1, v_snd_2909_);
v___x_2919_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
lean_object* v___x_2920_; 
v___x_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2919_);
return v___x_2920_;
}
}
else
{
lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_3161_; 
lean_inc(v_stop_2915_);
lean_inc(v_start_2914_);
lean_inc_ref(v_array_2913_);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_snd_2909_);
if (v_isSharedCheck_3161_ == 0)
{
lean_object* v_unused_3162_; lean_object* v_unused_3163_; lean_object* v_unused_3164_; 
v_unused_3162_ = lean_ctor_get(v_snd_2909_, 2);
lean_dec(v_unused_3162_);
v_unused_3163_ = lean_ctor_get(v_snd_2909_, 1);
lean_dec(v_unused_3163_);
v_unused_3164_ = lean_ctor_get(v_snd_2909_, 0);
lean_dec(v_unused_3164_);
v___x_2923_ = v_snd_2909_;
v_isShared_2924_ = v_isSharedCheck_3161_;
goto v_resetjp_2922_;
}
else
{
lean_dec(v_snd_2909_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_3161_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2929_; 
v___x_2925_ = lean_array_fget(v_array_2913_, v_start_2914_);
v___x_2926_ = lean_unsigned_to_nat(1u);
v___x_2927_ = lean_nat_add(v_start_2914_, v___x_2926_);
lean_dec(v_start_2914_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 1, v___x_2927_);
v___x_2929_ = v___x_2923_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_array_2913_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v___x_2927_);
lean_ctor_set(v_reuseFailAlloc_3160_, 2, v_stop_2915_);
v___x_2929_ = v_reuseFailAlloc_3160_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
uint8_t v___x_2930_; 
v___x_2930_ = lean_unbox(v___x_2925_);
if (v___x_2930_ == 0)
{
lean_object* v___x_2932_; 
lean_dec(v___x_2925_);
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 1, v___x_2929_);
lean_ctor_set(v___x_2911_, 0, v___x_2916_);
v___x_2932_ = v___x_2911_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v___x_2929_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
v_a_2903_ = v___x_2932_;
goto v___jp_2902_;
}
}
else
{
lean_object* v_cls_2934_; lean_object* v_a_2935_; lean_object* v_____x_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___x_2973_; 
v_cls_2934_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1));
v_a_2935_ = lean_array_uget_borrowed(v_as_2887_, v_i_2889_);
lean_inc(v___y_2900_);
lean_inc_ref(v___y_2899_);
lean_inc(v___y_2898_);
lean_inc_ref(v___y_2897_);
lean_inc(v_a_2935_);
v___x_2973_ = lean_infer_type(v_a_2935_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_3151_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_2976_ = v___x_2973_;
v_isShared_2977_ = v_isSharedCheck_3151_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2973_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_3151_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2978_; 
v___x_2978_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_a_2974_);
if (lean_obj_tag(v___x_2978_) == 1)
{
lean_object* v_val_2979_; lean_object* v_snd_2980_; lean_object* v_fst_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_3145_; 
lean_del_object(v___x_2976_);
v_val_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_val_2979_);
lean_dec_ref_known(v___x_2978_, 1);
v_snd_2980_ = lean_ctor_get(v_val_2979_, 1);
v_fst_2981_ = lean_ctor_get(v_val_2979_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_val_2979_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_2983_ = v_val_2979_;
v_isShared_2984_ = v_isSharedCheck_3145_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_snd_2980_);
lean_inc(v_fst_2981_);
lean_dec(v_val_2979_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_3145_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v_fst_2985_; lean_object* v_snd_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3144_; 
v_fst_2985_ = lean_ctor_get(v_snd_2980_, 0);
v_snd_2986_ = lean_ctor_get(v_snd_2980_, 1);
v_isSharedCheck_3144_ = !lean_is_exclusive(v_snd_2980_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_2988_ = v_snd_2980_;
v_isShared_2989_ = v_isSharedCheck_3144_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_snd_2986_);
lean_inc(v_fst_2985_);
lean_dec(v_snd_2980_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3144_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
uint8_t v___y_2991_; lean_object* v_lhs_x27_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3024_; uint8_t v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; uint8_t v___y_3082_; lean_object* v___y_3083_; uint8_t v___y_3118_; 
if (lean_obj_tag(v_fst_2981_) == 0)
{
uint8_t v___x_3142_; 
v___x_3142_ = 0;
v___y_3118_ = v___x_3142_;
goto v___jp_3117_;
}
else
{
uint8_t v___x_3143_; 
lean_dec_ref_known(v_fst_2981_, 1);
v___x_3143_ = lean_unbox(v___x_2925_);
v___y_3118_ = v___x_3143_;
goto v___jp_3117_;
}
v___jp_2990_:
{
if (v___y_2991_ == 0)
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Lean_Meta_Grind_proveEq_x3f(v_fst_2985_, v_lhs_x27_2992_, v___y_2991_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_3003_, 1);
v_____x_2937_ = v_a_3004_;
v___y_2938_ = v___y_2999_;
v___y_2939_ = v___y_3000_;
v___y_2940_ = v___y_3001_;
v___y_2941_ = v___y_3002_;
goto v___jp_2936_;
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_dec_ref(v___x_2929_);
lean_del_object(v___x_2911_);
v_a_3005_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_3003_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_3003_);
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
}
else
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Lean_Meta_Grind_proveHEq_x3f(v_fst_2985_, v_lhs_x27_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_a_3014_);
lean_dec_ref_known(v___x_3013_, 1);
v_____x_2937_ = v_a_3014_;
v___y_2938_ = v___y_2999_;
v___y_2939_ = v___y_3000_;
v___y_2940_ = v___y_3001_;
v___y_2941_ = v___y_3002_;
goto v___jp_2936_;
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec_ref(v___x_2929_);
lean_del_object(v___x_2911_);
v_a_3015_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_3013_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3013_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
}
v___jp_3023_:
{
lean_object* v___x_3037_; 
lean_inc_ref(v___y_3026_);
v___x_3037_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(v___y_3026_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3072_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3040_ = v___x_3037_;
v_isShared_3041_ = v_isSharedCheck_3072_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3037_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3072_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
uint8_t v___x_3042_; 
v___x_3042_ = lean_unbox(v_a_3038_);
lean_dec(v_a_3038_);
if (v___x_3042_ == 0)
{
lean_object* v___x_3043_; lean_object* v___x_3045_; 
lean_dec_ref(v___y_3026_);
lean_dec_ref(v___y_3024_);
lean_dec(v_fst_2985_);
lean_del_object(v___x_2911_);
v___x_3043_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 1, v___x_2929_);
lean_ctor_set(v___x_2988_, 0, v___x_3043_);
v___x_3045_ = v___x_2988_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3043_);
lean_ctor_set(v_reuseFailAlloc_3049_, 1, v___x_2929_);
v___x_3045_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
lean_object* v___x_3047_; 
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v___x_3045_);
v___x_3047_ = v___x_3040_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3045_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
else
{
lean_object* v___x_3050_; 
lean_del_object(v___x_3040_);
lean_inc_ref(v___y_3024_);
v___x_3050_ = l_Lean_Meta_isDefEqD(v___y_3024_, v___y_3026_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3063_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3053_ = v___x_3050_;
v_isShared_3054_ = v_isSharedCheck_3063_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3050_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3063_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
uint8_t v___x_3055_; 
v___x_3055_ = lean_unbox(v_a_3051_);
lean_dec(v_a_3051_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; lean_object* v___x_3058_; 
lean_dec_ref(v___y_3024_);
lean_dec(v_fst_2985_);
lean_del_object(v___x_2911_);
v___x_3056_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 1, v___x_2929_);
lean_ctor_set(v___x_2988_, 0, v___x_3056_);
v___x_3058_ = v___x_2988_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3056_);
lean_ctor_set(v_reuseFailAlloc_3062_, 1, v___x_2929_);
v___x_3058_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
lean_object* v___x_3060_; 
if (v_isShared_3054_ == 0)
{
lean_ctor_set(v___x_3053_, 0, v___x_3058_);
v___x_3060_ = v___x_3053_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3058_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
else
{
lean_del_object(v___x_3053_);
lean_del_object(v___x_2988_);
v___y_2991_ = v___y_3025_;
v_lhs_x27_2992_ = v___y_3024_;
v___y_2993_ = v___y_3027_;
v___y_2994_ = v___y_3028_;
v___y_2995_ = v___y_3029_;
v___y_2996_ = v___y_3030_;
v___y_2997_ = v___y_3031_;
v___y_2998_ = v___y_3032_;
v___y_2999_ = v___y_3033_;
v___y_3000_ = v___y_3034_;
v___y_3001_ = v___y_3035_;
v___y_3002_ = v___y_3036_;
goto v___jp_2990_;
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec_ref(v___y_3024_);
lean_del_object(v___x_2988_);
lean_dec(v_fst_2985_);
lean_dec_ref(v___x_2929_);
lean_del_object(v___x_2911_);
v_a_3064_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3050_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3050_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
}
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
lean_dec_ref(v___y_3026_);
lean_dec_ref(v___y_3024_);
lean_del_object(v___x_2988_);
lean_dec(v_fst_2985_);
lean_dec_ref(v___x_2929_);
lean_del_object(v___x_2911_);
v_a_3073_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3037_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3037_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3078_; 
if (v_isShared_3076_ == 0)
{
v___x_3078_ = v___x_3075_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
v___jp_3081_:
{
lean_object* v___x_3084_; 
lean_inc(v_fst_2985_);
v___x_3084_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_fst_2985_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_toCold_3085_; lean_object* v_options_3086_; uint8_t v_hasTrace_3087_; 
v_toCold_3085_ = lean_ctor_get(v___y_2899_, 0);
v_options_3086_ = lean_ctor_get(v_toCold_3085_, 2);
v_hasTrace_3087_ = lean_ctor_get_uint8(v_options_3086_, sizeof(void*)*1);
if (v_hasTrace_3087_ == 0)
{
lean_object* v_a_3088_; 
lean_del_object(v___x_2983_);
v_a_3088_ = lean_ctor_get(v___x_3084_, 0);
lean_inc(v_a_3088_);
lean_dec_ref_known(v___x_3084_, 1);
v___y_3024_ = v_a_3088_;
v___y_3025_ = v___y_3082_;
v___y_3026_ = v___y_3083_;
v___y_3027_ = v___y_2891_;
v___y_3028_ = v___y_2892_;
v___y_3029_ = v___y_2893_;
v___y_3030_ = v___y_2894_;
v___y_3031_ = v___y_2895_;
v___y_3032_ = v___y_2896_;
v___y_3033_ = v___y_2897_;
v___y_3034_ = v___y_2898_;
v___y_3035_ = v___y_2899_;
v___y_3036_ = v___y_2900_;
goto v___jp_3023_;
}
else
{
lean_object* v_a_3089_; lean_object* v_inheritedTraceOptions_3090_; lean_object* v___x_3091_; uint8_t v___x_3092_; 
v_a_3089_ = lean_ctor_get(v___x_3084_, 0);
lean_inc(v_a_3089_);
lean_dec_ref_known(v___x_3084_, 1);
v_inheritedTraceOptions_3090_ = lean_ctor_get(v_toCold_3085_, 11);
v___x_3091_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3);
v___x_3092_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3090_, v_options_3086_, v___x_3091_);
if (v___x_3092_ == 0)
{
lean_del_object(v___x_2983_);
v___y_3024_ = v_a_3089_;
v___y_3025_ = v___y_3082_;
v___y_3026_ = v___y_3083_;
v___y_3027_ = v___y_2891_;
v___y_3028_ = v___y_2892_;
v___y_3029_ = v___y_2893_;
v___y_3030_ = v___y_2894_;
v___y_3031_ = v___y_2895_;
v___y_3032_ = v___y_2896_;
v___y_3033_ = v___y_2897_;
v___y_3034_ = v___y_2898_;
v___y_3035_ = v___y_2899_;
v___y_3036_ = v___y_2900_;
goto v___jp_3023_;
}
else
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3096_; 
lean_inc(v_a_3089_);
v___x_3093_ = l_Lean_MessageData_ofExpr(v_a_3089_);
v___x_3094_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5);
if (v_isShared_2984_ == 0)
{
lean_ctor_set_tag(v___x_2983_, 7);
lean_ctor_set(v___x_2983_, 1, v___x_3094_);
lean_ctor_set(v___x_2983_, 0, v___x_3093_);
v___x_3096_ = v___x_2983_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3093_);
lean_ctor_set(v_reuseFailAlloc_3108_, 1, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
lean_inc_ref(v___y_3083_);
v___x_3097_ = l_Lean_MessageData_ofExpr(v___y_3083_);
v___x_3098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3096_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_2934_, v___x_3098_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_dec_ref_known(v___x_3099_, 1);
v___y_3024_ = v_a_3089_;
v___y_3025_ = v___y_3082_;
v___y_3026_ = v___y_3083_;
v___y_3027_ = v___y_2891_;
v___y_3028_ = v___y_2892_;
v___y_3029_ = v___y_2893_;
v___y_3030_ = v___y_2894_;
v___y_3031_ = v___y_2895_;
v___y_3032_ = v___y_2896_;
v___y_3033_ = v___y_2897_;
v___y_3034_ = v___y_2898_;
v___y_3035_ = v___y_2899_;
v___y_3036_ = v___y_2900_;
goto v___jp_3023_;
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
lean_dec(v_a_3089_);
lean_dec_ref(v___y_3083_);
lean_del_object(v___x_2988_);
lean_dec(v_fst_2985_);
lean_dec_ref(v___x_2929_);
lean_del_object(v___x_2911_);
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3099_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3099_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_dec_ref(v___y_3083_);
lean_del_object(v___x_2988_);
lean_dec(v_fst_2985_);
lean_del_object(v___x_2983_);
lean_dec_ref(v___x_2929_);
lean_del_object(v___x_2911_);
v_a_3109_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3084_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3084_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
v___jp_3117_:
{
lean_object* v___x_3119_; 
v___x_3119_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v_snd_2986_, v___y_2898_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; uint8_t v___x_3121_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3120_);
lean_dec_ref_known(v___x_3119_, 1);
v___x_3121_ = l_Lean_Expr_hasExprMVar(v_a_3120_);
if (v___x_3121_ == 0)
{
uint8_t v___x_3122_; 
v___x_3122_ = lean_unbox(v___x_2925_);
lean_dec(v___x_2925_);
if (v___x_3122_ == 0)
{
v___y_3082_ = v___y_3118_;
v___y_3083_ = v_a_3120_;
goto v___jp_3081_;
}
else
{
lean_object* v___x_3123_; 
v___x_3123_ = l_Lean_Meta_Grind_isEqv___redArg(v_fst_2985_, v_a_3120_, v___y_2891_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; uint8_t v___x_3125_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref_known(v___x_3123_, 1);
v___x_3125_ = lean_unbox(v_a_3124_);
lean_dec(v_a_3124_);
if (v___x_3125_ == 0)
{
v___y_3082_ = v___y_3118_;
v___y_3083_ = v_a_3120_;
goto v___jp_3081_;
}
else
{
lean_del_object(v___x_2988_);
lean_del_object(v___x_2983_);
v___y_2991_ = v___y_3118_;
v_lhs_x27_2992_ = v_a_3120_;
v___y_2993_ = v___y_2891_;
v___y_2994_ = v___y_2892_;
v___y_2995_ = v___y_2893_;
v___y_2996_ = v___y_2894_;
v___y_2997_ = v___y_2895_;
v___y_2998_ = v___y_2896_;
v___y_2999_ = v___y_2897_;
v___y_3000_ = v___y_2898_;
v___y_3001_ = v___y_2899_;
v___y_3002_ = v___y_2900_;
goto v___jp_2990_;
}
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec(v_a_3120_);
lean_del_object(v___x_2988_);
lean_dec(v_fst_2985_);
lean_del_object(v___x_2983_);
lean_dec_ref(v___x_2929_);
lean_del_object(v___x_2911_);
v_a_3126_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3123_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3123_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
}
else
{
lean_dec(v___x_2925_);
v___y_3082_ = v___y_3118_;
v___y_3083_ = v_a_3120_;
goto v___jp_3081_;
}
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
lean_del_object(v___x_2988_);
lean_dec(v_fst_2985_);
lean_del_object(v___x_2983_);
lean_dec_ref(v___x_2929_);
lean_dec(v___x_2925_);
lean_del_object(v___x_2911_);
v_a_3134_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3136_ = v___x_3119_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3119_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3134_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3149_; 
lean_dec(v___x_2978_);
lean_dec(v___x_2925_);
lean_del_object(v___x_2911_);
v___x_3146_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
v___x_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3146_);
lean_ctor_set(v___x_3147_, 1, v___x_2929_);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 0, v___x_3147_);
v___x_3149_ = v___x_2976_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec_ref(v___x_2929_);
lean_dec(v___x_2925_);
lean_del_object(v___x_2911_);
v_a_3152_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_2973_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_2973_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
v___jp_2936_:
{
if (lean_obj_tag(v_____x_2937_) == 1)
{
lean_object* v_val_2942_; lean_object* v___x_2943_; 
v_val_2942_ = lean_ctor_get(v_____x_2937_, 0);
lean_inc(v_val_2942_);
lean_dec_ref_known(v_____x_2937_, 1);
lean_inc(v_a_2935_);
v___x_2943_ = l_Lean_Meta_isExprDefEq(v_a_2935_, v_val_2942_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2959_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2946_ = v___x_2943_;
v_isShared_2947_ = v_isSharedCheck_2959_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2943_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2959_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
uint8_t v___x_2948_; 
v___x_2948_ = lean_unbox(v_a_2944_);
lean_dec(v_a_2944_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; lean_object* v___x_2951_; 
v___x_2949_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 1, v___x_2929_);
lean_ctor_set(v___x_2911_, 0, v___x_2949_);
v___x_2951_ = v___x_2911_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2949_);
lean_ctor_set(v_reuseFailAlloc_2955_, 1, v___x_2929_);
v___x_2951_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
lean_object* v___x_2953_; 
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 0, v___x_2951_);
v___x_2953_ = v___x_2946_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2951_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
else
{
lean_object* v___x_2957_; 
lean_del_object(v___x_2946_);
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 1, v___x_2929_);
lean_ctor_set(v___x_2911_, 0, v___x_2916_);
v___x_2957_ = v___x_2911_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_2958_, 1, v___x_2929_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
v_a_2903_ = v___x_2957_;
goto v___jp_2902_;
}
}
}
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
lean_dec_ref(v___x_2929_);
lean_del_object(v___x_2911_);
v_a_2960_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2943_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2943_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
else
{
lean_object* v___x_2968_; lean_object* v___x_2970_; 
lean_dec(v_____x_2937_);
v___x_2968_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 1, v___x_2929_);
lean_ctor_set(v___x_2911_, 0, v___x_2968_);
v___x_2970_ = v___x_2911_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2968_);
lean_ctor_set(v_reuseFailAlloc_2972_, 1, v___x_2929_);
v___x_2970_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2971_; 
v___x_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2970_);
return v___x_2971_;
}
}
}
}
}
}
}
}
}
v___jp_2902_:
{
size_t v___x_2904_; size_t v___x_2905_; 
v___x_2904_ = ((size_t)1ULL);
v___x_2905_ = lean_usize_add(v_i_2889_, v___x_2904_);
v_i_2889_ = v___x_2905_;
v_b_2890_ = v_a_2903_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___boxed(lean_object* v_as_3167_, lean_object* v_sz_3168_, lean_object* v_i_3169_, lean_object* v_b_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
size_t v_sz_boxed_3182_; size_t v_i_boxed_3183_; lean_object* v_res_3184_; 
v_sz_boxed_3182_ = lean_unbox_usize(v_sz_3168_);
lean_dec(v_sz_3168_);
v_i_boxed_3183_ = lean_unbox_usize(v_i_3169_);
lean_dec(v_i_3169_);
v_res_3184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(v_as_3167_, v_sz_boxed_3182_, v_i_boxed_3183_, v_b_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v_as_3167_);
return v_res_3184_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = ((lean_object*)(l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__0));
v___x_3187_ = l_Lean_stringToMessageData(v___x_3186_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1(lean_object* v_arg_3188_, uint8_t v___x_3189_, lean_object* v_e_3190_, lean_object* v___f_3191_, lean_object* v_cls_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v___x_3204_; 
lean_inc_ref(v_arg_3188_);
v___x_3204_ = l_Lean_Meta_forallMetaTelescope(v_arg_3188_, v___x_3189_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v_a_3205_; lean_object* v_fst_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3324_; 
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref_known(v___x_3204_, 1);
v_fst_3206_ = lean_ctor_get(v_a_3205_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v_a_3205_);
if (v_isSharedCheck_3324_ == 0)
{
lean_object* v_unused_3325_; 
v_unused_3325_ = lean_ctor_get(v_a_3205_, 1);
lean_dec(v_unused_3325_);
v___x_3208_ = v_a_3205_;
v_isShared_3209_ = v_isSharedCheck_3324_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_fst_3206_);
lean_dec(v_a_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3324_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3216_; 
v___x_3210_ = l_Lean_Meta_mkGenDiseqMask(v_arg_3188_);
lean_dec_ref(v_arg_3188_);
v___x_3211_ = lean_unsigned_to_nat(0u);
v___x_3212_ = lean_array_get_size(v___x_3210_);
v___x_3213_ = l_Array_toSubarray___redArg(v___x_3210_, v___x_3211_, v___x_3212_);
v___x_3214_ = lean_box(0);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 1, v___x_3213_);
lean_ctor_set(v___x_3208_, 0, v___x_3214_);
v___x_3216_ = v___x_3208_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3214_);
lean_ctor_set(v_reuseFailAlloc_3323_, 1, v___x_3213_);
v___x_3216_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
size_t v_sz_3217_; size_t v___x_3218_; lean_object* v___x_3219_; 
v_sz_3217_ = lean_array_size(v_fst_3206_);
v___x_3218_ = ((size_t)0ULL);
v___x_3219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(v_fst_3206_, v_sz_3217_, v___x_3218_, v___x_3216_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3314_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3222_ = v___x_3219_;
v_isShared_3223_ = v_isSharedCheck_3314_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3219_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3314_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v_fst_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3312_; 
v_fst_3224_ = lean_ctor_get(v_a_3220_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v_a_3220_);
if (v_isSharedCheck_3312_ == 0)
{
lean_object* v_unused_3313_; 
v_unused_3313_ = lean_ctor_get(v_a_3220_, 1);
lean_dec(v_unused_3313_);
v___x_3226_ = v_a_3220_;
v_isShared_3227_ = v_isSharedCheck_3312_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_fst_3224_);
lean_dec(v_a_3220_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3312_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
if (lean_obj_tag(v_fst_3224_) == 0)
{
lean_object* v___x_3228_; 
lean_del_object(v___x_3222_);
lean_inc_ref(v_e_3190_);
v___x_3228_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_3190_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3299_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3229_);
lean_dec_ref_known(v___x_3228_, 1);
v___x_3230_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3190_, v_a_3229_);
v___x_3231_ = l_Lean_mkAppN(v___x_3230_, v_fst_3206_);
lean_dec(v_fst_3206_);
v___x_3232_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v___x_3231_, v___y_3200_);
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3235_ = v___x_3232_;
v_isShared_3236_ = v_isSharedCheck_3299_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v___x_3232_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3299_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3242_; 
lean_inc(v_a_3233_);
v___x_3242_ = l_Lean_Meta_hasAssignableMVar(v_a_3233_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3290_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3245_ = v___x_3242_;
v_isShared_3246_ = v_isSharedCheck_3290_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3242_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3290_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
uint8_t v___x_3247_; 
v___x_3247_ = lean_unbox(v_a_3243_);
lean_dec(v_a_3243_);
if (v___x_3247_ == 0)
{
lean_object* v_toCold_3248_; lean_object* v_inheritedTraceOptions_3249_; lean_object* v___x_3250_; 
lean_del_object(v___x_3245_);
v_toCold_3248_ = lean_ctor_get(v___y_3201_, 0);
v_inheritedTraceOptions_3249_ = lean_ctor_get(v_toCold_3248_, 11);
lean_inc(v___y_3202_);
lean_inc_ref(v___y_3201_);
lean_inc(v___y_3200_);
lean_inc_ref(v___y_3199_);
lean_inc(v___y_3198_);
lean_inc_ref(v___y_3197_);
lean_inc(v___y_3196_);
lean_inc_ref(v___y_3195_);
lean_inc(v___y_3194_);
lean_inc(v___y_3193_);
lean_inc_ref(v_inheritedTraceOptions_3249_);
v___x_3250_ = lean_apply_12(v___f_3191_, v_inheritedTraceOptions_3249_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, lean_box(0));
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; uint8_t v___x_3252_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
lean_dec_ref_known(v___x_3250_, 1);
v___x_3252_ = lean_unbox(v_a_3251_);
lean_dec(v_a_3251_);
if (v___x_3252_ == 0)
{
lean_del_object(v___x_3226_);
lean_dec(v_cls_3192_);
goto v___jp_3237_;
}
else
{
lean_object* v___x_3253_; 
lean_inc(v___y_3202_);
lean_inc_ref(v___y_3201_);
lean_inc(v___y_3200_);
lean_inc_ref(v___y_3199_);
lean_inc(v_a_3233_);
v___x_3253_ = lean_infer_type(v_a_3233_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3258_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
lean_inc(v_a_3254_);
lean_dec_ref_known(v___x_3253_, 1);
lean_inc(v_a_3233_);
v___x_3255_ = l_Lean_MessageData_ofExpr(v_a_3233_);
v___x_3256_ = lean_obj_once(&l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1, &l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1_once, _init_l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1);
if (v_isShared_3227_ == 0)
{
lean_ctor_set_tag(v___x_3226_, 7);
lean_ctor_set(v___x_3226_, 1, v___x_3256_);
lean_ctor_set(v___x_3226_, 0, v___x_3255_);
v___x_3258_ = v___x_3226_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3255_);
lean_ctor_set(v_reuseFailAlloc_3270_, 1, v___x_3256_);
v___x_3258_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3259_ = l_Lean_MessageData_ofExpr(v_a_3254_);
v___x_3260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3258_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
v___x_3261_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3192_, v___x_3260_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_dec_ref_known(v___x_3261_, 1);
goto v___jp_3237_;
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_del_object(v___x_3235_);
lean_dec(v_a_3233_);
v_a_3262_ = lean_ctor_get(v___x_3261_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3261_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3261_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_del_object(v___x_3235_);
lean_dec(v_a_3233_);
lean_del_object(v___x_3226_);
lean_dec(v_cls_3192_);
v_a_3271_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3253_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3253_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
}
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
lean_del_object(v___x_3235_);
lean_dec(v_a_3233_);
lean_del_object(v___x_3226_);
lean_dec(v_cls_3192_);
v_a_3279_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3250_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3250_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
else
{
lean_object* v___x_3288_; 
lean_del_object(v___x_3235_);
lean_dec(v_a_3233_);
lean_del_object(v___x_3226_);
lean_dec(v_cls_3192_);
lean_dec_ref(v___f_3191_);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 0, v___x_3214_);
v___x_3288_ = v___x_3245_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3214_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
lean_del_object(v___x_3235_);
lean_dec(v_a_3233_);
lean_del_object(v___x_3226_);
lean_dec(v_cls_3192_);
lean_dec_ref(v___f_3191_);
v_a_3291_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3242_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3242_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3291_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
v___jp_3237_:
{
lean_object* v___x_3238_; lean_object* v___x_3240_; 
v___x_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3238_, 0, v_a_3233_);
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 0, v___x_3238_);
v___x_3240_ = v___x_3235_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
lean_del_object(v___x_3226_);
lean_dec(v_fst_3206_);
lean_dec(v_cls_3192_);
lean_dec_ref(v___f_3191_);
lean_dec_ref(v_e_3190_);
v_a_3300_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3228_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3228_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3300_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
else
{
lean_object* v_val_3308_; lean_object* v___x_3310_; 
lean_del_object(v___x_3226_);
lean_dec(v_fst_3206_);
lean_dec(v_cls_3192_);
lean_dec_ref(v___f_3191_);
lean_dec_ref(v_e_3190_);
v_val_3308_ = lean_ctor_get(v_fst_3224_, 0);
lean_inc(v_val_3308_);
lean_dec_ref_known(v_fst_3224_, 1);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v_val_3308_);
v___x_3310_ = v___x_3222_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_val_3308_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
}
else
{
lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3322_; 
lean_dec(v_fst_3206_);
lean_dec(v_cls_3192_);
lean_dec_ref(v___f_3191_);
lean_dec_ref(v_e_3190_);
v_a_3315_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3317_ = v___x_3219_;
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3219_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3320_; 
if (v_isShared_3318_ == 0)
{
v___x_3320_ = v___x_3317_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_a_3315_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
}
}
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
lean_dec(v_cls_3192_);
lean_dec_ref(v___f_3191_);
lean_dec_ref(v_e_3190_);
lean_dec_ref(v_arg_3188_);
v_a_3326_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3204_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3204_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1___boxed(lean_object* v_arg_3334_, lean_object* v___x_3335_, lean_object* v_e_3336_, lean_object* v___f_3337_, lean_object* v_cls_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
uint8_t v___x_77300__boxed_3350_; lean_object* v_res_3351_; 
v___x_77300__boxed_3350_ = lean_unbox(v___x_3335_);
v_res_3351_ = l_Lean_Meta_Grind_tryToProveFalse___lam__1(v_arg_3334_, v___x_77300__boxed_3350_, v_e_3336_, v___f_3337_, v_cls_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec(v___y_3339_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse(lean_object* v_e_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_){
_start:
{
lean_object* v_toCold_3369_; lean_object* v_inheritedTraceOptions_3370_; lean_object* v_cls_3371_; lean_object* v___f_3372_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___x_3424_; lean_object* v_a_3425_; uint8_t v___x_3426_; 
v_toCold_3369_ = lean_ctor_get(v_a_3363_, 0);
v_inheritedTraceOptions_3370_ = lean_ctor_get(v_toCold_3369_, 11);
v_cls_3371_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1));
v___f_3372_ = ((lean_object*)(l_Lean_Meta_Grind_tryToProveFalse___closed__0));
v___x_3424_ = l_Lean_Meta_Grind_tryToProveFalse___lam__0(v_cls_3371_, v_inheritedTraceOptions_3370_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_);
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref(v___x_3424_);
v___x_3426_ = lean_unbox(v_a_3425_);
lean_dec(v_a_3425_);
if (v___x_3426_ == 0)
{
v___y_3374_ = v_a_3355_;
v___y_3375_ = v_a_3356_;
v___y_3376_ = v_a_3357_;
v___y_3377_ = v_a_3358_;
v___y_3378_ = v_a_3359_;
v___y_3379_ = v_a_3360_;
v___y_3380_ = v_a_3361_;
v___y_3381_ = v_a_3362_;
v___y_3382_ = v_a_3363_;
v___y_3383_ = v_a_3364_;
goto v___jp_3373_;
}
else
{
lean_object* v___x_3427_; 
v___x_3427_ = l_Lean_Meta_Grind_updateLastTag(v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
lean_dec_ref_known(v___x_3427_, 1);
lean_inc_ref(v_e_3354_);
v___x_3428_ = l_Lean_MessageData_ofExpr(v_e_3354_);
v___x_3429_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3371_, v___x_3428_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_dec_ref_known(v___x_3429_, 1);
v___y_3374_ = v_a_3355_;
v___y_3375_ = v_a_3356_;
v___y_3376_ = v_a_3357_;
v___y_3377_ = v_a_3358_;
v___y_3378_ = v_a_3359_;
v___y_3379_ = v_a_3360_;
v___y_3380_ = v_a_3361_;
v___y_3381_ = v_a_3362_;
v___y_3382_ = v_a_3363_;
v___y_3383_ = v_a_3364_;
goto v___jp_3373_;
}
else
{
lean_dec_ref(v_e_3354_);
return v___x_3429_;
}
}
else
{
lean_dec_ref(v_e_3354_);
return v___x_3427_;
}
}
v___jp_3366_:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = lean_box(0);
v___x_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
return v___x_3368_;
}
v___jp_3373_:
{
lean_object* v___x_3384_; 
lean_inc_ref(v_e_3354_);
v___x_3384_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3354_, v___y_3381_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3386_; uint8_t v___x_3387_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3384_, 1);
v___x_3386_ = l_Lean_Expr_cleanupAnnotations(v_a_3385_);
v___x_3387_ = l_Lean_Expr_isApp(v___x_3386_);
if (v___x_3387_ == 0)
{
lean_dec_ref(v___x_3386_);
lean_dec_ref(v_e_3354_);
goto v___jp_3366_;
}
else
{
lean_object* v_arg_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; uint8_t v___x_3391_; 
v_arg_3388_ = lean_ctor_get(v___x_3386_, 1);
lean_inc_ref(v_arg_3388_);
v___x_3389_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3386_);
v___x_3390_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3391_ = l_Lean_Expr_isConstOf(v___x_3389_, v___x_3390_);
lean_dec_ref(v___x_3389_);
if (v___x_3391_ == 0)
{
lean_dec_ref(v_arg_3388_);
lean_dec_ref(v_e_3354_);
goto v___jp_3366_;
}
else
{
uint8_t v___x_3392_; lean_object* v___x_3393_; lean_object* v___f_3394_; uint8_t v___x_3395_; lean_object* v___x_3396_; 
v___x_3392_ = 0;
v___x_3393_ = lean_box(v___x_3392_);
v___f_3394_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_tryToProveFalse___lam__1___boxed), 16, 5);
lean_closure_set(v___f_3394_, 0, v_arg_3388_);
lean_closure_set(v___f_3394_, 1, v___x_3393_);
lean_closure_set(v___f_3394_, 2, v_e_3354_);
lean_closure_set(v___f_3394_, 3, v___f_3372_);
lean_closure_set(v___f_3394_, 4, v_cls_3371_);
v___x_3395_ = 0;
v___x_3396_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(v___f_3394_, v___x_3395_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3407_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3399_ = v___x_3396_;
v_isShared_3400_ = v_isSharedCheck_3407_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3396_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3407_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
if (lean_obj_tag(v_a_3397_) == 1)
{
lean_object* v_val_3401_; lean_object* v___x_3402_; 
lean_del_object(v___x_3399_);
v_val_3401_ = lean_ctor_get(v_a_3397_, 0);
lean_inc(v_val_3401_);
lean_dec_ref_known(v_a_3397_, 1);
v___x_3402_ = l_Lean_Meta_Grind_closeGoal(v_val_3401_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
return v___x_3402_;
}
else
{
lean_object* v___x_3403_; lean_object* v___x_3405_; 
lean_dec(v_a_3397_);
v___x_3403_ = lean_box(0);
if (v_isShared_3400_ == 0)
{
lean_ctor_set(v___x_3399_, 0, v___x_3403_);
v___x_3405_ = v___x_3399_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
v_a_3408_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3396_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3396_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
}
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec_ref(v_e_3354_);
v_a_3416_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3384_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3384_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___boxed(lean_object* v_e_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_);
lean_dec(v_a_3440_);
lean_dec_ref(v_a_3439_);
lean_dec(v_a_3438_);
lean_dec_ref(v_a_3437_);
lean_dec(v_a_3436_);
lean_dec_ref(v_a_3435_);
lean_dec(v_a_3434_);
lean_dec_ref(v_a_3433_);
lean_dec(v_a_3432_);
lean_dec(v_a_3431_);
return v_res_3442_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1(void){
_start:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3444_ = ((lean_object*)(l_Lean_Meta_Grind_propagateMatchCondUp___closed__0));
v___x_3445_ = l_Lean_stringToMessageData(v___x_3444_);
return v___x_3445_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3(void){
_start:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3447_ = ((lean_object*)(l_Lean_Meta_Grind_propagateMatchCondUp___closed__2));
v___x_3448_ = l_Lean_stringToMessageData(v___x_3447_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp(lean_object* v_e_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_){
_start:
{
lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v_toCold_3475_; lean_object* v_options_3476_; lean_object* v_inheritedTraceOptions_3477_; uint8_t v_hasTrace_3478_; lean_object* v_cls_3479_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; 
v_toCold_3475_ = lean_ctor_get(v_a_3458_, 0);
v_options_3476_ = lean_ctor_get(v_toCold_3475_, 2);
v_inheritedTraceOptions_3477_ = lean_ctor_get(v_toCold_3475_, 11);
v_hasTrace_3478_ = lean_ctor_get_uint8(v_options_3476_, sizeof(void*)*1);
v_cls_3479_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
if (v_hasTrace_3478_ == 0)
{
v___y_3481_ = v_a_3450_;
v___y_3482_ = v_a_3451_;
v___y_3483_ = v_a_3452_;
v___y_3484_ = v_a_3453_;
v___y_3485_ = v_a_3454_;
v___y_3486_ = v_a_3455_;
v___y_3487_ = v_a_3456_;
v___y_3488_ = v_a_3457_;
v___y_3489_ = v_a_3458_;
v___y_3490_ = v_a_3459_;
goto v___jp_3480_;
}
else
{
lean_object* v___x_3587_; uint8_t v___x_3588_; 
v___x_3587_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_3588_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3477_, v_options_3476_, v___x_3587_);
if (v___x_3588_ == 0)
{
v___y_3481_ = v_a_3450_;
v___y_3482_ = v_a_3451_;
v___y_3483_ = v_a_3452_;
v___y_3484_ = v_a_3453_;
v___y_3485_ = v_a_3454_;
v___y_3486_ = v_a_3455_;
v___y_3487_ = v_a_3456_;
v___y_3488_ = v_a_3457_;
v___y_3489_ = v_a_3458_;
v___y_3490_ = v_a_3459_;
goto v___jp_3480_;
}
else
{
lean_object* v___x_3589_; 
v___x_3589_ = l_Lean_Meta_Grind_updateLastTag(v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
lean_dec_ref_known(v___x_3589_, 1);
v___x_3590_ = lean_obj_once(&l_Lean_Meta_Grind_propagateMatchCondUp___closed__3, &l_Lean_Meta_Grind_propagateMatchCondUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3);
lean_inc_ref(v_e_3449_);
v___x_3591_ = l_Lean_indentExpr(v_e_3449_);
v___x_3592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3590_);
lean_ctor_set(v___x_3592_, 1, v___x_3591_);
v___x_3593_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3479_, v___x_3592_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_dec_ref_known(v___x_3593_, 1);
v___y_3481_ = v_a_3450_;
v___y_3482_ = v_a_3451_;
v___y_3483_ = v_a_3452_;
v___y_3484_ = v_a_3453_;
v___y_3485_ = v_a_3454_;
v___y_3486_ = v_a_3455_;
v___y_3487_ = v_a_3456_;
v___y_3488_ = v_a_3457_;
v___y_3489_ = v_a_3458_;
v___y_3490_ = v_a_3459_;
goto v___jp_3480_;
}
else
{
lean_dec_ref(v_e_3449_);
return v___x_3593_;
}
}
else
{
lean_dec_ref(v_e_3449_);
return v___x_3589_;
}
}
}
v___jp_3461_:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3462_ = lean_box(0);
v___x_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3462_);
return v___x_3463_;
}
v___jp_3464_:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; 
lean_inc_ref(v_e_3449_);
v___x_3473_ = l_Lean_Meta_mkEqTrueCore(v_e_3449_, v___y_3465_);
v___x_3474_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_3449_, v___x_3473_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
return v___x_3474_;
}
v___jp_3480_:
{
lean_object* v___x_3491_; 
lean_inc_ref(v_e_3449_);
v___x_3491_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3449_, v___y_3481_, v___y_3485_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; uint8_t v___x_3493_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref_known(v___x_3491_, 1);
v___x_3493_ = lean_unbox(v_a_3492_);
lean_dec(v_a_3492_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3494_; 
lean_inc_ref(v_e_3449_);
v___x_3494_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3449_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3550_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3497_ = v___x_3494_;
v_isShared_3498_ = v_isSharedCheck_3550_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3494_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3550_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
uint8_t v___x_3499_; 
v___x_3499_ = lean_unbox(v_a_3495_);
lean_dec(v_a_3495_);
if (v___x_3499_ == 0)
{
lean_object* v___x_3500_; lean_object* v___x_3502_; 
lean_dec_ref(v_e_3449_);
v___x_3500_ = lean_box(0);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v___x_3500_);
v___x_3502_ = v___x_3497_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3500_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
else
{
lean_object* v___x_3504_; 
lean_del_object(v___x_3497_);
lean_inc_ref(v_e_3449_);
v___x_3504_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_3449_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v_a_3505_; 
v_a_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc(v_a_3505_);
lean_dec_ref_known(v___x_3504_, 1);
if (lean_obj_tag(v_a_3505_) == 1)
{
lean_object* v_toCold_3506_; lean_object* v_options_3507_; uint8_t v_hasTrace_3508_; 
v_toCold_3506_ = lean_ctor_get(v___y_3489_, 0);
v_options_3507_ = lean_ctor_get(v_toCold_3506_, 2);
v_hasTrace_3508_ = lean_ctor_get_uint8(v_options_3507_, sizeof(void*)*1);
if (v_hasTrace_3508_ == 0)
{
lean_object* v_val_3509_; 
v_val_3509_ = lean_ctor_get(v_a_3505_, 0);
lean_inc(v_val_3509_);
lean_dec_ref_known(v_a_3505_, 1);
v___y_3465_ = v_val_3509_;
v___y_3466_ = v___y_3481_;
v___y_3467_ = v___y_3483_;
v___y_3468_ = v___y_3485_;
v___y_3469_ = v___y_3487_;
v___y_3470_ = v___y_3488_;
v___y_3471_ = v___y_3489_;
v___y_3472_ = v___y_3490_;
goto v___jp_3464_;
}
else
{
lean_object* v_val_3510_; lean_object* v_inheritedTraceOptions_3511_; lean_object* v___x_3512_; uint8_t v___x_3513_; 
v_val_3510_ = lean_ctor_get(v_a_3505_, 0);
lean_inc(v_val_3510_);
lean_dec_ref_known(v_a_3505_, 1);
v_inheritedTraceOptions_3511_ = lean_ctor_get(v_toCold_3506_, 11);
v___x_3512_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_3513_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3511_, v_options_3507_, v___x_3512_);
if (v___x_3513_ == 0)
{
v___y_3465_ = v_val_3510_;
v___y_3466_ = v___y_3481_;
v___y_3467_ = v___y_3483_;
v___y_3468_ = v___y_3485_;
v___y_3469_ = v___y_3487_;
v___y_3470_ = v___y_3488_;
v___y_3471_ = v___y_3489_;
v___y_3472_ = v___y_3490_;
goto v___jp_3464_;
}
else
{
lean_object* v___x_3514_; 
v___x_3514_ = l_Lean_Meta_Grind_updateLastTag(v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v___x_3515_; 
lean_dec_ref_known(v___x_3514_, 1);
lean_inc(v___y_3490_);
lean_inc_ref(v___y_3489_);
lean_inc(v___y_3488_);
lean_inc_ref(v___y_3487_);
lean_inc(v_val_3510_);
v___x_3515_ = lean_infer_type(v_val_3510_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3515_, 1);
v___x_3517_ = l_Lean_MessageData_ofExpr(v_a_3516_);
v___x_3518_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3479_, v___x_3517_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_dec_ref_known(v___x_3518_, 1);
v___y_3465_ = v_val_3510_;
v___y_3466_ = v___y_3481_;
v___y_3467_ = v___y_3483_;
v___y_3468_ = v___y_3485_;
v___y_3469_ = v___y_3487_;
v___y_3470_ = v___y_3488_;
v___y_3471_ = v___y_3489_;
v___y_3472_ = v___y_3490_;
goto v___jp_3464_;
}
else
{
lean_dec(v_val_3510_);
lean_dec_ref(v_e_3449_);
return v___x_3518_;
}
}
else
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
lean_dec(v_val_3510_);
lean_dec_ref(v_e_3449_);
v_a_3519_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_3515_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3515_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3519_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
else
{
lean_dec(v_val_3510_);
lean_dec_ref(v_e_3449_);
return v___x_3514_;
}
}
}
}
else
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
lean_dec(v_a_3505_);
v___x_3527_ = lean_obj_once(&l_Lean_Meta_Grind_propagateMatchCondUp___closed__1, &l_Lean_Meta_Grind_propagateMatchCondUp___closed__1_once, _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1);
v___x_3528_ = l_Lean_indentExpr(v_e_3449_);
v___x_3529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3527_);
lean_ctor_set(v___x_3529_, 1, v___x_3528_);
v___x_3530_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_3485_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; uint8_t v_verbose_3532_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3530_, 1);
v_verbose_3532_ = lean_ctor_get_uint8(v_a_3531_, 0);
lean_dec(v_a_3531_);
if (v_verbose_3532_ == 0)
{
lean_dec_ref_known(v___x_3529_, 2);
goto v___jp_3461_;
}
else
{
lean_object* v___x_3533_; 
v___x_3533_ = l_Lean_Meta_Sym_reportIssue(v___x_3529_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_dec_ref_known(v___x_3533_, 1);
goto v___jp_3461_;
}
else
{
return v___x_3533_;
}
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_dec_ref_known(v___x_3529_, 2);
v_a_3534_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3530_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3530_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
}
else
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3549_; 
lean_dec_ref(v_e_3449_);
v_a_3542_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3544_ = v___x_3504_;
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3504_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3547_; 
if (v_isShared_3545_ == 0)
{
v___x_3547_ = v___x_3544_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_a_3542_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
}
}
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_dec_ref(v_e_3449_);
v_a_3551_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3494_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3494_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
else
{
lean_object* v___x_3559_; 
lean_inc_ref(v_e_3449_);
v___x_3559_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3449_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3570_; 
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3562_ = v___x_3559_;
v_isShared_3563_ = v_isSharedCheck_3570_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_3559_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3570_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
uint8_t v___x_3564_; 
v___x_3564_ = lean_unbox(v_a_3560_);
lean_dec(v_a_3560_);
if (v___x_3564_ == 0)
{
lean_object* v___x_3565_; 
lean_del_object(v___x_3562_);
v___x_3565_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3449_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
return v___x_3565_;
}
else
{
lean_object* v___x_3566_; lean_object* v___x_3568_; 
lean_dec_ref(v_e_3449_);
v___x_3566_ = lean_box(0);
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 0, v___x_3566_);
v___x_3568_ = v___x_3562_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3566_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
else
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3578_; 
lean_dec_ref(v_e_3449_);
v_a_3571_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3573_ = v___x_3559_;
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3559_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3574_ == 0)
{
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3571_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
}
else
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
lean_dec_ref(v_e_3449_);
v_a_3579_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3581_ = v___x_3491_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3491_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3579_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___boxed(lean_object* v_e_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l_Lean_Meta_Grind_propagateMatchCondUp(v_e_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_);
lean_dec(v_a_3604_);
lean_dec_ref(v_a_3603_);
lean_dec(v_a_3602_);
lean_dec_ref(v_a_3601_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
lean_dec(v_a_3595_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3608_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3609_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondUp___boxed), 12, 0);
v___x_3610_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3608_, v___x_3609_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_9____boxed(lean_object* v_a_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_9_();
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown(lean_object* v_e_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_){
_start:
{
lean_object* v___x_3625_; 
lean_inc_ref(v_e_3613_);
v___x_3625_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3613_, v_a_3614_, v_a_3618_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3655_; 
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3628_ = v___x_3625_;
v_isShared_3629_ = v_isSharedCheck_3655_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3625_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3655_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
uint8_t v___x_3630_; 
v___x_3630_ = lean_unbox(v_a_3626_);
lean_dec(v_a_3626_);
if (v___x_3630_ == 0)
{
lean_object* v___x_3631_; lean_object* v___x_3633_; 
lean_dec_ref(v_e_3613_);
v___x_3631_ = lean_box(0);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 0, v___x_3631_);
v___x_3633_ = v___x_3628_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3631_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
else
{
lean_object* v___x_3635_; 
lean_del_object(v___x_3628_);
lean_inc_ref(v_e_3613_);
v___x_3635_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
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
v___x_3641_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
return v___x_3641_;
}
else
{
lean_object* v___x_3642_; lean_object* v___x_3644_; 
lean_dec_ref(v_e_3613_);
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
lean_dec_ref(v_e_3613_);
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
}
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
lean_dec_ref(v_e_3613_);
v_a_3656_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___x_3625_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3625_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___boxed(lean_object* v_e_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l_Lean_Meta_Grind_propagateMatchCondDown(v_e_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
lean_dec(v_a_3674_);
lean_dec_ref(v_a_3673_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
lean_dec(v_a_3670_);
lean_dec_ref(v_a_3669_);
lean_dec(v_a_3668_);
lean_dec_ref(v_a_3667_);
lean_dec(v_a_3666_);
lean_dec(v_a_3665_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3678_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3679_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondDown___boxed), 12, 0);
v___x_3680_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3678_, v___x_3679_);
return v___x_3680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_9____boxed(lean_object* v_a_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_9_();
return v_res_3682_;
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
