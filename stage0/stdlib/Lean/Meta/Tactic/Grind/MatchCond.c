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
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_proveEq_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_proveHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "proveFalse"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_0),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_1),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(181, 170, 56, 23, 185, 62, 169, 45)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(234, 57, 131, 114, 246, 81, 253, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " =\?= "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_tryToProveFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value)} };
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8____boxed(lean_object*);
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
v___x_170_ = lean_array_fget_borrowed(v_xs_160_, v_i_163_);
v___x_171_ = lean_box(0);
v___x_172_ = lean_array_get_borrowed(v___x_171_, v_tys_161_, v_i_163_);
lean_inc(v___x_172_);
lean_inc(v___x_170_);
lean_inc_ref(v_binderType_165_);
v___x_173_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f(v_binderType_165_, v___x_170_, v___x_172_);
if (lean_obj_tag(v___x_173_) == 1)
{
lean_object* v_val_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___y_179_; size_t v___x_183_; size_t v___x_184_; uint8_t v___x_185_; 
v_val_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_val_174_);
lean_dec_ref_known(v___x_173_, 1);
v___x_175_ = lean_unsigned_to_nat(1u);
v___x_176_ = lean_nat_add(v_i_163_, v___x_175_);
lean_inc_ref(v_body_166_);
v___x_177_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_160_, v_tys_161_, v_body_166_, v___x_176_);
lean_dec(v___x_176_);
v___x_183_ = lean_ptr_addr(v_binderType_165_);
v___x_184_ = lean_ptr_addr(v_val_174_);
v___x_185_ = lean_usize_dec_eq(v___x_183_, v___x_184_);
if (v___x_185_ == 0)
{
v___y_179_ = v___x_185_;
goto v___jp_178_;
}
else
{
size_t v___x_186_; size_t v___x_187_; uint8_t v___x_188_; 
v___x_186_ = lean_ptr_addr(v_body_166_);
v___x_187_ = lean_ptr_addr(v___x_177_);
v___x_188_ = lean_usize_dec_eq(v___x_186_, v___x_187_);
v___y_179_ = v___x_188_;
goto v___jp_178_;
}
v___jp_178_:
{
if (v___y_179_ == 0)
{
lean_object* v___x_180_; 
lean_inc(v_binderName_164_);
lean_dec_ref_known(v_e_162_, 3);
v___x_180_ = l_Lean_Expr_forallE___override(v_binderName_164_, v_val_174_, v___x_177_, v_binderInfo_167_);
return v___x_180_;
}
else
{
uint8_t v___x_181_; 
v___x_181_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_167_, v_binderInfo_167_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
lean_inc(v_binderName_164_);
lean_dec_ref_known(v_e_162_, 3);
v___x_182_ = l_Lean_Expr_forallE___override(v_binderName_164_, v_val_174_, v___x_177_, v_binderInfo_167_);
return v___x_182_;
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
lean_object* v___x_189_; uint8_t v___y_191_; size_t v___x_195_; uint8_t v___x_196_; 
lean_dec(v___x_173_);
lean_inc_ref(v_body_166_);
v___x_189_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_160_, v_tys_161_, v_body_166_, v_i_163_);
v___x_195_ = lean_ptr_addr(v_binderType_165_);
v___x_196_ = lean_usize_dec_eq(v___x_195_, v___x_195_);
if (v___x_196_ == 0)
{
v___y_191_ = v___x_196_;
goto v___jp_190_;
}
else
{
size_t v___x_197_; size_t v___x_198_; uint8_t v___x_199_; 
v___x_197_ = lean_ptr_addr(v_body_166_);
v___x_198_ = lean_ptr_addr(v___x_189_);
v___x_199_ = lean_usize_dec_eq(v___x_197_, v___x_198_);
v___y_191_ = v___x_199_;
goto v___jp_190_;
}
v___jp_190_:
{
if (v___y_191_ == 0)
{
lean_object* v___x_192_; 
lean_inc_ref(v_binderType_165_);
lean_inc(v_binderName_164_);
lean_dec_ref_known(v_e_162_, 3);
v___x_192_ = l_Lean_Expr_forallE___override(v_binderName_164_, v_binderType_165_, v___x_189_, v_binderInfo_167_);
return v___x_192_;
}
else
{
uint8_t v___x_193_; 
v___x_193_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_167_, v_binderInfo_167_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
lean_inc_ref(v_binderType_165_);
lean_inc(v_binderName_164_);
lean_dec_ref_known(v_e_162_, 3);
v___x_194_ = l_Lean_Expr_forallE___override(v_binderName_164_, v_binderType_165_, v___x_189_, v_binderInfo_167_);
return v___x_194_;
}
else
{
lean_dec_ref(v___x_189_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss___boxed(lean_object* v_xs_200_, lean_object* v_tys_201_, lean_object* v_e_202_, lean_object* v_i_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_200_, v_tys_201_, v_e_202_, v_i_203_);
lean_dec(v_i_203_);
lean_dec_ref(v_tys_201_);
lean_dec_ref(v_xs_200_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0(lean_object* v_k_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v_b_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v___x_218_; 
lean_inc(v___y_216_);
lean_inc_ref(v___y_215_);
lean_inc(v___y_214_);
lean_inc_ref(v___y_213_);
lean_inc(v___y_211_);
lean_inc_ref(v___y_210_);
lean_inc(v___y_209_);
lean_inc_ref(v___y_208_);
lean_inc(v___y_207_);
lean_inc(v___y_206_);
v___x_218_ = lean_apply_12(v_k_205_, v_b_212_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, lean_box(0));
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v_b_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0(v_k_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v_b_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec(v___y_220_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(lean_object* v_name_233_, uint8_t v_bi_234_, lean_object* v_type_235_, lean_object* v_k_236_, uint8_t v_kind_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v___f_249_; lean_object* v___x_250_; 
lean_inc(v___y_243_);
lean_inc_ref(v___y_242_);
lean_inc(v___y_241_);
lean_inc_ref(v___y_240_);
lean_inc(v___y_239_);
lean_inc(v___y_238_);
v___f_249_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_249_, 0, v_k_236_);
lean_closure_set(v___f_249_, 1, v___y_238_);
lean_closure_set(v___f_249_, 2, v___y_239_);
lean_closure_set(v___f_249_, 3, v___y_240_);
lean_closure_set(v___f_249_, 4, v___y_241_);
lean_closure_set(v___f_249_, 5, v___y_242_);
lean_closure_set(v___f_249_, 6, v___y_243_);
v___x_250_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_233_, v_bi_234_, v_type_235_, v___f_249_, v_kind_237_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
if (lean_obj_tag(v___x_250_) == 0)
{
return v___x_250_;
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_250_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___boxed(lean_object* v_name_259_, lean_object* v_bi_260_, lean_object* v_type_261_, lean_object* v_k_262_, lean_object* v_kind_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
uint8_t v_bi_boxed_275_; uint8_t v_kind_boxed_276_; lean_object* v_res_277_; 
v_bi_boxed_275_ = lean_unbox(v_bi_260_);
v_kind_boxed_276_ = lean_unbox(v_kind_263_);
v_res_277_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_259_, v_bi_boxed_275_, v_type_261_, v_k_262_, v_kind_boxed_276_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec(v___y_264_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(lean_object* v_name_278_, lean_object* v_type_279_, lean_object* v_k_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
uint8_t v___x_292_; uint8_t v___x_293_; lean_object* v___x_294_; 
v___x_292_ = 0;
v___x_293_ = 0;
v___x_294_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_278_, v___x_292_, v_type_279_, v_k_280_, v___x_293_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg___boxed(lean_object* v_name_295_, lean_object* v_type_296_, lean_object* v_k_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v_name_295_, v_type_296_, v_k_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec(v___y_298_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed(lean_object** _args){
lean_object* v_i_313_ = _args[0];
lean_object* v_xs_314_ = _args[1];
lean_object* v_tys_315_ = _args[2];
lean_object* v_tysxs_316_ = _args[3];
lean_object* v_args_317_ = _args[4];
lean_object* v_val_318_ = _args[5];
lean_object* v_fst_319_ = _args[6];
lean_object* v_e_320_ = _args[7];
lean_object* v_lhss_u03b1s_321_ = _args[8];
lean_object* v_ty_322_ = _args[9];
lean_object* v___y_323_ = _args[10];
lean_object* v___y_324_ = _args[11];
lean_object* v___y_325_ = _args[12];
lean_object* v___y_326_ = _args[13];
lean_object* v___y_327_ = _args[14];
lean_object* v___y_328_ = _args[15];
lean_object* v___y_329_ = _args[16];
lean_object* v___y_330_ = _args[17];
lean_object* v___y_331_ = _args[18];
lean_object* v___y_332_ = _args[19];
lean_object* v___y_333_ = _args[20];
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(v_i_313_, v_xs_314_, v_tys_315_, v_tysxs_316_, v_args_317_, v_val_318_, v_fst_319_, v_e_320_, v_lhss_u03b1s_321_, v_ty_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec(v___y_323_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(lean_object* v_i_338_, lean_object* v_xs_339_, lean_object* v_tys_340_, lean_object* v_tysxs_341_, lean_object* v_args_342_, lean_object* v_fst_343_, lean_object* v_e_344_, lean_object* v_lhss_u03b1s_345_, lean_object* v_x_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_359_ = lean_nat_add(v_i_338_, v___x_358_);
lean_inc_ref(v_x_346_);
v___x_360_ = lean_array_push(v_xs_339_, v_x_346_);
v___x_361_ = lean_box(0);
v___x_362_ = lean_array_push(v_tys_340_, v___x_361_);
v___x_363_ = lean_array_push(v_tysxs_341_, v_x_346_);
v___x_364_ = lean_array_push(v_args_342_, v_fst_343_);
v___x_365_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_344_, v_lhss_u03b1s_345_, v___x_359_, v___x_360_, v___x_362_, v___x_363_, v___x_364_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed(lean_object** _args){
lean_object* v_i_366_ = _args[0];
lean_object* v_xs_367_ = _args[1];
lean_object* v_tys_368_ = _args[2];
lean_object* v_tysxs_369_ = _args[3];
lean_object* v_args_370_ = _args[4];
lean_object* v_fst_371_ = _args[5];
lean_object* v_e_372_ = _args[6];
lean_object* v_lhss_u03b1s_373_ = _args[7];
lean_object* v_x_374_ = _args[8];
lean_object* v___y_375_ = _args[9];
lean_object* v___y_376_ = _args[10];
lean_object* v___y_377_ = _args[11];
lean_object* v___y_378_ = _args[12];
lean_object* v___y_379_ = _args[13];
lean_object* v___y_380_ = _args[14];
lean_object* v___y_381_ = _args[15];
lean_object* v___y_382_ = _args[16];
lean_object* v___y_383_ = _args[17];
lean_object* v___y_384_ = _args[18];
lean_object* v___y_385_ = _args[19];
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(v_i_366_, v_xs_367_, v_tys_368_, v_tysxs_369_, v_args_370_, v_fst_371_, v_e_372_, v_lhss_u03b1s_373_, v_x_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec(v___y_375_);
lean_dec(v_i_366_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(lean_object* v_e_387_, lean_object* v_lhss_u03b1s_388_, lean_object* v_i_389_, lean_object* v_xs_390_, lean_object* v_tys_391_, lean_object* v_tysxs_392_, lean_object* v_args_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_405_ = lean_array_get_size(v_lhss_u03b1s_388_);
v___x_406_ = lean_nat_dec_lt(v_i_389_, v___x_405_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; lean_object* v_eAbst_408_; uint8_t v___x_409_; uint8_t v___x_410_; lean_object* v___x_411_; 
lean_dec(v_i_389_);
lean_dec_ref(v_lhss_u03b1s_388_);
v___x_407_ = lean_unsigned_to_nat(0u);
v_eAbst_408_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_390_, v_tys_391_, v_e_387_, v___x_407_);
lean_dec_ref(v_tys_391_);
lean_dec_ref(v_xs_390_);
v___x_409_ = 1;
v___x_410_ = 1;
v___x_411_ = l_Lean_Meta_mkLambdaFVars(v_tysxs_392_, v_eAbst_408_, v___x_406_, v___x_409_, v___x_406_, v___x_409_, v___x_410_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
lean_dec_ref(v_tysxs_392_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref_known(v___x_411_, 1);
v___x_413_ = l_Lean_mkAppN(v_a_412_, v_args_393_);
v___x_414_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_413_, v_a_399_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_423_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_423_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v_args_393_);
lean_ctor_set(v___x_419_, 1, v_a_415_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_419_);
v___x_421_ = v___x_417_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_dec_ref(v_args_393_);
v_a_424_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_414_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_414_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
lean_dec_ref(v_args_393_);
v_a_432_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_411_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_411_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
else
{
lean_object* v___x_440_; lean_object* v_snd_441_; 
v___x_440_ = lean_array_fget_borrowed(v_lhss_u03b1s_388_, v_i_389_);
v_snd_441_ = lean_ctor_get(v___x_440_, 1);
if (lean_obj_tag(v_snd_441_) == 1)
{
lean_object* v_fst_442_; lean_object* v_val_443_; lean_object* v___x_444_; 
v_fst_442_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_fst_442_);
v_val_443_ = lean_ctor_get(v_snd_441_, 0);
lean_inc_n(v_val_443_, 2);
lean_inc(v_a_403_);
lean_inc_ref(v_a_402_);
lean_inc(v_a_401_);
lean_inc_ref(v_a_400_);
v___x_444_ = lean_infer_type(v_val_443_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___f_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref_known(v___x_444_, 1);
lean_inc(v_i_389_);
v___f_446_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed), 21, 9);
lean_closure_set(v___f_446_, 0, v_i_389_);
lean_closure_set(v___f_446_, 1, v_xs_390_);
lean_closure_set(v___f_446_, 2, v_tys_391_);
lean_closure_set(v___f_446_, 3, v_tysxs_392_);
lean_closure_set(v___f_446_, 4, v_args_393_);
lean_closure_set(v___f_446_, 5, v_val_443_);
lean_closure_set(v___f_446_, 6, v_fst_442_);
lean_closure_set(v___f_446_, 7, v_e_387_);
lean_closure_set(v___f_446_, 8, v_lhss_u03b1s_388_);
v___x_447_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__1));
v___x_448_ = lean_name_append_index_after(v___x_447_, v_i_389_);
v___x_449_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v___x_448_, v_a_445_, v___f_446_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
return v___x_449_;
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_dec(v_val_443_);
lean_dec(v_fst_442_);
lean_dec_ref(v_args_393_);
lean_dec_ref(v_tysxs_392_);
lean_dec_ref(v_tys_391_);
lean_dec_ref(v_xs_390_);
lean_dec(v_i_389_);
lean_dec_ref(v_lhss_u03b1s_388_);
lean_dec_ref(v_e_387_);
v_a_450_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_444_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_444_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
else
{
lean_object* v_fst_458_; lean_object* v___x_459_; 
v_fst_458_ = lean_ctor_get(v___x_440_, 0);
lean_inc_n(v_fst_458_, 2);
lean_inc(v_a_403_);
lean_inc_ref(v_a_402_);
lean_inc(v_a_401_);
lean_inc_ref(v_a_400_);
v___x_459_ = lean_infer_type(v_fst_458_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___f_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_460_);
lean_dec_ref_known(v___x_459_, 1);
lean_inc(v_i_389_);
v___f_461_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed), 20, 8);
lean_closure_set(v___f_461_, 0, v_i_389_);
lean_closure_set(v___f_461_, 1, v_xs_390_);
lean_closure_set(v___f_461_, 2, v_tys_391_);
lean_closure_set(v___f_461_, 3, v_tysxs_392_);
lean_closure_set(v___f_461_, 4, v_args_393_);
lean_closure_set(v___f_461_, 5, v_fst_458_);
lean_closure_set(v___f_461_, 6, v_e_387_);
lean_closure_set(v___f_461_, 7, v_lhss_u03b1s_388_);
v___x_462_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1));
v___x_463_ = lean_name_append_index_after(v___x_462_, v_i_389_);
v___x_464_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v___x_463_, v_a_460_, v___f_461_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
return v___x_464_;
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec(v_fst_458_);
lean_dec_ref(v_args_393_);
lean_dec_ref(v_tysxs_392_);
lean_dec_ref(v_tys_391_);
lean_dec_ref(v_xs_390_);
lean_dec(v_i_389_);
lean_dec_ref(v_lhss_u03b1s_388_);
lean_dec_ref(v_e_387_);
v_a_465_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_459_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_459_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(lean_object* v_i_473_, lean_object* v_xs_474_, lean_object* v_ty_475_, lean_object* v_tys_476_, lean_object* v_tysxs_477_, lean_object* v_args_478_, lean_object* v_val_479_, lean_object* v_fst_480_, lean_object* v_e_481_, lean_object* v_lhss_u03b1s_482_, lean_object* v_x_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_495_ = lean_unsigned_to_nat(1u);
v___x_496_ = lean_nat_add(v_i_473_, v___x_495_);
lean_inc_ref(v_x_483_);
v___x_497_ = lean_array_push(v_xs_474_, v_x_483_);
lean_inc_ref(v_ty_475_);
v___x_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_498_, 0, v_ty_475_);
v___x_499_ = lean_array_push(v_tys_476_, v___x_498_);
v___x_500_ = lean_array_push(v_tysxs_477_, v_ty_475_);
v___x_501_ = lean_array_push(v___x_500_, v_x_483_);
v___x_502_ = lean_array_push(v_args_478_, v_val_479_);
v___x_503_ = lean_array_push(v___x_502_, v_fst_480_);
v___x_504_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_481_, v_lhss_u03b1s_482_, v___x_496_, v___x_497_, v___x_499_, v___x_501_, v___x_503_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0___boxed(lean_object** _args){
lean_object* v_i_505_ = _args[0];
lean_object* v_xs_506_ = _args[1];
lean_object* v_ty_507_ = _args[2];
lean_object* v_tys_508_ = _args[3];
lean_object* v_tysxs_509_ = _args[4];
lean_object* v_args_510_ = _args[5];
lean_object* v_val_511_ = _args[6];
lean_object* v_fst_512_ = _args[7];
lean_object* v_e_513_ = _args[8];
lean_object* v_lhss_u03b1s_514_ = _args[9];
lean_object* v_x_515_ = _args[10];
lean_object* v___y_516_ = _args[11];
lean_object* v___y_517_ = _args[12];
lean_object* v___y_518_ = _args[13];
lean_object* v___y_519_ = _args[14];
lean_object* v___y_520_ = _args[15];
lean_object* v___y_521_ = _args[16];
lean_object* v___y_522_ = _args[17];
lean_object* v___y_523_ = _args[18];
lean_object* v___y_524_ = _args[19];
lean_object* v___y_525_ = _args[20];
lean_object* v___y_526_ = _args[21];
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(v_i_505_, v_xs_506_, v_ty_507_, v_tys_508_, v_tysxs_509_, v_args_510_, v_val_511_, v_fst_512_, v_e_513_, v_lhss_u03b1s_514_, v_x_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec(v___y_516_);
lean_dec(v_i_505_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(lean_object* v_i_528_, lean_object* v_xs_529_, lean_object* v_tys_530_, lean_object* v_tysxs_531_, lean_object* v_args_532_, lean_object* v_val_533_, lean_object* v_fst_534_, lean_object* v_e_535_, lean_object* v_lhss_u03b1s_536_, lean_object* v_ty_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v___f_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
lean_inc_ref(v_ty_537_);
lean_inc(v_i_528_);
v___f_549_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0___boxed), 22, 10);
lean_closure_set(v___f_549_, 0, v_i_528_);
lean_closure_set(v___f_549_, 1, v_xs_529_);
lean_closure_set(v___f_549_, 2, v_ty_537_);
lean_closure_set(v___f_549_, 3, v_tys_530_);
lean_closure_set(v___f_549_, 4, v_tysxs_531_);
lean_closure_set(v___f_549_, 5, v_args_532_);
lean_closure_set(v___f_549_, 6, v_val_533_);
lean_closure_set(v___f_549_, 7, v_fst_534_);
lean_closure_set(v___f_549_, 8, v_e_535_);
lean_closure_set(v___f_549_, 9, v_lhss_u03b1s_536_);
v___x_550_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1));
v___x_551_ = lean_name_append_index_after(v___x_550_, v_i_528_);
v___x_552_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v___x_551_, v_ty_537_, v___f_549_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___boxed(lean_object** _args){
lean_object* v_e_553_ = _args[0];
lean_object* v_lhss_u03b1s_554_ = _args[1];
lean_object* v_i_555_ = _args[2];
lean_object* v_xs_556_ = _args[3];
lean_object* v_tys_557_ = _args[4];
lean_object* v_tysxs_558_ = _args[5];
lean_object* v_args_559_ = _args[6];
lean_object* v_a_560_ = _args[7];
lean_object* v_a_561_ = _args[8];
lean_object* v_a_562_ = _args[9];
lean_object* v_a_563_ = _args[10];
lean_object* v_a_564_ = _args[11];
lean_object* v_a_565_ = _args[12];
lean_object* v_a_566_ = _args[13];
lean_object* v_a_567_ = _args[14];
lean_object* v_a_568_ = _args[15];
lean_object* v_a_569_ = _args[16];
lean_object* v_a_570_ = _args[17];
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_553_, v_lhss_u03b1s_554_, v_i_555_, v_xs_556_, v_tys_557_, v_tysxs_558_, v_args_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec(v_a_560_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0(lean_object* v_00_u03b1_572_, lean_object* v_name_573_, uint8_t v_bi_574_, lean_object* v_type_575_, lean_object* v_k_576_, uint8_t v_kind_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_573_, v_bi_574_, v_type_575_, v_k_576_, v_kind_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_590_ = _args[0];
lean_object* v_name_591_ = _args[1];
lean_object* v_bi_592_ = _args[2];
lean_object* v_type_593_ = _args[3];
lean_object* v_k_594_ = _args[4];
lean_object* v_kind_595_ = _args[5];
lean_object* v___y_596_ = _args[6];
lean_object* v___y_597_ = _args[7];
lean_object* v___y_598_ = _args[8];
lean_object* v___y_599_ = _args[9];
lean_object* v___y_600_ = _args[10];
lean_object* v___y_601_ = _args[11];
lean_object* v___y_602_ = _args[12];
lean_object* v___y_603_ = _args[13];
lean_object* v___y_604_ = _args[14];
lean_object* v___y_605_ = _args[15];
lean_object* v___y_606_ = _args[16];
_start:
{
uint8_t v_bi_boxed_607_; uint8_t v_kind_boxed_608_; lean_object* v_res_609_; 
v_bi_boxed_607_ = lean_unbox(v_bi_592_);
v_kind_boxed_608_ = lean_unbox(v_kind_595_);
v_res_609_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0(v_00_u03b1_590_, v_name_591_, v_bi_boxed_607_, v_type_593_, v_k_594_, v_kind_boxed_608_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec(v___y_596_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0(lean_object* v_00_u03b1_610_, lean_object* v_name_611_, lean_object* v_type_612_, lean_object* v_k_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v_name_611_, v_type_612_, v_k_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___boxed(lean_object* v_00_u03b1_626_, lean_object* v_name_627_, lean_object* v_type_628_, lean_object* v_k_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0(v_00_u03b1_626_, v_name_627_, v_type_628_, v_k_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec(v___y_630_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter___redArg(lean_object* v_x_642_, lean_object* v_h__1_643_){
_start:
{
lean_object* v_fst_644_; lean_object* v_snd_645_; lean_object* v___x_646_; 
v_fst_644_ = lean_ctor_get(v_x_642_, 0);
lean_inc(v_fst_644_);
v_snd_645_ = lean_ctor_get(v_x_642_, 1);
lean_inc(v_snd_645_);
lean_dec_ref(v_x_642_);
v___x_646_ = lean_apply_2(v_h__1_643_, v_fst_644_, v_snd_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter(lean_object* v_motive_647_, lean_object* v_x_648_, lean_object* v_h__1_649_){
_start:
{
lean_object* v_fst_650_; lean_object* v_snd_651_; lean_object* v___x_652_; 
v_fst_650_ = lean_ctor_get(v_x_648_, 0);
lean_inc(v_fst_650_);
v_snd_651_ = lean_ctor_get(v_x_648_, 1);
lean_inc(v_snd_651_);
lean_dec_ref(v_x_648_);
v___x_652_ = lean_apply_2(v_h__1_649_, v_fst_650_, v_snd_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter___redArg(lean_object* v_00_u03b1_x3f_653_, lean_object* v_h__1_654_, lean_object* v_h__2_655_){
_start:
{
if (lean_obj_tag(v_00_u03b1_x3f_653_) == 1)
{
lean_object* v_val_656_; lean_object* v___x_657_; 
lean_dec(v_h__2_655_);
v_val_656_ = lean_ctor_get(v_00_u03b1_x3f_653_, 0);
lean_inc(v_val_656_);
lean_dec_ref_known(v_00_u03b1_x3f_653_, 1);
v___x_657_ = lean_apply_1(v_h__1_654_, v_val_656_);
return v___x_657_;
}
else
{
lean_object* v___x_658_; 
lean_dec(v_h__1_654_);
v___x_658_ = lean_apply_2(v_h__2_655_, v_00_u03b1_x3f_653_, lean_box(0));
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter(lean_object* v_motive_659_, lean_object* v_00_u03b1_x3f_660_, lean_object* v_h__1_661_, lean_object* v_h__2_662_){
_start:
{
if (lean_obj_tag(v_00_u03b1_x3f_660_) == 1)
{
lean_object* v_val_663_; lean_object* v___x_664_; 
lean_dec(v_h__2_662_);
v_val_663_ = lean_ctor_get(v_00_u03b1_x3f_660_, 0);
lean_inc(v_val_663_);
lean_dec_ref_known(v_00_u03b1_x3f_660_, 1);
v___x_664_ = lean_apply_1(v_h__1_661_, v_val_663_);
return v___x_664_;
}
else
{
lean_object* v___x_665_; 
lean_dec(v_h__1_661_);
v___x_665_ = lean_apply_2(v_h__2_662_, v_00_u03b1_x3f_660_, lean_box(0));
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(lean_object* v_matchCond_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v___x_691_; uint8_t v___x_692_; 
lean_inc_ref(v_matchCond_675_);
v___x_691_ = l_Lean_Expr_cleanupAnnotations(v_matchCond_675_);
v___x_692_ = l_Lean_Expr_isApp(v___x_691_);
if (v___x_692_ == 0)
{
lean_dec_ref(v___x_691_);
goto v___jp_687_;
}
else
{
lean_object* v_arg_693_; lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v_arg_693_ = lean_ctor_get(v___x_691_, 1);
lean_inc_ref(v_arg_693_);
v___x_694_ = l_Lean_Expr_appFnCleanup___redArg(v___x_691_);
v___x_695_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_696_ = l_Lean_Expr_isConstOf(v___x_694_, v___x_695_);
lean_dec_ref(v___x_694_);
if (v___x_696_ == 0)
{
lean_dec_ref(v_arg_693_);
goto v___jp_687_;
}
else
{
lean_object* v_lhss_u03b1s_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
lean_dec_ref(v_matchCond_675_);
lean_inc_ref(v_arg_693_);
v_lhss_u03b1s_697_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss(v_arg_693_);
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0));
v___x_700_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_arg_693_, v_lhss_u03b1s_697_, v___x_698_, v___x_699_, v___x_699_, v___x_699_, v___x_699_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_);
return v___x_700_;
}
}
v___jp_687_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_688_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0));
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v_matchCond_675_);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___boxed(lean_object* v_matchCond_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(v_matchCond_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec(v_a_702_);
return v_res_713_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0(void){
_start:
{
lean_object* v___x_717_; lean_object* v_dummy_718_; 
v___x_717_ = lean_box(0);
v_dummy_718_ = l_Lean_Expr_sort___override(v___x_717_);
return v_dummy_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(lean_object* v_lhs_719_, lean_object* v_rhs_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
uint8_t v___x_732_; 
v___x_732_ = l_Lean_Expr_hasLooseBVars(v_lhs_719_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_Meta_Grind_getRootENode___redArg(v_lhs_719_, v_a_721_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_874_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_874_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_874_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_874_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
uint8_t v_ctor_738_; 
v_ctor_738_ = lean_ctor_get_uint8(v_a_734_, sizeof(void*)*12 + 2);
if (v_ctor_738_ == 0)
{
uint8_t v_interpreted_739_; 
v_interpreted_739_ = lean_ctor_get_uint8(v_a_734_, sizeof(void*)*12 + 1);
if (v_interpreted_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_742_; 
lean_dec(v_a_734_);
lean_dec_ref(v_rhs_720_);
v___x_740_ = lean_box(v_interpreted_739_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_740_);
v___x_742_ = v___x_736_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
else
{
lean_object* v_self_744_; uint8_t v___x_745_; 
v_self_744_ = lean_ctor_get(v_a_734_, 0);
lean_inc_ref(v_self_744_);
lean_dec(v_a_734_);
v___x_745_ = l_Lean_Expr_hasLooseBVars(v_rhs_720_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
lean_del_object(v___x_736_);
lean_inc_ref(v_rhs_720_);
v___x_746_ = l_Lean_Meta_isLitValue(v_rhs_720_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; uint8_t v___x_748_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
v___x_748_ = lean_unbox(v_a_747_);
if (v___x_748_ == 0)
{
lean_dec(v_a_747_);
lean_dec_ref(v_self_744_);
lean_dec_ref(v_rhs_720_);
return v___x_746_;
}
else
{
lean_object* v___x_749_; 
lean_dec_ref_known(v___x_746_, 1);
v___x_749_ = l_Lean_Meta_normLitValue(v_self_744_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_751_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v___x_749_, 1);
v___x_751_ = l_Lean_Meta_normLitValue(v_rhs_720_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_764_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_764_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_764_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_764_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
uint8_t v___x_756_; 
v___x_756_ = lean_expr_eqv(v_a_750_, v_a_752_);
lean_dec(v_a_752_);
lean_dec(v_a_750_);
if (v___x_756_ == 0)
{
lean_object* v___x_758_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v_a_747_);
v___x_758_ = v___x_754_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_747_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
else
{
lean_object* v___x_760_; lean_object* v___x_762_; 
lean_dec(v_a_747_);
v___x_760_ = lean_box(v___x_745_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_760_);
v___x_762_ = v___x_754_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
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
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec(v_a_750_);
lean_dec(v_a_747_);
v_a_765_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_751_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_751_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec(v_a_747_);
lean_dec_ref(v_rhs_720_);
v_a_773_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_749_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_749_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
else
{
lean_dec_ref(v_self_744_);
lean_dec_ref(v_rhs_720_);
return v___x_746_;
}
}
else
{
lean_object* v___x_781_; lean_object* v___x_783_; 
lean_dec_ref(v_self_744_);
lean_dec_ref(v_rhs_720_);
v___x_781_ = lean_box(v_ctor_738_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_781_);
v___x_783_ = v___x_736_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v_self_785_; lean_object* v___x_786_; 
lean_del_object(v___x_736_);
v_self_785_ = lean_ctor_get(v_a_734_, 0);
lean_inc_ref_n(v_self_785_, 2);
lean_dec(v_a_734_);
v___x_786_ = l_Lean_Meta_isConstructorApp_x3f(v_self_785_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_865_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_865_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_865_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_865_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
if (lean_obj_tag(v_a_787_) == 1)
{
lean_object* v_val_791_; lean_object* v___x_792_; 
lean_del_object(v___x_789_);
v_val_791_ = lean_ctor_get(v_a_787_, 0);
lean_inc(v_val_791_);
lean_dec_ref_known(v_a_787_, 1);
lean_inc_ref(v_rhs_720_);
v___x_792_ = l_Lean_Meta_isConstructorApp_x3f(v_rhs_720_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_852_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_852_ == 0)
{
v___x_795_ = v___x_792_;
v_isShared_796_ = v_isSharedCheck_852_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_852_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
if (lean_obj_tag(v_a_793_) == 1)
{
lean_object* v_toConstantVal_797_; lean_object* v_val_798_; lean_object* v_toConstantVal_799_; lean_object* v_numParams_800_; lean_object* v_numFields_801_; lean_object* v_name_802_; lean_object* v_name_803_; uint8_t v___x_804_; 
v_toConstantVal_797_ = lean_ctor_get(v_val_791_, 0);
lean_inc_ref(v_toConstantVal_797_);
v_val_798_ = lean_ctor_get(v_a_793_, 0);
lean_inc(v_val_798_);
lean_dec_ref_known(v_a_793_, 1);
v_toConstantVal_799_ = lean_ctor_get(v_val_798_, 0);
lean_inc_ref(v_toConstantVal_799_);
lean_dec(v_val_798_);
v_numParams_800_ = lean_ctor_get(v_val_791_, 3);
lean_inc(v_numParams_800_);
v_numFields_801_ = lean_ctor_get(v_val_791_, 4);
lean_inc(v_numFields_801_);
lean_dec(v_val_791_);
v_name_802_ = lean_ctor_get(v_toConstantVal_797_, 0);
lean_inc(v_name_802_);
lean_dec_ref(v_toConstantVal_797_);
v_name_803_ = lean_ctor_get(v_toConstantVal_799_, 0);
lean_inc(v_name_803_);
lean_dec_ref(v_toConstantVal_799_);
v___x_804_ = lean_name_eq(v_name_802_, v_name_803_);
lean_dec(v_name_803_);
lean_dec(v_name_802_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_807_; 
lean_dec(v_numFields_801_);
lean_dec(v_numParams_800_);
lean_dec_ref(v_self_785_);
lean_dec_ref(v_rhs_720_);
v___x_805_ = lean_box(v_ctor_738_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_805_);
v___x_807_ = v___x_795_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
else
{
if (v___x_732_ == 0)
{
lean_object* v_nargs_809_; lean_object* v_nargs_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v_dummy_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
lean_del_object(v___x_795_);
v_nargs_809_ = l_Lean_Expr_getAppNumArgs(v_self_785_);
v_nargs_810_ = l_Lean_Expr_getAppNumArgs(v_rhs_720_);
v___x_811_ = lean_nat_add(v_numParams_800_, v_numFields_801_);
lean_dec(v_numFields_801_);
v___x_812_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0));
v_dummy_813_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0);
lean_inc(v_nargs_809_);
v___x_814_ = lean_mk_array(v_nargs_809_, v_dummy_813_);
v___x_815_ = lean_unsigned_to_nat(1u);
v___x_816_ = lean_nat_sub(v_nargs_809_, v___x_815_);
lean_dec(v_nargs_809_);
v___x_817_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_785_, v___x_814_, v___x_816_);
lean_inc(v_nargs_810_);
v___x_818_ = lean_mk_array(v_nargs_810_, v_dummy_813_);
v___x_819_ = lean_nat_sub(v_nargs_810_, v___x_815_);
lean_dec(v_nargs_810_);
v___x_820_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_rhs_720_, v___x_818_, v___x_819_);
v___x_821_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v___x_811_, v___x_817_, v___x_820_, v_ctor_738_, v_numParams_800_, v___x_812_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
lean_dec_ref(v___x_820_);
lean_dec_ref(v___x_817_);
lean_dec(v___x_811_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_835_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_835_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_835_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_835_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_fst_826_; 
v_fst_826_ = lean_ctor_get(v_a_822_, 0);
lean_inc(v_fst_826_);
lean_dec(v_a_822_);
if (lean_obj_tag(v_fst_826_) == 0)
{
lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_827_ = lean_box(v___x_732_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_827_);
v___x_829_ = v___x_824_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
else
{
lean_object* v_val_831_; lean_object* v___x_833_; 
v_val_831_ = lean_ctor_get(v_fst_826_, 0);
lean_inc(v_val_831_);
lean_dec_ref_known(v_fst_826_, 1);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v_val_831_);
v___x_833_ = v___x_824_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_val_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
v_a_836_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_821_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_821_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
else
{
lean_object* v___x_844_; lean_object* v___x_846_; 
lean_dec(v_numFields_801_);
lean_dec(v_numParams_800_);
lean_dec_ref(v_self_785_);
lean_dec_ref(v_rhs_720_);
v___x_844_ = lean_box(v_ctor_738_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_844_);
v___x_846_ = v___x_795_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
else
{
lean_object* v___x_848_; lean_object* v___x_850_; 
lean_dec(v_a_793_);
lean_dec(v_val_791_);
lean_dec_ref(v_self_785_);
lean_dec_ref(v_rhs_720_);
v___x_848_ = lean_box(v___x_732_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_848_);
v___x_850_ = v___x_795_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
lean_dec(v_val_791_);
lean_dec_ref(v_self_785_);
lean_dec_ref(v_rhs_720_);
v_a_853_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_792_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_792_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
else
{
lean_object* v___x_861_; lean_object* v___x_863_; 
lean_dec(v_a_787_);
lean_dec_ref(v_self_785_);
lean_dec_ref(v_rhs_720_);
v___x_861_ = lean_box(v___x_732_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_861_);
v___x_863_ = v___x_789_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec_ref(v_self_785_);
lean_dec_ref(v_rhs_720_);
v_a_866_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_786_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_786_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec_ref(v_rhs_720_);
v_a_875_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_733_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_733_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
uint8_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
lean_dec_ref(v_rhs_720_);
lean_dec_ref(v_lhs_719_);
v___x_883_ = 0;
v___x_884_ = lean_box(v___x_883_);
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
return v___x_885_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(lean_object* v_upperBound_886_, lean_object* v___x_887_, lean_object* v___x_888_, uint8_t v___x_889_, lean_object* v_a_890_, lean_object* v_b_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
uint8_t v___x_903_; 
v___x_903_ = lean_nat_dec_lt(v_a_890_, v_upperBound_886_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
lean_dec(v_a_890_);
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v_b_891_);
return v___x_904_;
}
else
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
lean_dec_ref(v_b_891_);
v___x_905_ = l_Lean_instInhabitedExpr;
v___x_906_ = lean_array_get_borrowed(v___x_905_, v___x_887_, v_a_890_);
v___x_907_ = lean_array_get_borrowed(v___x_905_, v___x_888_, v_a_890_);
lean_inc(v___x_907_);
lean_inc(v___x_906_);
v___x_908_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v___x_906_, v___x_907_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_925_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_925_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_925_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_925_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_913_ = lean_box(0);
v___x_914_ = lean_unbox(v_a_909_);
lean_dec(v_a_909_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
lean_del_object(v___x_911_);
v___x_915_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0));
v___x_916_ = lean_unsigned_to_nat(1u);
v___x_917_ = lean_nat_add(v_a_890_, v___x_916_);
lean_dec(v_a_890_);
v_a_890_ = v___x_917_;
v_b_891_ = v___x_915_;
goto _start;
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
lean_dec(v_a_890_);
v___x_919_ = lean_box(v___x_889_);
v___x_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v___x_913_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_921_);
v___x_923_ = v___x_911_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v_a_890_);
v_a_926_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_908_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_908_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_934_ = _args[0];
lean_object* v___x_935_ = _args[1];
lean_object* v___x_936_ = _args[2];
lean_object* v___x_937_ = _args[3];
lean_object* v_a_938_ = _args[4];
lean_object* v_b_939_ = _args[5];
lean_object* v___y_940_ = _args[6];
lean_object* v___y_941_ = _args[7];
lean_object* v___y_942_ = _args[8];
lean_object* v___y_943_ = _args[9];
lean_object* v___y_944_ = _args[10];
lean_object* v___y_945_ = _args[11];
lean_object* v___y_946_ = _args[12];
lean_object* v___y_947_ = _args[13];
lean_object* v___y_948_ = _args[14];
lean_object* v___y_949_ = _args[15];
lean_object* v___y_950_ = _args[16];
_start:
{
uint8_t v___x_28909__boxed_951_; lean_object* v_res_952_; 
v___x_28909__boxed_951_ = lean_unbox(v___x_937_);
v_res_952_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v_upperBound_934_, v___x_935_, v___x_936_, v___x_28909__boxed_951_, v_a_938_, v_b_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v___x_935_);
lean_dec(v_upperBound_934_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___boxed(lean_object* v_lhs_953_, lean_object* v_rhs_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v_lhs_953_, v_rhs_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec(v_a_955_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(lean_object* v_upperBound_967_, lean_object* v___x_968_, lean_object* v___x_969_, uint8_t v___x_970_, lean_object* v_inst_971_, lean_object* v_R_972_, lean_object* v_a_973_, lean_object* v_b_974_, lean_object* v_c_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v_upperBound_967_, v___x_968_, v___x_969_, v___x_970_, v_a_973_, v_b_974_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_988_ = _args[0];
lean_object* v___x_989_ = _args[1];
lean_object* v___x_990_ = _args[2];
lean_object* v___x_991_ = _args[3];
lean_object* v_inst_992_ = _args[4];
lean_object* v_R_993_ = _args[5];
lean_object* v_a_994_ = _args[6];
lean_object* v_b_995_ = _args[7];
lean_object* v_c_996_ = _args[8];
lean_object* v___y_997_ = _args[9];
lean_object* v___y_998_ = _args[10];
lean_object* v___y_999_ = _args[11];
lean_object* v___y_1000_ = _args[12];
lean_object* v___y_1001_ = _args[13];
lean_object* v___y_1002_ = _args[14];
lean_object* v___y_1003_ = _args[15];
lean_object* v___y_1004_ = _args[16];
lean_object* v___y_1005_ = _args[17];
lean_object* v___y_1006_ = _args[18];
lean_object* v___y_1007_ = _args[19];
_start:
{
uint8_t v___x_29305__boxed_1008_; lean_object* v_res_1009_; 
v___x_29305__boxed_1008_ = lean_unbox(v___x_991_);
v_res_1009_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(v_upperBound_988_, v___x_989_, v___x_990_, v___x_29305__boxed_1008_, v_inst_992_, v_R_993_, v_a_994_, v_b_995_, v_c_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___x_990_);
lean_dec_ref(v___x_989_);
lean_dec(v_upperBound_988_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(lean_object* v_e_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_e_1010_);
if (lean_obj_tag(v___x_1022_) == 1)
{
lean_object* v_val_1023_; lean_object* v_snd_1024_; lean_object* v_fst_1025_; lean_object* v_snd_1026_; lean_object* v___x_1027_; 
v_val_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_val_1023_);
lean_dec_ref_known(v___x_1022_, 1);
v_snd_1024_ = lean_ctor_get(v_val_1023_, 1);
lean_inc(v_snd_1024_);
lean_dec(v_val_1023_);
v_fst_1025_ = lean_ctor_get(v_snd_1024_, 0);
lean_inc(v_fst_1025_);
v_snd_1026_ = lean_ctor_get(v_snd_1024_, 1);
lean_inc(v_snd_1026_);
lean_dec(v_snd_1024_);
v___x_1027_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v_fst_1025_, v_snd_1026_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
return v___x_1027_;
}
else
{
uint8_t v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
lean_dec(v___x_1022_);
v___x_1028_ = 0;
v___x_1029_ = lean_box(v___x_1028_);
v___x_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
return v___x_1030_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp___boxed(lean_object* v_e_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_e_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec(v_a_1032_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(uint8_t v___x_1044_, lean_object* v_snd_1045_, lean_object* v_____r_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1058_ = lean_box(v___x_1044_);
v___x_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v_snd_1045_);
v___x_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0___boxed(lean_object* v___x_1063_, lean_object* v_snd_1064_, lean_object* v_____r_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
uint8_t v___x_32248__boxed_1077_; lean_object* v_res_1078_; 
v___x_32248__boxed_1077_ = lean_unbox(v___x_1063_);
v_res_1078_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_32248__boxed_1077_, v_snd_1064_, v_____r_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec(v___y_1066_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(lean_object* v_msgData_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v___x_1085_; lean_object* v_env_1086_; lean_object* v___x_1087_; lean_object* v_mctx_1088_; lean_object* v_lctx_1089_; lean_object* v_options_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1085_ = lean_st_ref_get(v___y_1083_);
v_env_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc_ref(v_env_1086_);
lean_dec(v___x_1085_);
v___x_1087_ = lean_st_ref_get(v___y_1081_);
v_mctx_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc_ref(v_mctx_1088_);
lean_dec(v___x_1087_);
v_lctx_1089_ = lean_ctor_get(v___y_1080_, 2);
v_options_1090_ = lean_ctor_get(v___y_1082_, 2);
lean_inc_ref(v_options_1090_);
lean_inc_ref(v_lctx_1089_);
v___x_1091_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1091_, 0, v_env_1086_);
lean_ctor_set(v___x_1091_, 1, v_mctx_1088_);
lean_ctor_set(v___x_1091_, 2, v_lctx_1089_);
lean_ctor_set(v___x_1091_, 3, v_options_1090_);
v___x_1092_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
lean_ctor_set(v___x_1092_, 1, v_msgData_1079_);
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0___boxed(lean_object* v_msgData_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(v_msgData_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
return v_res_1100_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1101_; double v___x_1102_; 
v___x_1101_ = lean_unsigned_to_nat(0u);
v___x_1102_ = lean_float_of_nat(v___x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(lean_object* v_cls_1106_, lean_object* v_msg_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_ref_1113_; lean_object* v___x_1114_; lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1159_; 
v_ref_1113_ = lean_ctor_get(v___y_1110_, 5);
v___x_1114_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(v_msg_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1159_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1159_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v_traceState_1120_; lean_object* v_env_1121_; lean_object* v_nextMacroScope_1122_; lean_object* v_ngen_1123_; lean_object* v_auxDeclNGen_1124_; lean_object* v_cache_1125_; lean_object* v_messages_1126_; lean_object* v_infoState_1127_; lean_object* v_snapshotTasks_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1158_; 
v___x_1119_ = lean_st_ref_take(v___y_1111_);
v_traceState_1120_ = lean_ctor_get(v___x_1119_, 4);
v_env_1121_ = lean_ctor_get(v___x_1119_, 0);
v_nextMacroScope_1122_ = lean_ctor_get(v___x_1119_, 1);
v_ngen_1123_ = lean_ctor_get(v___x_1119_, 2);
v_auxDeclNGen_1124_ = lean_ctor_get(v___x_1119_, 3);
v_cache_1125_ = lean_ctor_get(v___x_1119_, 5);
v_messages_1126_ = lean_ctor_get(v___x_1119_, 6);
v_infoState_1127_ = lean_ctor_get(v___x_1119_, 7);
v_snapshotTasks_1128_ = lean_ctor_get(v___x_1119_, 8);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1130_ = v___x_1119_;
v_isShared_1131_ = v_isSharedCheck_1158_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_snapshotTasks_1128_);
lean_inc(v_infoState_1127_);
lean_inc(v_messages_1126_);
lean_inc(v_cache_1125_);
lean_inc(v_traceState_1120_);
lean_inc(v_auxDeclNGen_1124_);
lean_inc(v_ngen_1123_);
lean_inc(v_nextMacroScope_1122_);
lean_inc(v_env_1121_);
lean_dec(v___x_1119_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1158_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
uint64_t v_tid_1132_; lean_object* v_traces_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1157_; 
v_tid_1132_ = lean_ctor_get_uint64(v_traceState_1120_, sizeof(void*)*1);
v_traces_1133_ = lean_ctor_get(v_traceState_1120_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_traceState_1120_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1135_ = v_traceState_1120_;
v_isShared_1136_ = v_isSharedCheck_1157_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_traces_1133_);
lean_dec(v_traceState_1120_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1157_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; double v___x_1138_; uint8_t v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1137_ = lean_box(0);
v___x_1138_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0);
v___x_1139_ = 0;
v___x_1140_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1));
v___x_1141_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1141_, 0, v_cls_1106_);
lean_ctor_set(v___x_1141_, 1, v___x_1137_);
lean_ctor_set(v___x_1141_, 2, v___x_1140_);
lean_ctor_set_float(v___x_1141_, sizeof(void*)*3, v___x_1138_);
lean_ctor_set_float(v___x_1141_, sizeof(void*)*3 + 8, v___x_1138_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*3 + 16, v___x_1139_);
v___x_1142_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__2));
v___x_1143_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1141_);
lean_ctor_set(v___x_1143_, 1, v_a_1115_);
lean_ctor_set(v___x_1143_, 2, v___x_1142_);
lean_inc(v_ref_1113_);
v___x_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1144_, 0, v_ref_1113_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = l_Lean_PersistentArray_push___redArg(v_traces_1133_, v___x_1144_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1145_);
v___x_1147_ = v___x_1135_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1145_);
lean_ctor_set_uint64(v_reuseFailAlloc_1156_, sizeof(void*)*1, v_tid_1132_);
v___x_1147_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1149_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 4, v___x_1147_);
v___x_1149_ = v___x_1130_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_env_1121_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_nextMacroScope_1122_);
lean_ctor_set(v_reuseFailAlloc_1155_, 2, v_ngen_1123_);
lean_ctor_set(v_reuseFailAlloc_1155_, 3, v_auxDeclNGen_1124_);
lean_ctor_set(v_reuseFailAlloc_1155_, 4, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1155_, 5, v_cache_1125_);
lean_ctor_set(v_reuseFailAlloc_1155_, 6, v_messages_1126_);
lean_ctor_set(v_reuseFailAlloc_1155_, 7, v_infoState_1127_);
lean_ctor_set(v_reuseFailAlloc_1155_, 8, v_snapshotTasks_1128_);
v___x_1149_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1150_ = lean_st_ref_set(v___y_1111_, v___x_1149_);
v___x_1151_ = lean_box(0);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1151_);
v___x_1153_ = v___x_1117_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___boxed(lean_object* v_cls_1160_, lean_object* v_msg_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1160_, v_msg_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
return v_res_1167_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_1179_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5));
v___x_1180_ = l_Lean_Name_append(v___x_1179_, v___x_1178_);
return v___x_1180_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__7));
v___x_1183_ = l_Lean_stringToMessageData(v___x_1182_);
return v___x_1183_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__9));
v___x_1186_ = l_Lean_stringToMessageData(v___x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(uint8_t v___x_1187_, lean_object* v_a_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___y_1201_; lean_object* v_snd_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1283_; 
v_snd_1221_ = lean_ctor_get(v_a_1188_, 1);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_a_1188_);
if (v_isSharedCheck_1283_ == 0)
{
lean_object* v_unused_1284_; 
v_unused_1284_ = lean_ctor_get(v_a_1188_, 0);
lean_dec(v_unused_1284_);
v___x_1223_ = v_a_1188_;
v_isShared_1224_ = v_isSharedCheck_1283_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_snd_1221_);
lean_dec(v_a_1188_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1283_;
goto v_resetjp_1222_;
}
v___jp_1200_:
{
if (lean_obj_tag(v___y_1201_) == 0)
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1212_; 
v_a_1202_ = lean_ctor_get(v___y_1201_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___y_1201_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1204_ = v___y_1201_;
v_isShared_1205_ = v_isSharedCheck_1212_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___y_1201_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1212_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
if (lean_obj_tag(v_a_1202_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1208_; 
v_a_1206_ = lean_ctor_get(v_a_1202_, 0);
lean_inc(v_a_1206_);
lean_dec_ref_known(v_a_1202_, 1);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v_a_1206_);
v___x_1208_ = v___x_1204_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
else
{
lean_object* v_a_1210_; 
lean_del_object(v___x_1204_);
v_a_1210_ = lean_ctor_get(v_a_1202_, 0);
lean_inc(v_a_1210_);
lean_dec_ref_known(v_a_1202_, 1);
v_a_1188_ = v_a_1210_;
goto _start;
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
v_a_1213_ = lean_ctor_get(v___y_1201_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___y_1201_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___y_1201_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___y_1201_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_box(0);
if (lean_obj_tag(v_snd_1221_) == 7)
{
lean_object* v_binderType_1226_; lean_object* v_body_1227_; lean_object* v___x_1228_; 
v_binderType_1226_ = lean_ctor_get(v_snd_1221_, 1);
v_body_1227_ = lean_ctor_get(v_snd_1221_, 2);
lean_inc_ref(v_binderType_1226_);
v___x_1228_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_binderType_1226_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; uint8_t v___x_1230_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1229_);
lean_dec_ref_known(v___x_1228_, 1);
v___x_1230_ = lean_unbox(v_a_1229_);
lean_dec(v_a_1229_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1232_; 
lean_inc_ref(v_body_1227_);
lean_dec_ref_known(v_snd_1221_, 3);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v_body_1227_);
lean_ctor_set(v___x_1223_, 0, v___x_1225_);
v___x_1232_ = v___x_1223_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_body_1227_);
v___x_1232_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
v_a_1188_ = v___x_1232_;
goto _start;
}
}
else
{
lean_object* v_options_1235_; lean_object* v_inheritedTraceOptions_1236_; uint8_t v_hasTrace_1237_; 
lean_del_object(v___x_1223_);
v_options_1235_ = lean_ctor_get(v___y_1197_, 2);
v_inheritedTraceOptions_1236_ = lean_ctor_get(v___y_1197_, 13);
v_hasTrace_1237_ = lean_ctor_get_uint8(v_options_1235_, sizeof(void*)*1);
if (v_hasTrace_1237_ == 0)
{
goto v___jp_1238_;
}
else
{
lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1241_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_1242_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_1243_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1236_, v_options_1235_, v___x_1242_);
if (v___x_1243_ == 0)
{
goto v___jp_1238_;
}
else
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_Meta_Grind_updateLastTag(v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_dec_ref_known(v___x_1244_, 1);
v___x_1245_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8);
lean_inc_ref(v_snd_1221_);
v___x_1246_ = l_Lean_indentExpr(v_snd_1221_);
v___x_1247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1245_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___x_1248_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10);
v___x_1249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
lean_inc_ref(v_binderType_1226_);
v___x_1250_ = l_Lean_indentExpr(v_binderType_1226_);
v___x_1251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1249_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
v___x_1252_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_1241_, v___x_1251_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___x_1254_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref_known(v___x_1252_, 1);
v___x_1254_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_1187_, v_snd_1221_, v_a_1253_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
v___y_1201_ = v___x_1254_;
goto v___jp_1200_;
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
lean_dec_ref_known(v_snd_1221_, 3);
v_a_1255_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1252_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1252_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_dec_ref_known(v_snd_1221_, 3);
v_a_1263_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1244_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1244_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
v___jp_1238_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = lean_box(0);
v___x_1240_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_1187_, v_snd_1221_, v___x_1239_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
v___y_1201_ = v___x_1240_;
goto v___jp_1200_;
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec_ref_known(v_snd_1221_, 3);
lean_del_object(v___x_1223_);
v_a_1271_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1228_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1228_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
else
{
lean_object* v___x_1280_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1225_);
v___x_1280_ = v___x_1223_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_snd_1221_);
v___x_1280_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1281_; 
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
return v___x_1281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___boxed(lean_object* v___x_1285_, lean_object* v_a_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
uint8_t v___x_32461__boxed_1298_; lean_object* v_res_1299_; 
v___x_32461__boxed_1298_ = lean_unbox(v___x_1285_);
v_res_1299_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_32461__boxed_1298_, v_a_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec(v___y_1287_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(lean_object* v_e_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1300_, v_a_1308_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1355_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1315_ = v___x_1312_;
v_isShared_1316_ = v_isSharedCheck_1355_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1312_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1355_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = l_Lean_Expr_cleanupAnnotations(v_a_1313_);
v___x_1324_ = l_Lean_Expr_isApp(v___x_1323_);
if (v___x_1324_ == 0)
{
lean_dec_ref(v___x_1323_);
goto v___jp_1317_;
}
else
{
lean_object* v_arg_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v_arg_1325_ = lean_ctor_get(v___x_1323_, 1);
lean_inc_ref(v_arg_1325_);
v___x_1326_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1323_);
v___x_1327_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_1328_ = l_Lean_Expr_isConstOf(v___x_1326_, v___x_1327_);
lean_dec_ref(v___x_1326_);
if (v___x_1328_ == 0)
{
lean_dec_ref(v_arg_1325_);
goto v___jp_1317_;
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_del_object(v___x_1315_);
v___x_1329_ = lean_box(0);
v___x_1330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
lean_ctor_set(v___x_1330_, 1, v_arg_1325_);
v___x_1331_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_1328_, v___x_1330_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1346_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1346_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1346_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v_fst_1336_; 
v_fst_1336_ = lean_ctor_get(v_a_1332_, 0);
lean_inc(v_fst_1336_);
lean_dec(v_a_1332_);
if (lean_obj_tag(v_fst_1336_) == 0)
{
uint8_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1337_ = 0;
v___x_1338_ = lean_box(v___x_1337_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1338_);
v___x_1340_ = v___x_1334_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
else
{
lean_object* v_val_1342_; lean_object* v___x_1344_; 
v_val_1342_ = lean_ctor_get(v_fst_1336_, 0);
lean_inc(v_val_1342_);
lean_dec_ref_known(v_fst_1336_, 1);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v_val_1342_);
v___x_1344_ = v___x_1334_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_val_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
v_a_1347_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1331_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1331_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
v___jp_1317_:
{
uint8_t v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1318_ = 0;
v___x_1319_ = lean_box(v___x_1318_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 0, v___x_1319_);
v___x_1321_ = v___x_1315_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
v_a_1356_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1312_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1312_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied___boxed(lean_object* v_e_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec(v_a_1365_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(lean_object* v_cls_1377_, lean_object* v_msg_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1377_, v_msg_1378_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___boxed(lean_object* v_cls_1391_, lean_object* v_msg_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(v_cls_1391_, v_msg_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec(v___y_1393_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(uint8_t v___x_1405_, lean_object* v_inst_1406_, lean_object* v_a_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_1405_, v_a_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___boxed(lean_object* v___x_1420_, lean_object* v_inst_1421_, lean_object* v_a_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
uint8_t v___x_32832__boxed_1434_; lean_object* v_res_1435_; 
v___x_32832__boxed_1434_ = lean_unbox(v___x_1420_);
v_res_1435_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(v___x_32832__boxed_1434_, v_inst_1421_, v_a_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
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
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(lean_object* v_k_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v_b_1443_, lean_object* v_c_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; 
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc_ref(v___y_1445_);
lean_inc(v___y_1442_);
lean_inc_ref(v___y_1441_);
lean_inc(v___y_1440_);
lean_inc_ref(v___y_1439_);
lean_inc(v___y_1438_);
lean_inc(v___y_1437_);
v___x_1450_ = lean_apply_13(v_k_1436_, v_b_1443_, v_c_1444_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, lean_box(0));
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed(lean_object* v_k_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v_b_1458_, lean_object* v_c_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(v_k_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v_b_1458_, v_c_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec(v___y_1452_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(lean_object* v_type_1466_, lean_object* v_k_1467_, uint8_t v_cleanupAnnotations_1468_, uint8_t v_whnfType_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v___f_1481_; lean_object* v___x_1482_; 
lean_inc(v___y_1475_);
lean_inc_ref(v___y_1474_);
lean_inc(v___y_1473_);
lean_inc_ref(v___y_1472_);
lean_inc(v___y_1471_);
lean_inc(v___y_1470_);
v___f_1481_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1481_, 0, v_k_1467_);
lean_closure_set(v___f_1481_, 1, v___y_1470_);
lean_closure_set(v___f_1481_, 2, v___y_1471_);
lean_closure_set(v___f_1481_, 3, v___y_1472_);
lean_closure_set(v___f_1481_, 4, v___y_1473_);
lean_closure_set(v___f_1481_, 5, v___y_1474_);
lean_closure_set(v___f_1481_, 6, v___y_1475_);
v___x_1482_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1466_, v___f_1481_, v_cleanupAnnotations_1468_, v_whnfType_1469_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
if (lean_obj_tag(v___x_1482_) == 0)
{
return v___x_1482_;
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1482_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1482_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___boxed(lean_object* v_type_1491_, lean_object* v_k_1492_, lean_object* v_cleanupAnnotations_1493_, lean_object* v_whnfType_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1506_; uint8_t v_whnfType_boxed_1507_; lean_object* v_res_1508_; 
v_cleanupAnnotations_boxed_1506_ = lean_unbox(v_cleanupAnnotations_1493_);
v_whnfType_boxed_1507_ = lean_unbox(v_whnfType_1494_);
v_res_1508_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_1491_, v_k_1492_, v_cleanupAnnotations_boxed_1506_, v_whnfType_boxed_1507_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec(v___y_1495_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(lean_object* v_00_u03b1_1509_, lean_object* v_type_1510_, lean_object* v_k_1511_, uint8_t v_cleanupAnnotations_1512_, uint8_t v_whnfType_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_1510_, v_k_1511_, v_cleanupAnnotations_1512_, v_whnfType_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___boxed(lean_object* v_00_u03b1_1526_, lean_object* v_type_1527_, lean_object* v_k_1528_, lean_object* v_cleanupAnnotations_1529_, lean_object* v_whnfType_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1542_; uint8_t v_whnfType_boxed_1543_; lean_object* v_res_1544_; 
v_cleanupAnnotations_boxed_1542_ = lean_unbox(v_cleanupAnnotations_1529_);
v_whnfType_boxed_1543_ = lean_unbox(v_whnfType_1530_);
v_res_1544_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(v_00_u03b1_1526_, v_type_1527_, v_k_1528_, v_cleanupAnnotations_boxed_1542_, v_whnfType_boxed_1543_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec(v___y_1531_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed(lean_object* v_e_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_xs_1551_, lean_object* v_x_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
uint8_t v_a_95618__boxed_1564_; lean_object* v_res_1565_; 
v_a_95618__boxed_1564_ = lean_unbox(v_a_1549_);
v_res_1565_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(v_e_1548_, v_a_95618__boxed_1564_, v_a_1550_, v_xs_1551_, v_x_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v_x_1552_);
lean_dec_ref(v_xs_1551_);
return v_res_1565_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__0));
v___x_1568_ = l_Lean_stringToMessageData(v___x_1567_);
return v___x_1568_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3(void){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__2));
v___x_1571_ = l_Lean_stringToMessageData(v___x_1570_);
return v___x_1571_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__4));
v___x_1574_ = l_Lean_stringToMessageData(v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(lean_object* v_e_1575_, lean_object* v_h_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_){
_start:
{
uint8_t v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; uint8_t v___y_1595_; uint8_t v___y_1596_; lean_object* v_h_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; uint8_t v___y_1793_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v_options_1967_; uint8_t v_hasTrace_1968_; 
v_options_1967_ = lean_ctor_get(v_a_1585_, 2);
v_hasTrace_1968_ = lean_ctor_get_uint8(v_options_1967_, sizeof(void*)*1);
if (v_hasTrace_1968_ == 0)
{
v___y_1870_ = v_a_1577_;
v___y_1871_ = v_a_1578_;
v___y_1872_ = v_a_1579_;
v___y_1873_ = v_a_1580_;
v___y_1874_ = v_a_1581_;
v___y_1875_ = v_a_1582_;
v___y_1876_ = v_a_1583_;
v___y_1877_ = v_a_1584_;
v___y_1878_ = v_a_1585_;
v___y_1879_ = v_a_1586_;
goto v___jp_1869_;
}
else
{
lean_object* v_inheritedTraceOptions_1969_; lean_object* v_cls_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v_inheritedTraceOptions_1969_ = lean_ctor_get(v_a_1585_, 13);
v_cls_1970_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_1971_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_1972_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1969_, v_options_1967_, v___x_1971_);
if (v___x_1972_ == 0)
{
v___y_1870_ = v_a_1577_;
v___y_1871_ = v_a_1578_;
v___y_1872_ = v_a_1579_;
v___y_1873_ = v_a_1580_;
v___y_1874_ = v_a_1581_;
v___y_1875_ = v_a_1582_;
v___y_1876_ = v_a_1583_;
v___y_1877_ = v_a_1584_;
v___y_1878_ = v_a_1585_;
v___y_1879_ = v_a_1586_;
goto v___jp_1869_;
}
else
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_Meta_Grind_updateLastTag(v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v___x_1974_; 
lean_dec_ref_known(v___x_1973_, 1);
lean_inc(v_a_1586_);
lean_inc_ref(v_a_1585_);
lean_inc(v_a_1584_);
lean_inc_ref(v_a_1583_);
lean_inc_ref(v_h_1576_);
v___x_1974_ = lean_infer_type(v_h_1576_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref_known(v___x_1974_, 1);
v___x_1976_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5);
v___x_1977_ = l_Lean_MessageData_ofExpr(v_a_1975_);
v___x_1978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1976_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1970_, v___x_1978_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_dec_ref_known(v___x_1979_, 1);
v___y_1870_ = v_a_1577_;
v___y_1871_ = v_a_1578_;
v___y_1872_ = v_a_1579_;
v___y_1873_ = v_a_1580_;
v___y_1874_ = v_a_1581_;
v___y_1875_ = v_a_1582_;
v___y_1876_ = v_a_1583_;
v___y_1877_ = v_a_1584_;
v___y_1878_ = v_a_1585_;
v___y_1879_ = v_a_1586_;
goto v___jp_1869_;
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref(v_h_1576_);
lean_dec_ref(v_e_1575_);
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
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
lean_dec_ref(v_h_1576_);
lean_dec_ref(v_e_1575_);
v_a_1988_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1974_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1974_);
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
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec_ref(v_h_1576_);
lean_dec_ref(v_e_1575_);
v_a_1996_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1973_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1973_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
v___jp_1588_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = lean_box(0);
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
return v___x_1590_;
}
v___jp_1591_:
{
if (v___y_1596_ == 0)
{
lean_dec_ref(v_e_1575_);
if (v___y_1595_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_dec_ref(v_h_1597_);
lean_dec_ref(v___y_1594_);
lean_dec_ref(v___y_1593_);
v___x_1608_ = lean_box(0);
v___x_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
return v___x_1609_;
}
else
{
lean_object* v___x_1610_; 
lean_inc_ref(v___y_1594_);
v___x_1610_ = l_Lean_Meta_normLitValue(v___y_1594_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1612_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1610_, 1);
lean_inc_ref(v___y_1593_);
v___x_1612_ = l_Lean_Meta_normLitValue(v___y_1593_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1652_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1615_ = v___x_1612_;
v_isShared_1616_ = v_isSharedCheck_1652_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1612_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1652_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
uint8_t v___x_1617_; 
v___x_1617_ = lean_expr_eqv(v_a_1611_, v_a_1613_);
lean_dec(v_a_1613_);
lean_dec(v_a_1611_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; 
lean_del_object(v___x_1615_);
v___x_1618_ = l_Lean_Meta_mkEq(v___y_1594_, v___y_1593_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
lean_dec_ref_known(v___x_1618_, 1);
v___x_1620_ = l_Lean_mkNot(v_a_1619_);
v___x_1621_ = l_Lean_Meta_mkDecideProof(v___x_1620_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1631_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1624_ = v___x_1621_;
v_isShared_1625_ = v_isSharedCheck_1631_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1621_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1631_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1626_ = l_Lean_Expr_app___override(v_a_1622_, v_h_1597_);
v___x_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v___x_1627_);
v___x_1629_ = v___x_1624_;
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
lean_dec_ref(v_h_1597_);
v_a_1632_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1621_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1621_);
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
lean_dec_ref(v_h_1597_);
v_a_1640_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1618_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1618_);
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
lean_dec_ref(v_h_1597_);
lean_dec_ref(v___y_1594_);
lean_dec_ref(v___y_1593_);
v___x_1648_ = lean_box(0);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 0, v___x_1648_);
v___x_1650_ = v___x_1615_;
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
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec(v_a_1611_);
lean_dec_ref(v_h_1597_);
lean_dec_ref(v___y_1594_);
lean_dec_ref(v___y_1593_);
v_a_1653_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1612_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1612_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec_ref(v_h_1597_);
lean_dec_ref(v___y_1594_);
lean_dec_ref(v___y_1593_);
v_a_1661_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1610_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1610_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
else
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Lean_Meta_isConstructorApp_x3f(v___y_1594_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1770_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1770_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1770_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
if (lean_obj_tag(v_a_1670_) == 1)
{
lean_object* v_val_1674_; lean_object* v___x_1675_; 
lean_del_object(v___x_1672_);
v_val_1674_ = lean_ctor_get(v_a_1670_, 0);
lean_inc(v_val_1674_);
lean_dec_ref_known(v_a_1670_, 1);
v___x_1675_ = l_Lean_Meta_isConstructorApp_x3f(v___y_1593_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1757_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1678_ = v___x_1675_;
v_isShared_1679_ = v_isSharedCheck_1757_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1675_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1757_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
if (lean_obj_tag(v_a_1676_) == 1)
{
lean_object* v_val_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1752_; 
lean_del_object(v___x_1678_);
v_val_1680_ = lean_ctor_get(v_a_1676_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v_a_1676_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1682_ = v_a_1676_;
v_isShared_1683_ = v_isSharedCheck_1752_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_val_1680_);
lean_dec(v_a_1676_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1752_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_1602_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v___x_1686_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_a_1685_);
lean_dec_ref_known(v___x_1684_, 1);
v___x_1686_ = l_Lean_Meta_mkNoConfusion(v_a_1685_, v_h_1597_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_toConstantVal_1687_; lean_object* v_toConstantVal_1688_; lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1735_; 
v_toConstantVal_1687_ = lean_ctor_get(v_val_1674_, 0);
lean_inc_ref(v_toConstantVal_1687_);
lean_dec(v_val_1674_);
v_toConstantVal_1688_ = lean_ctor_get(v_val_1680_, 0);
lean_inc_ref(v_toConstantVal_1688_);
lean_dec(v_val_1680_);
v_a_1689_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1691_ = v___x_1686_;
v_isShared_1692_ = v_isSharedCheck_1735_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1686_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1735_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v_name_1693_; lean_object* v_name_1694_; uint8_t v___x_1695_; 
v_name_1693_ = lean_ctor_get(v_toConstantVal_1687_, 0);
lean_inc(v_name_1693_);
lean_dec_ref(v_toConstantVal_1687_);
v_name_1694_ = lean_ctor_get(v_toConstantVal_1688_, 0);
lean_inc(v_name_1694_);
lean_dec_ref(v_toConstantVal_1688_);
v___x_1695_ = lean_name_eq(v_name_1693_, v_name_1694_);
lean_dec(v_name_1694_);
lean_dec(v_name_1693_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1697_; 
lean_dec_ref(v_e_1575_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 0, v_a_1689_);
v___x_1697_ = v___x_1682_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1689_);
v___x_1697_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
lean_object* v___x_1699_; 
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1697_);
v___x_1699_ = v___x_1691_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
else
{
lean_object* v___x_1702_; 
lean_del_object(v___x_1691_);
lean_del_object(v___x_1682_);
lean_inc(v___y_1607_);
lean_inc_ref(v___y_1606_);
lean_inc(v___y_1605_);
lean_inc_ref(v___y_1604_);
lean_inc(v_a_1689_);
v___x_1702_ = lean_infer_type(v_a_1689_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v___x_1704_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1702_, 1);
v___x_1704_ = l_Lean_Meta_whnfD(v_a_1703_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1718_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1718_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1718_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
if (lean_obj_tag(v_a_1705_) == 7)
{
lean_object* v_binderType_1709_; lean_object* v___x_1710_; lean_object* v___f_1711_; uint8_t v___x_1712_; lean_object* v___x_1713_; 
lean_del_object(v___x_1707_);
v_binderType_1709_ = lean_ctor_get(v_a_1705_, 1);
lean_inc_ref(v_binderType_1709_);
lean_dec_ref_known(v_a_1705_, 3);
v___x_1710_ = lean_box(v___y_1592_);
v___f_1711_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed), 16, 3);
lean_closure_set(v___f_1711_, 0, v_e_1575_);
lean_closure_set(v___f_1711_, 1, v___x_1710_);
lean_closure_set(v___f_1711_, 2, v_a_1689_);
v___x_1712_ = 0;
v___x_1713_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_binderType_1709_, v___f_1711_, v___x_1712_, v___x_1712_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
return v___x_1713_;
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1716_; 
lean_dec(v_a_1705_);
lean_dec(v_a_1689_);
lean_dec_ref(v_e_1575_);
v___x_1714_ = lean_box(0);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1714_);
v___x_1716_ = v___x_1707_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec(v_a_1689_);
lean_dec_ref(v_e_1575_);
v_a_1719_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1704_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1704_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec(v_a_1689_);
lean_dec_ref(v_e_1575_);
v_a_1727_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1702_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1702_);
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
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_del_object(v___x_1682_);
lean_dec(v_val_1680_);
lean_dec(v_val_1674_);
lean_dec_ref(v_e_1575_);
v_a_1736_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1686_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1686_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_del_object(v___x_1682_);
lean_dec(v_val_1680_);
lean_dec(v_val_1674_);
lean_dec_ref(v_h_1597_);
lean_dec_ref(v_e_1575_);
v_a_1744_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1684_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1684_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1755_; 
lean_dec(v_a_1676_);
lean_dec(v_val_1674_);
lean_dec_ref(v_h_1597_);
lean_dec_ref(v_e_1575_);
v___x_1753_ = lean_box(0);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1753_);
v___x_1755_ = v___x_1678_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_dec(v_val_1674_);
lean_dec_ref(v_h_1597_);
lean_dec_ref(v_e_1575_);
v_a_1758_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1675_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1675_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1768_; 
lean_dec(v_a_1670_);
lean_dec_ref(v_h_1597_);
lean_dec_ref(v___y_1593_);
lean_dec_ref(v_e_1575_);
v___x_1766_ = lean_box(0);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1766_);
v___x_1768_ = v___x_1672_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec_ref(v_h_1597_);
lean_dec_ref(v___y_1593_);
lean_dec_ref(v_e_1575_);
v_a_1771_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1669_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1669_);
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
}
v___jp_1779_:
{
lean_object* v_self_1794_; uint8_t v_interpreted_1795_; uint8_t v_ctor_1796_; lean_object* v___x_1797_; 
v_self_1794_ = lean_ctor_get(v___y_1781_, 0);
lean_inc_ref_n(v_self_1794_, 2);
v_interpreted_1795_ = lean_ctor_get_uint8(v___y_1781_, sizeof(void*)*12 + 1);
v_ctor_1796_ = lean_ctor_get_uint8(v___y_1781_, sizeof(void*)*12 + 2);
lean_dec_ref(v___y_1781_);
lean_inc_ref(v___y_1788_);
v___x_1797_ = l_Lean_Meta_Grind_hasSameType(v_self_1794_, v___y_1788_, v___y_1791_, v___y_1785_, v___y_1782_, v___y_1786_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1860_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1860_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1860_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
uint8_t v___x_1802_; 
v___x_1802_ = lean_unbox(v_a_1798_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; lean_object* v___x_1805_; 
lean_dec(v_a_1798_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v___y_1792_);
lean_dec_ref(v___y_1788_);
lean_dec_ref(v_h_1576_);
lean_dec_ref(v_e_1575_);
v___x_1803_ = lean_box(0);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1803_);
v___x_1805_ = v___x_1800_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
else
{
lean_del_object(v___x_1800_);
if (v___y_1793_ == 0)
{
lean_object* v___x_1807_; 
lean_inc(v___y_1786_);
lean_inc_ref(v___y_1782_);
lean_inc(v___y_1785_);
lean_inc_ref(v___y_1791_);
lean_inc(v___y_1784_);
lean_inc_ref(v___y_1783_);
lean_inc(v___y_1789_);
lean_inc_ref(v___y_1790_);
lean_inc(v___y_1787_);
lean_inc(v___y_1780_);
lean_inc_ref(v_self_1794_);
v___x_1807_ = lean_grind_mk_eq_proof(v_self_1794_, v___y_1792_, v___y_1780_, v___y_1787_, v___y_1790_, v___y_1789_, v___y_1783_, v___y_1784_, v___y_1791_, v___y_1785_, v___y_1782_, v___y_1786_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1809_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
lean_dec_ref_known(v___x_1807_, 1);
v___x_1809_ = l_Lean_Meta_mkEqTrans(v_a_1808_, v_h_1576_, v___y_1791_, v___y_1785_, v___y_1782_, v___y_1786_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; uint8_t v___x_1811_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref_known(v___x_1809_, 1);
v___x_1811_ = lean_unbox(v_a_1798_);
lean_dec(v_a_1798_);
v___y_1592_ = v___x_1811_;
v___y_1593_ = v___y_1788_;
v___y_1594_ = v_self_1794_;
v___y_1595_ = v_interpreted_1795_;
v___y_1596_ = v_ctor_1796_;
v_h_1597_ = v_a_1810_;
v___y_1598_ = v___y_1780_;
v___y_1599_ = v___y_1787_;
v___y_1600_ = v___y_1790_;
v___y_1601_ = v___y_1789_;
v___y_1602_ = v___y_1783_;
v___y_1603_ = v___y_1784_;
v___y_1604_ = v___y_1791_;
v___y_1605_ = v___y_1785_;
v___y_1606_ = v___y_1782_;
v___y_1607_ = v___y_1786_;
goto v___jp_1591_;
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec(v_a_1798_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v___y_1788_);
lean_dec_ref(v_e_1575_);
v_a_1812_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1809_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1809_);
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
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec(v_a_1798_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v___y_1788_);
lean_dec_ref(v_h_1576_);
lean_dec_ref(v_e_1575_);
v_a_1820_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1807_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1807_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
else
{
lean_object* v___x_1828_; 
lean_inc(v___y_1786_);
lean_inc_ref(v___y_1782_);
lean_inc(v___y_1785_);
lean_inc_ref(v___y_1791_);
lean_inc(v___y_1784_);
lean_inc_ref(v___y_1783_);
lean_inc(v___y_1789_);
lean_inc_ref(v___y_1790_);
lean_inc(v___y_1787_);
lean_inc(v___y_1780_);
lean_inc_ref(v_self_1794_);
v___x_1828_ = lean_grind_mk_heq_proof(v_self_1794_, v___y_1792_, v___y_1780_, v___y_1787_, v___y_1790_, v___y_1789_, v___y_1783_, v___y_1784_, v___y_1791_, v___y_1785_, v___y_1782_, v___y_1786_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1830_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
lean_dec_ref_known(v___x_1828_, 1);
v___x_1830_ = l_Lean_Meta_mkHEqTrans(v_a_1829_, v_h_1576_, v___y_1791_, v___y_1785_, v___y_1782_, v___y_1786_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; uint8_t v___x_1832_; lean_object* v___x_1833_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref_known(v___x_1830_, 1);
v___x_1832_ = 0;
v___x_1833_ = l_Lean_Meta_mkEqOfHEq(v_a_1831_, v___x_1832_, v___y_1791_, v___y_1785_, v___y_1782_, v___y_1786_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; uint8_t v___x_1835_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1833_, 1);
v___x_1835_ = lean_unbox(v_a_1798_);
lean_dec(v_a_1798_);
v___y_1592_ = v___x_1835_;
v___y_1593_ = v___y_1788_;
v___y_1594_ = v_self_1794_;
v___y_1595_ = v_interpreted_1795_;
v___y_1596_ = v_ctor_1796_;
v_h_1597_ = v_a_1834_;
v___y_1598_ = v___y_1780_;
v___y_1599_ = v___y_1787_;
v___y_1600_ = v___y_1790_;
v___y_1601_ = v___y_1789_;
v___y_1602_ = v___y_1783_;
v___y_1603_ = v___y_1784_;
v___y_1604_ = v___y_1791_;
v___y_1605_ = v___y_1785_;
v___y_1606_ = v___y_1782_;
v___y_1607_ = v___y_1786_;
goto v___jp_1591_;
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_dec(v_a_1798_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v___y_1788_);
lean_dec_ref(v_e_1575_);
v_a_1836_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1833_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1833_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec(v_a_1798_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v___y_1788_);
lean_dec_ref(v_e_1575_);
v_a_1844_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1830_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1830_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec(v_a_1798_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v___y_1788_);
lean_dec_ref(v_h_1576_);
lean_dec_ref(v_e_1575_);
v_a_1852_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1828_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1828_);
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
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec_ref(v_self_1794_);
lean_dec_ref(v___y_1792_);
lean_dec_ref(v___y_1788_);
lean_dec_ref(v_h_1576_);
lean_dec_ref(v_e_1575_);
v_a_1861_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1797_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1797_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
v___jp_1869_:
{
lean_object* v___x_1880_; 
lean_inc(v___y_1879_);
lean_inc_ref(v___y_1878_);
lean_inc(v___y_1877_);
lean_inc_ref(v___y_1876_);
lean_inc_ref(v_h_1576_);
v___x_1880_ = lean_infer_type(v_h_1576_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1958_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1883_ = v___x_1880_;
v_isShared_1884_ = v_isSharedCheck_1958_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1880_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1958_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; 
v___x_1885_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_a_1881_);
if (lean_obj_tag(v___x_1885_) == 1)
{
lean_object* v_val_1886_; lean_object* v_snd_1887_; lean_object* v_fst_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1953_; 
lean_del_object(v___x_1883_);
v_val_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_val_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v_snd_1887_ = lean_ctor_get(v_val_1886_, 1);
v_fst_1888_ = lean_ctor_get(v_val_1886_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_val_1886_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1890_ = v_val_1886_;
v_isShared_1891_ = v_isSharedCheck_1953_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_snd_1887_);
lean_inc(v_fst_1888_);
lean_dec(v_val_1886_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1953_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v_fst_1892_; lean_object* v_snd_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1952_; 
v_fst_1892_ = lean_ctor_get(v_snd_1887_, 0);
v_snd_1893_ = lean_ctor_get(v_snd_1887_, 1);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_snd_1887_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1895_ = v_snd_1887_;
v_isShared_1896_ = v_isSharedCheck_1952_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_snd_1893_);
lean_inc(v_fst_1892_);
lean_dec(v_snd_1887_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1952_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_Meta_Sym_shareCommon___redArg(v_fst_1892_, v___y_1875_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1899_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v___x_1897_, 1);
v___x_1899_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_a_1898_, v___y_1870_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref_known(v___x_1899_, 1);
if (lean_obj_tag(v_a_1900_) == 1)
{
lean_del_object(v___x_1895_);
lean_del_object(v___x_1890_);
if (lean_obj_tag(v_fst_1888_) == 0)
{
lean_object* v_val_1901_; uint8_t v___x_1902_; 
v_val_1901_ = lean_ctor_get(v_a_1900_, 0);
lean_inc(v_val_1901_);
lean_dec_ref_known(v_a_1900_, 1);
v___x_1902_ = 0;
v___y_1780_ = v___y_1870_;
v___y_1781_ = v_val_1901_;
v___y_1782_ = v___y_1878_;
v___y_1783_ = v___y_1874_;
v___y_1784_ = v___y_1875_;
v___y_1785_ = v___y_1877_;
v___y_1786_ = v___y_1879_;
v___y_1787_ = v___y_1871_;
v___y_1788_ = v_snd_1893_;
v___y_1789_ = v___y_1873_;
v___y_1790_ = v___y_1872_;
v___y_1791_ = v___y_1876_;
v___y_1792_ = v_a_1898_;
v___y_1793_ = v___x_1902_;
goto v___jp_1779_;
}
else
{
lean_object* v_val_1903_; uint8_t v___x_1904_; 
lean_dec_ref_known(v_fst_1888_, 1);
v_val_1903_ = lean_ctor_get(v_a_1900_, 0);
lean_inc(v_val_1903_);
lean_dec_ref_known(v_a_1900_, 1);
v___x_1904_ = 1;
v___y_1780_ = v___y_1870_;
v___y_1781_ = v_val_1903_;
v___y_1782_ = v___y_1878_;
v___y_1783_ = v___y_1874_;
v___y_1784_ = v___y_1875_;
v___y_1785_ = v___y_1877_;
v___y_1786_ = v___y_1879_;
v___y_1787_ = v___y_1871_;
v___y_1788_ = v_snd_1893_;
v___y_1789_ = v___y_1873_;
v___y_1790_ = v___y_1872_;
v___y_1791_ = v___y_1876_;
v___y_1792_ = v_a_1898_;
v___y_1793_ = v___x_1904_;
goto v___jp_1779_;
}
}
else
{
lean_object* v___x_1905_; 
lean_dec(v_a_1900_);
lean_dec(v_snd_1893_);
lean_dec(v_fst_1888_);
lean_dec_ref(v_h_1576_);
v___x_1905_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1874_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; uint8_t v___x_1907_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref_known(v___x_1905_, 1);
v___x_1907_ = lean_unbox(v_a_1906_);
lean_dec(v_a_1906_);
if (v___x_1907_ == 0)
{
lean_dec(v_a_1898_);
lean_del_object(v___x_1895_);
lean_del_object(v___x_1890_);
lean_dec_ref(v_e_1575_);
goto v___jp_1588_;
}
else
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1908_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1);
v___x_1909_ = l_Lean_indentExpr(v_a_1898_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set_tag(v___x_1895_, 7);
lean_ctor_set(v___x_1895_, 1, v___x_1909_);
lean_ctor_set(v___x_1895_, 0, v___x_1908_);
v___x_1911_ = v___x_1895_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1908_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1912_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3);
if (v_isShared_1891_ == 0)
{
lean_ctor_set_tag(v___x_1890_, 7);
lean_ctor_set(v___x_1890_, 1, v___x_1912_);
lean_ctor_set(v___x_1890_, 0, v___x_1911_);
v___x_1914_ = v___x_1890_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1911_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1915_ = l_Lean_indentExpr(v_e_1575_);
v___x_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1914_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = l_Lean_Meta_Sym_reportIssue(v___x_1916_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_dec_ref_known(v___x_1917_, 1);
goto v___jp_1588_;
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1917_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1917_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec(v_a_1898_);
lean_del_object(v___x_1895_);
lean_del_object(v___x_1890_);
lean_dec_ref(v_e_1575_);
v_a_1928_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1905_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1905_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec(v_a_1898_);
lean_del_object(v___x_1895_);
lean_dec(v_snd_1893_);
lean_del_object(v___x_1890_);
lean_dec(v_fst_1888_);
lean_dec_ref(v_h_1576_);
lean_dec_ref(v_e_1575_);
v_a_1936_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1899_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1899_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_del_object(v___x_1895_);
lean_dec(v_snd_1893_);
lean_del_object(v___x_1890_);
lean_dec(v_fst_1888_);
lean_dec_ref(v_h_1576_);
lean_dec_ref(v_e_1575_);
v_a_1944_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1897_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1897_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1956_; 
lean_dec(v___x_1885_);
lean_dec_ref(v_h_1576_);
lean_dec_ref(v_e_1575_);
v___x_1954_ = lean_box(0);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1954_);
v___x_1956_ = v___x_1883_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1954_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec_ref(v_h_1576_);
lean_dec_ref(v_e_1575_);
v_a_1959_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1880_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1880_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(lean_object* v_e_2004_, lean_object* v_xs_2005_, uint8_t v_a_2006_, lean_object* v_a_2007_, lean_object* v_as_2008_, size_t v_sz_2009_, size_t v_i_2010_, lean_object* v_b_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
uint8_t v___x_2023_; 
v___x_2023_ = lean_usize_dec_lt(v_i_2010_, v_sz_2009_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; 
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_e_2004_);
v___x_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2024_, 0, v_b_2011_);
return v___x_2024_;
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2026_; 
lean_dec_ref(v_b_2011_);
v_a_2025_ = lean_array_uget_borrowed(v_as_2008_, v_i_2010_);
lean_inc(v_a_2025_);
lean_inc_ref(v_e_2004_);
v___x_2026_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2004_, v_a_2025_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2028_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2026_, 1);
v___x_2028_ = lean_box(0);
if (lean_obj_tag(v_a_2027_) == 1)
{
lean_object* v_val_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2058_; 
lean_dec_ref(v_e_2004_);
v_val_2029_ = lean_ctor_get(v_a_2027_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_a_2027_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2031_ = v_a_2027_;
v_isShared_2032_ = v_isSharedCheck_2058_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_val_2029_);
lean_dec(v_a_2027_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2058_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
uint8_t v___x_2033_; uint8_t v___x_2034_; lean_object* v___x_2035_; 
v___x_2033_ = 0;
v___x_2034_ = 1;
v___x_2035_ = l_Lean_Meta_mkLambdaFVars(v_xs_2005_, v_val_2029_, v___x_2033_, v_a_2006_, v___x_2033_, v_a_2006_, v___x_2034_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2049_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2038_ = v___x_2035_;
v_isShared_2039_ = v_isSharedCheck_2049_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2035_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2049_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2040_; lean_object* v___x_2042_; 
v___x_2040_ = l_Lean_Expr_app___override(v_a_2007_, v_a_2036_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v___x_2040_);
v___x_2042_ = v___x_2031_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; 
v___x_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
v___x_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
lean_ctor_set(v___x_2044_, 1, v___x_2028_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v___x_2044_);
v___x_2046_ = v___x_2038_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2044_);
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
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_del_object(v___x_2031_);
lean_dec_ref(v_a_2007_);
v_a_2050_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2035_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2035_);
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
else
{
lean_object* v___x_2059_; size_t v___x_2060_; size_t v___x_2061_; 
lean_dec(v_a_2027_);
v___x_2059_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v___x_2060_ = ((size_t)1ULL);
v___x_2061_ = lean_usize_add(v_i_2010_, v___x_2060_);
v_i_2010_ = v___x_2061_;
v_b_2011_ = v___x_2059_;
goto _start;
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_e_2004_);
v_a_2063_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2026_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2026_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(lean_object* v_e_2071_, uint8_t v_a_2072_, lean_object* v_a_2073_, lean_object* v_xs_2074_, lean_object* v_x_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; size_t v_sz_2089_; size_t v___x_2090_; lean_object* v___x_2091_; 
v___x_2087_ = lean_box(0);
v___x_2088_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_sz_2089_ = lean_array_size(v_xs_2074_);
v___x_2090_ = ((size_t)0ULL);
v___x_2091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_2071_, v_xs_2074_, v_a_2072_, v_a_2073_, v_xs_2074_, v_sz_2089_, v___x_2090_, v___x_2088_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
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
lean_object* v_a_2115_ = _args[2];
lean_object* v_a_2116_ = _args[3];
lean_object* v_as_2117_ = _args[4];
lean_object* v_sz_2118_ = _args[5];
lean_object* v_i_2119_ = _args[6];
lean_object* v_b_2120_ = _args[7];
lean_object* v___y_2121_ = _args[8];
lean_object* v___y_2122_ = _args[9];
lean_object* v___y_2123_ = _args[10];
lean_object* v___y_2124_ = _args[11];
lean_object* v___y_2125_ = _args[12];
lean_object* v___y_2126_ = _args[13];
lean_object* v___y_2127_ = _args[14];
lean_object* v___y_2128_ = _args[15];
lean_object* v___y_2129_ = _args[16];
lean_object* v___y_2130_ = _args[17];
lean_object* v___y_2131_ = _args[18];
_start:
{
uint8_t v_a_95642__boxed_2132_; size_t v_sz_boxed_2133_; size_t v_i_boxed_2134_; lean_object* v_res_2135_; 
v_a_95642__boxed_2132_ = lean_unbox(v_a_2115_);
v_sz_boxed_2133_ = lean_unbox_usize(v_sz_2118_);
lean_dec(v_sz_2118_);
v_i_boxed_2134_ = lean_unbox_usize(v_i_2119_);
lean_dec(v_i_2119_);
v_res_2135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_2113_, v_xs_2114_, v_a_95642__boxed_2132_, v_a_2116_, v_as_2117_, v_sz_boxed_2133_, v_i_boxed_2134_, v_b_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v_as_2117_);
lean_dec_ref(v_xs_2114_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___boxed(lean_object* v_e_2136_, lean_object* v_h_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2136_, v_h_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_);
lean_dec(v_a_2147_);
lean_dec_ref(v_a_2146_);
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
lean_dec(v_a_2143_);
lean_dec_ref(v_a_2142_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
lean_dec(v_a_2139_);
lean_dec(v_a_2138_);
return v_res_2149_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__0));
v___x_2152_ = l_Lean_stringToMessageData(v___x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(lean_object* v_e_2153_, lean_object* v_xs_2154_, uint8_t v___x_2155_, lean_object* v_as_2156_, size_t v_sz_2157_, size_t v_i_2158_, lean_object* v_b_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v_a_2172_; uint8_t v___x_2176_; 
v___x_2176_ = lean_usize_dec_lt(v_i_2158_, v_sz_2157_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; 
lean_dec_ref(v_e_2153_);
v___x_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2177_, 0, v_b_2159_);
return v___x_2177_;
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2179_; 
lean_dec_ref(v_b_2159_);
v_a_2178_ = lean_array_uget_borrowed(v_as_2156_, v_i_2158_);
lean_inc(v___y_2169_);
lean_inc_ref(v___y_2168_);
lean_inc(v___y_2167_);
lean_inc_ref(v___y_2166_);
lean_inc(v_a_2178_);
v___x_2179_ = lean_infer_type(v_a_2178_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2181_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc_n(v_a_2180_, 2);
lean_dec_ref_known(v___x_2179_, 1);
v___x_2181_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_a_2180_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; uint8_t v___x_2235_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
lean_dec_ref_known(v___x_2181_, 1);
v___x_2183_ = lean_box(0);
v___x_2184_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v___x_2235_ = lean_unbox(v_a_2182_);
lean_dec(v_a_2182_);
if (v___x_2235_ == 0)
{
lean_dec(v_a_2180_);
v_a_2172_ = v___x_2184_;
goto v___jp_2171_;
}
else
{
lean_object* v_options_2236_; uint8_t v_hasTrace_2237_; 
v_options_2236_ = lean_ctor_get(v___y_2168_, 2);
v_hasTrace_2237_ = lean_ctor_get_uint8(v_options_2236_, sizeof(void*)*1);
if (v_hasTrace_2237_ == 0)
{
lean_dec(v_a_2180_);
v___y_2186_ = v___y_2160_;
v___y_2187_ = v___y_2161_;
v___y_2188_ = v___y_2162_;
v___y_2189_ = v___y_2163_;
v___y_2190_ = v___y_2164_;
v___y_2191_ = v___y_2165_;
v___y_2192_ = v___y_2166_;
v___y_2193_ = v___y_2167_;
v___y_2194_ = v___y_2168_;
v___y_2195_ = v___y_2169_;
goto v___jp_2185_;
}
else
{
lean_object* v_inheritedTraceOptions_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; uint8_t v___x_2241_; 
v_inheritedTraceOptions_2238_ = lean_ctor_get(v___y_2168_, 13);
v___x_2239_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_2240_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_2241_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2238_, v_options_2236_, v___x_2240_);
if (v___x_2241_ == 0)
{
lean_dec(v_a_2180_);
v___y_2186_ = v___y_2160_;
v___y_2187_ = v___y_2161_;
v___y_2188_ = v___y_2162_;
v___y_2189_ = v___y_2163_;
v___y_2190_ = v___y_2164_;
v___y_2191_ = v___y_2165_;
v___y_2192_ = v___y_2166_;
v___y_2193_ = v___y_2167_;
v___y_2194_ = v___y_2168_;
v___y_2195_ = v___y_2169_;
goto v___jp_2185_;
}
else
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_Meta_Grind_updateLastTag(v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
lean_dec_ref_known(v___x_2242_, 1);
v___x_2243_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1);
v___x_2244_ = l_Lean_MessageData_ofExpr(v_a_2180_);
v___x_2245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2243_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
v___x_2246_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_2239_, v___x_2245_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_dec_ref_known(v___x_2246_, 1);
v___y_2186_ = v___y_2160_;
v___y_2187_ = v___y_2161_;
v___y_2188_ = v___y_2162_;
v___y_2189_ = v___y_2163_;
v___y_2190_ = v___y_2164_;
v___y_2191_ = v___y_2165_;
v___y_2192_ = v___y_2166_;
v___y_2193_ = v___y_2167_;
v___y_2194_ = v___y_2168_;
v___y_2195_ = v___y_2169_;
goto v___jp_2185_;
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec_ref(v_e_2153_);
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2246_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2246_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v_a_2180_);
lean_dec_ref(v_e_2153_);
v_a_2255_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2242_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2242_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
}
}
v___jp_2185_:
{
lean_object* v___x_2196_; 
lean_inc(v_a_2178_);
lean_inc_ref(v_e_2153_);
v___x_2196_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2153_, v_a_2178_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2196_, 1);
if (lean_obj_tag(v_a_2197_) == 1)
{
lean_object* v_val_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2226_; 
lean_dec_ref(v_e_2153_);
v_val_2198_ = lean_ctor_get(v_a_2197_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_a_2197_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2200_ = v_a_2197_;
v_isShared_2201_ = v_isSharedCheck_2226_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_val_2198_);
lean_dec(v_a_2197_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2226_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
uint8_t v___x_2202_; uint8_t v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = 0;
v___x_2203_ = 1;
v___x_2204_ = l_Lean_Meta_mkLambdaFVars(v_xs_2154_, v_val_2198_, v___x_2202_, v___x_2155_, v___x_2202_, v___x_2155_, v___x_2203_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2217_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2207_ = v___x_2204_;
v_isShared_2208_ = v_isSharedCheck_2217_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2204_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2217_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v_a_2205_);
v___x_2210_ = v___x_2200_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
v___x_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
lean_ctor_set(v___x_2212_, 1, v___x_2183_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2212_);
v___x_2214_ = v___x_2207_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_del_object(v___x_2200_);
v_a_2218_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2204_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2204_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
else
{
lean_dec(v_a_2197_);
v_a_2172_ = v___x_2184_;
goto v___jp_2171_;
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec_ref(v_e_2153_);
v_a_2227_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2196_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2196_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec(v_a_2180_);
lean_dec_ref(v_e_2153_);
v_a_2263_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2181_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2181_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_dec_ref(v_e_2153_);
v_a_2271_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2179_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2179_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
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
v___jp_2171_:
{
size_t v___x_2173_; size_t v___x_2174_; 
v___x_2173_ = ((size_t)1ULL);
v___x_2174_ = lean_usize_add(v_i_2158_, v___x_2173_);
lean_inc_ref(v_a_2172_);
v_i_2158_ = v___x_2174_;
v_b_2159_ = v_a_2172_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_e_2279_ = _args[0];
lean_object* v_xs_2280_ = _args[1];
lean_object* v___x_2281_ = _args[2];
lean_object* v_as_2282_ = _args[3];
lean_object* v_sz_2283_ = _args[4];
lean_object* v_i_2284_ = _args[5];
lean_object* v_b_2285_ = _args[6];
lean_object* v___y_2286_ = _args[7];
lean_object* v___y_2287_ = _args[8];
lean_object* v___y_2288_ = _args[9];
lean_object* v___y_2289_ = _args[10];
lean_object* v___y_2290_ = _args[11];
lean_object* v___y_2291_ = _args[12];
lean_object* v___y_2292_ = _args[13];
lean_object* v___y_2293_ = _args[14];
lean_object* v___y_2294_ = _args[15];
lean_object* v___y_2295_ = _args[16];
lean_object* v___y_2296_ = _args[17];
_start:
{
uint8_t v___x_30241__boxed_2297_; size_t v_sz_boxed_2298_; size_t v_i_boxed_2299_; lean_object* v_res_2300_; 
v___x_30241__boxed_2297_ = lean_unbox(v___x_2281_);
v_sz_boxed_2298_ = lean_unbox_usize(v_sz_2283_);
lean_dec(v_sz_2283_);
v_i_boxed_2299_ = lean_unbox_usize(v_i_2284_);
lean_dec(v_i_2284_);
v_res_2300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2279_, v_xs_2280_, v___x_30241__boxed_2297_, v_as_2282_, v_sz_boxed_2298_, v_i_boxed_2299_, v_b_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v_as_2282_);
lean_dec_ref(v_xs_2280_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(lean_object* v_e_2301_, uint8_t v___x_2302_, lean_object* v_xs_2303_, lean_object* v_x_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; size_t v_sz_2318_; size_t v___x_2319_; lean_object* v___x_2320_; 
v___x_2316_ = lean_box(0);
v___x_2317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_sz_2318_ = lean_array_size(v_xs_2303_);
v___x_2319_ = ((size_t)0ULL);
v___x_2320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2301_, v_xs_2303_, v___x_2302_, v_xs_2303_, v_sz_2318_, v___x_2319_, v___x_2317_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2333_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2323_ = v___x_2320_;
v_isShared_2324_ = v_isSharedCheck_2333_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2333_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v_fst_2325_; 
v_fst_2325_ = lean_ctor_get(v_a_2321_, 0);
lean_inc(v_fst_2325_);
lean_dec(v_a_2321_);
if (lean_obj_tag(v_fst_2325_) == 0)
{
lean_object* v___x_2327_; 
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v___x_2316_);
v___x_2327_ = v___x_2323_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2316_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
else
{
lean_object* v_val_2329_; lean_object* v___x_2331_; 
v_val_2329_ = lean_ctor_get(v_fst_2325_, 0);
lean_inc(v_val_2329_);
lean_dec_ref_known(v_fst_2325_, 1);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v_val_2329_);
v___x_2331_ = v___x_2323_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_val_2329_);
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
v_a_2334_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2320_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2320_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed(lean_object* v_e_2342_, lean_object* v___x_2343_, lean_object* v_xs_2344_, lean_object* v_x_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
uint8_t v___x_30493__boxed_2357_; lean_object* v_res_2358_; 
v___x_30493__boxed_2357_ = lean_unbox(v___x_2343_);
v_res_2358_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(v_e_2342_, v___x_30493__boxed_2357_, v_xs_2344_, v_x_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v_x_2345_);
lean_dec_ref(v_xs_2344_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(lean_object* v_e_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_){
_start:
{
lean_object* v___x_2371_; 
lean_inc_ref(v_e_2359_);
v___x_2371_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2359_, v_a_2367_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2391_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2374_ = v___x_2371_;
v_isShared_2375_ = v_isSharedCheck_2391_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2371_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2391_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2381_; uint8_t v___x_2382_; 
v___x_2381_ = l_Lean_Expr_cleanupAnnotations(v_a_2372_);
v___x_2382_ = l_Lean_Expr_isApp(v___x_2381_);
if (v___x_2382_ == 0)
{
lean_dec_ref(v___x_2381_);
lean_dec_ref(v_e_2359_);
goto v___jp_2376_;
}
else
{
lean_object* v_arg_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; 
v_arg_2383_ = lean_ctor_get(v___x_2381_, 1);
lean_inc_ref(v_arg_2383_);
v___x_2384_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2381_);
v___x_2385_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_2386_ = l_Lean_Expr_isConstOf(v___x_2384_, v___x_2385_);
lean_dec_ref(v___x_2384_);
if (v___x_2386_ == 0)
{
lean_dec_ref(v_arg_2383_);
lean_dec_ref(v_e_2359_);
goto v___jp_2376_;
}
else
{
lean_object* v___x_2387_; lean_object* v___f_2388_; uint8_t v___x_2389_; lean_object* v___x_2390_; 
lean_del_object(v___x_2374_);
v___x_2387_ = lean_box(v___x_2386_);
v___f_2388_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed), 15, 2);
lean_closure_set(v___f_2388_, 0, v_e_2359_);
lean_closure_set(v___f_2388_, 1, v___x_2387_);
v___x_2389_ = 0;
v___x_2390_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_arg_2383_, v___f_2388_, v___x_2389_, v___x_2389_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
return v___x_2390_;
}
}
v___jp_2376_:
{
lean_object* v___x_2377_; lean_object* v___x_2379_; 
v___x_2377_ = lean_box(0);
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 0, v___x_2377_);
v___x_2379_ = v___x_2374_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
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
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
lean_dec_ref(v_e_2359_);
v_a_2392_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2371_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2371_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___boxed(lean_object* v_e_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
lean_dec(v_a_2410_);
lean_dec_ref(v_a_2409_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec(v_a_2401_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(lean_object* v_e_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v___x_2425_; 
lean_inc_ref(v_e_2413_);
v___x_2425_ = l_Lean_Meta_Grind_getRootENode___redArg(v_e_2413_, v_a_2414_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2493_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2493_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2493_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
uint8_t v_ctor_2430_; 
v_ctor_2430_ = lean_ctor_get_uint8(v_a_2426_, sizeof(void*)*12 + 2);
if (v_ctor_2430_ == 0)
{
uint8_t v_interpreted_2431_; 
v_interpreted_2431_ = lean_ctor_get_uint8(v_a_2426_, sizeof(void*)*12 + 1);
if (v_interpreted_2431_ == 0)
{
lean_object* v___x_2433_; 
lean_dec(v_a_2426_);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v_e_2413_);
v___x_2433_ = v___x_2428_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_e_2413_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
else
{
lean_object* v_self_2435_; lean_object* v___x_2437_; 
lean_dec_ref(v_e_2413_);
v_self_2435_ = lean_ctor_get(v_a_2426_, 0);
lean_inc_ref(v_self_2435_);
lean_dec(v_a_2426_);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v_self_2435_);
v___x_2437_ = v___x_2428_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_self_2435_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
else
{
lean_object* v_self_2439_; lean_object* v___x_2440_; 
lean_del_object(v___x_2428_);
lean_dec_ref(v_e_2413_);
v_self_2439_ = lean_ctor_get(v_a_2426_, 0);
lean_inc_ref_n(v_self_2439_, 2);
lean_dec(v_a_2426_);
v___x_2440_ = l_Lean_Meta_isConstructorApp_x3f(v_self_2439_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2484_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2443_ = v___x_2440_;
v_isShared_2444_ = v_isSharedCheck_2484_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2440_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2484_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
if (lean_obj_tag(v_a_2441_) == 1)
{
lean_object* v_val_2445_; lean_object* v_numParams_2446_; lean_object* v_numFields_2447_; lean_object* v_nargs_2448_; lean_object* v___x_2449_; lean_object* v_dummy_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; uint8_t v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
lean_del_object(v___x_2443_);
v_val_2445_ = lean_ctor_get(v_a_2441_, 0);
lean_inc(v_val_2445_);
lean_dec_ref_known(v_a_2441_, 1);
v_numParams_2446_ = lean_ctor_get(v_val_2445_, 3);
lean_inc(v_numParams_2446_);
v_numFields_2447_ = lean_ctor_get(v_val_2445_, 4);
lean_inc(v_numFields_2447_);
lean_dec(v_val_2445_);
v_nargs_2448_ = l_Lean_Expr_getAppNumArgs(v_self_2439_);
v___x_2449_ = lean_nat_add(v_numParams_2446_, v_numFields_2447_);
lean_dec(v_numFields_2447_);
v_dummy_2450_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0);
lean_inc(v_nargs_2448_);
v___x_2451_ = lean_mk_array(v_nargs_2448_, v_dummy_2450_);
v___x_2452_ = lean_unsigned_to_nat(1u);
v___x_2453_ = lean_nat_sub(v_nargs_2448_, v___x_2452_);
lean_dec(v_nargs_2448_);
lean_inc_ref(v_self_2439_);
v___x_2454_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_2439_, v___x_2451_, v___x_2453_);
v___x_2455_ = 0;
v___x_2456_ = lean_box(v___x_2455_);
v___x_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2454_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
v___x_2458_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v___x_2449_, v_ctor_2430_, v_numParams_2446_, v___x_2457_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
lean_dec(v___x_2449_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2472_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2472_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2472_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v_snd_2463_; uint8_t v___x_2464_; 
v_snd_2463_ = lean_ctor_get(v_a_2459_, 1);
v___x_2464_ = lean_unbox(v_snd_2463_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2466_; 
lean_dec(v_a_2459_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v_self_2439_);
v___x_2466_ = v___x_2461_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_self_2439_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
else
{
lean_object* v_fst_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
lean_del_object(v___x_2461_);
v_fst_2468_ = lean_ctor_get(v_a_2459_, 0);
lean_inc(v_fst_2468_);
lean_dec(v_a_2459_);
v___x_2469_ = l_Lean_Expr_getAppFn(v_self_2439_);
lean_dec_ref(v_self_2439_);
v___x_2470_ = l_Lean_mkAppN(v___x_2469_, v_fst_2468_);
lean_dec(v_fst_2468_);
v___x_2471_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_2470_, v_a_2419_);
return v___x_2471_;
}
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec_ref(v_self_2439_);
v_a_2473_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2458_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2458_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
else
{
lean_object* v___x_2482_; 
lean_dec(v_a_2441_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v_self_2439_);
v___x_2482_ = v___x_2443_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_self_2439_);
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
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec_ref(v_self_2439_);
v_a_2485_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2440_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2440_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_dec_ref(v_e_2413_);
v_a_2494_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2425_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2425_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(lean_object* v_upperBound_2502_, uint8_t v___x_2503_, lean_object* v_a_2504_, lean_object* v_b_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
uint8_t v___x_2517_; 
v___x_2517_ = lean_nat_dec_lt(v_a_2504_, v_upperBound_2502_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; 
lean_dec(v_a_2504_);
v___x_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2518_, 0, v_b_2505_);
return v___x_2518_;
}
else
{
lean_object* v_fst_2519_; lean_object* v_snd_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2550_; 
v_fst_2519_ = lean_ctor_get(v_b_2505_, 0);
v_snd_2520_ = lean_ctor_get(v_b_2505_, 1);
v_isSharedCheck_2550_ = !lean_is_exclusive(v_b_2505_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2522_ = v_b_2505_;
v_isShared_2523_ = v_isSharedCheck_2550_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_snd_2520_);
lean_inc(v_fst_2519_);
lean_dec(v_b_2505_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2550_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2524_ = l_Lean_instInhabitedExpr;
v___x_2525_ = lean_array_get_borrowed(v___x_2524_, v_fst_2519_, v_a_2504_);
lean_inc(v___x_2525_);
v___x_2526_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v___x_2525_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2527_; lean_object* v_a_2529_; uint8_t v___x_2533_; 
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_a_2527_);
lean_dec_ref_known(v___x_2526_, 1);
v___x_2533_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2525_, v_a_2527_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2537_; 
lean_dec(v_snd_2520_);
v___x_2534_ = lean_array_set(v_fst_2519_, v_a_2504_, v_a_2527_);
v___x_2535_ = lean_box(v___x_2503_);
if (v_isShared_2523_ == 0)
{
lean_ctor_set(v___x_2522_, 1, v___x_2535_);
lean_ctor_set(v___x_2522_, 0, v___x_2534_);
v___x_2537_ = v___x_2522_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2534_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v___x_2535_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
v_a_2529_ = v___x_2537_;
goto v___jp_2528_;
}
}
else
{
lean_object* v___x_2540_; 
lean_dec(v_a_2527_);
if (v_isShared_2523_ == 0)
{
v___x_2540_ = v___x_2522_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_fst_2519_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_snd_2520_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
v_a_2529_ = v___x_2540_;
goto v___jp_2528_;
}
}
v___jp_2528_:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = lean_unsigned_to_nat(1u);
v___x_2531_ = lean_nat_add(v_a_2504_, v___x_2530_);
lean_dec(v_a_2504_);
v_a_2504_ = v___x_2531_;
v_b_2505_ = v_a_2529_;
goto _start;
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_del_object(v___x_2522_);
lean_dec(v_snd_2520_);
lean_dec(v_fst_2519_);
lean_dec(v_a_2504_);
v_a_2542_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2526_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2526_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg___boxed(lean_object* v_upperBound_2551_, lean_object* v___x_2552_, lean_object* v_a_2553_, lean_object* v_b_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
uint8_t v___x_15840__boxed_2566_; lean_object* v_res_2567_; 
v___x_15840__boxed_2566_ = lean_unbox(v___x_2552_);
v_res_2567_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2551_, v___x_15840__boxed_2566_, v_a_2553_, v_b_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec(v_upperBound_2551_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go___boxed(lean_object* v_e_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_e_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_);
lean_dec(v_a_2578_);
lean_dec_ref(v_a_2577_);
lean_dec(v_a_2576_);
lean_dec_ref(v_a_2575_);
lean_dec(v_a_2574_);
lean_dec_ref(v_a_2573_);
lean_dec(v_a_2572_);
lean_dec_ref(v_a_2571_);
lean_dec(v_a_2570_);
lean_dec(v_a_2569_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(lean_object* v_upperBound_2581_, uint8_t v___x_2582_, lean_object* v_inst_2583_, lean_object* v_R_2584_, lean_object* v_a_2585_, lean_object* v_b_2586_, lean_object* v_c_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2581_, v___x_2582_, v_a_2585_, v_b_2586_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_2600_ = _args[0];
lean_object* v___x_2601_ = _args[1];
lean_object* v_inst_2602_ = _args[2];
lean_object* v_R_2603_ = _args[3];
lean_object* v_a_2604_ = _args[4];
lean_object* v_b_2605_ = _args[5];
lean_object* v_c_2606_ = _args[6];
lean_object* v___y_2607_ = _args[7];
lean_object* v___y_2608_ = _args[8];
lean_object* v___y_2609_ = _args[9];
lean_object* v___y_2610_ = _args[10];
lean_object* v___y_2611_ = _args[11];
lean_object* v___y_2612_ = _args[12];
lean_object* v___y_2613_ = _args[13];
lean_object* v___y_2614_ = _args[14];
lean_object* v___y_2615_ = _args[15];
lean_object* v___y_2616_ = _args[16];
lean_object* v___y_2617_ = _args[17];
_start:
{
uint8_t v___x_16081__boxed_2618_; lean_object* v_res_2619_; 
v___x_16081__boxed_2618_ = lean_unbox(v___x_2601_);
v_res_2619_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(v_upperBound_2600_, v___x_16081__boxed_2618_, v_inst_2602_, v_R_2603_, v_a_2604_, v_b_2605_, v_c_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec(v_upperBound_2600_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(lean_object* v_e_2620_, lean_object* v___y_2621_){
_start:
{
uint8_t v___x_2623_; 
v___x_2623_ = l_Lean_Expr_hasMVar(v_e_2620_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; 
v___x_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2624_, 0, v_e_2620_);
return v___x_2624_;
}
else
{
lean_object* v___x_2625_; lean_object* v_mctx_2626_; lean_object* v___x_2627_; lean_object* v_fst_2628_; lean_object* v_snd_2629_; lean_object* v___x_2630_; lean_object* v_cache_2631_; lean_object* v_zetaDeltaFVarIds_2632_; lean_object* v_postponed_2633_; lean_object* v_diag_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2643_; 
v___x_2625_ = lean_st_ref_get(v___y_2621_);
v_mctx_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc_ref(v_mctx_2626_);
lean_dec(v___x_2625_);
v___x_2627_ = l_Lean_instantiateMVarsCore(v_mctx_2626_, v_e_2620_);
v_fst_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_fst_2628_);
v_snd_2629_ = lean_ctor_get(v___x_2627_, 1);
lean_inc(v_snd_2629_);
lean_dec_ref(v___x_2627_);
v___x_2630_ = lean_st_ref_take(v___y_2621_);
v_cache_2631_ = lean_ctor_get(v___x_2630_, 1);
v_zetaDeltaFVarIds_2632_ = lean_ctor_get(v___x_2630_, 2);
v_postponed_2633_ = lean_ctor_get(v___x_2630_, 3);
v_diag_2634_ = lean_ctor_get(v___x_2630_, 4);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2643_ == 0)
{
lean_object* v_unused_2644_; 
v_unused_2644_ = lean_ctor_get(v___x_2630_, 0);
lean_dec(v_unused_2644_);
v___x_2636_ = v___x_2630_;
v_isShared_2637_ = v_isSharedCheck_2643_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_diag_2634_);
lean_inc(v_postponed_2633_);
lean_inc(v_zetaDeltaFVarIds_2632_);
lean_inc(v_cache_2631_);
lean_dec(v___x_2630_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2643_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 0, v_snd_2629_);
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_snd_2629_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_cache_2631_);
lean_ctor_set(v_reuseFailAlloc_2642_, 2, v_zetaDeltaFVarIds_2632_);
lean_ctor_set(v_reuseFailAlloc_2642_, 3, v_postponed_2633_);
lean_ctor_set(v_reuseFailAlloc_2642_, 4, v_diag_2634_);
v___x_2639_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = lean_st_ref_set(v___y_2621_, v___x_2639_);
v___x_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2641_, 0, v_fst_2628_);
return v___x_2641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg___boxed(lean_object* v_e_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(v_e_2645_, v___y_2646_);
lean_dec(v___y_2646_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(lean_object* v_e_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(v_e_2649_, v___y_2657_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___boxed(lean_object* v_e_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(v_e_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec(v___y_2663_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0(lean_object* v_k_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v___x_2687_; 
lean_inc(v___y_2681_);
lean_inc_ref(v___y_2680_);
lean_inc(v___y_2679_);
lean_inc_ref(v___y_2678_);
lean_inc(v___y_2677_);
lean_inc(v___y_2676_);
v___x_2687_ = lean_apply_11(v_k_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, lean_box(0));
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0___boxed(lean_object* v_k_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0(v_k_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec(v___y_2689_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(lean_object* v_k_2701_, uint8_t v_allowLevelAssignments_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v___f_2714_; lean_object* v___x_2715_; 
lean_inc(v___y_2708_);
lean_inc_ref(v___y_2707_);
lean_inc(v___y_2706_);
lean_inc_ref(v___y_2705_);
lean_inc(v___y_2704_);
lean_inc(v___y_2703_);
v___f_2714_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_2714_, 0, v_k_2701_);
lean_closure_set(v___f_2714_, 1, v___y_2703_);
lean_closure_set(v___f_2714_, 2, v___y_2704_);
lean_closure_set(v___f_2714_, 3, v___y_2705_);
lean_closure_set(v___f_2714_, 4, v___y_2706_);
lean_closure_set(v___f_2714_, 5, v___y_2707_);
lean_closure_set(v___f_2714_, 6, v___y_2708_);
v___x_2715_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2702_, v___f_2714_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
if (lean_obj_tag(v___x_2715_) == 0)
{
return v___x_2715_;
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___boxed(lean_object* v_k_2724_, lean_object* v_allowLevelAssignments_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2737_; lean_object* v_res_2738_; 
v_allowLevelAssignments_boxed_2737_ = lean_unbox(v_allowLevelAssignments_2725_);
v_res_2738_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(v_k_2724_, v_allowLevelAssignments_boxed_2737_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(lean_object* v_00_u03b1_2739_, lean_object* v_k_2740_, uint8_t v_allowLevelAssignments_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v___x_2753_; 
v___x_2753_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(v_k_2740_, v_allowLevelAssignments_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___boxed(lean_object* v_00_u03b1_2754_, lean_object* v_k_2755_, lean_object* v_allowLevelAssignments_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2768_; lean_object* v_res_2769_; 
v_allowLevelAssignments_boxed_2768_ = lean_unbox(v_allowLevelAssignments_2756_);
v_res_2769_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_00_u03b1_2754_, v_k_2755_, v_allowLevelAssignments_boxed_2768_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec(v___y_2757_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0(lean_object* v_cls_2770_, lean_object* v_____do__lift_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v_options_2783_; uint8_t v_hasTrace_2784_; 
v_options_2783_ = lean_ctor_get(v___y_2780_, 2);
v_hasTrace_2784_ = lean_ctor_get_uint8(v_options_2783_, sizeof(void*)*1);
if (v_hasTrace_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_dec(v_cls_2770_);
v___x_2785_ = lean_box(v_hasTrace_2784_);
v___x_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
return v___x_2786_;
}
else
{
lean_object* v___x_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2787_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5));
v___x_2788_ = l_Lean_Name_append(v___x_2787_, v_cls_2770_);
v___x_2789_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2771_, v_options_2783_, v___x_2788_);
lean_dec(v___x_2788_);
v___x_2790_ = lean_box(v___x_2789_);
v___x_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2790_);
return v___x_2791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed(lean_object* v_cls_2792_, lean_object* v_____do__lift_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Lean_Meta_Grind_tryToProveFalse___lam__0(v_cls_2792_, v_____do__lift_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v_____do__lift_2793_);
return v_res_2805_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3(void){
_start:
{
lean_object* v_cls_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v_cls_2814_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2));
v___x_2815_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5));
v___x_2816_ = l_Lean_Name_append(v___x_2815_, v_cls_2814_);
return v___x_2816_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__4));
v___x_2819_ = l_Lean_stringToMessageData(v___x_2818_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(lean_object* v_as_2820_, size_t v_sz_2821_, size_t v_i_2822_, lean_object* v_b_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v_a_2836_; uint8_t v___x_2840_; 
v___x_2840_ = lean_usize_dec_lt(v_i_2822_, v_sz_2821_);
if (v___x_2840_ == 0)
{
lean_object* v___x_2841_; 
v___x_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2841_, 0, v_b_2823_);
return v___x_2841_;
}
else
{
lean_object* v_snd_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_3029_; 
v_snd_2842_ = lean_ctor_get(v_b_2823_, 1);
v_isSharedCheck_3029_ = !lean_is_exclusive(v_b_2823_);
if (v_isSharedCheck_3029_ == 0)
{
lean_object* v_unused_3030_; 
v_unused_3030_ = lean_ctor_get(v_b_2823_, 0);
lean_dec(v_unused_3030_);
v___x_2844_ = v_b_2823_;
v_isShared_2845_ = v_isSharedCheck_3029_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_snd_2842_);
lean_dec(v_b_2823_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_3029_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v_array_2846_; lean_object* v_start_2847_; lean_object* v_stop_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; 
v_array_2846_ = lean_ctor_get(v_snd_2842_, 0);
v_start_2847_ = lean_ctor_get(v_snd_2842_, 1);
v_stop_2848_ = lean_ctor_get(v_snd_2842_, 2);
v___x_2849_ = lean_box(0);
v___x_2850_ = lean_nat_dec_lt(v_start_2847_, v_stop_2848_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2852_; 
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v___x_2849_);
v___x_2852_ = v___x_2844_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2849_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_snd_2842_);
v___x_2852_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
lean_object* v___x_2853_; 
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
return v___x_2853_;
}
}
else
{
lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_3025_; 
lean_inc(v_stop_2848_);
lean_inc(v_start_2847_);
lean_inc_ref(v_array_2846_);
v_isSharedCheck_3025_ = !lean_is_exclusive(v_snd_2842_);
if (v_isSharedCheck_3025_ == 0)
{
lean_object* v_unused_3026_; lean_object* v_unused_3027_; lean_object* v_unused_3028_; 
v_unused_3026_ = lean_ctor_get(v_snd_2842_, 2);
lean_dec(v_unused_3026_);
v_unused_3027_ = lean_ctor_get(v_snd_2842_, 1);
lean_dec(v_unused_3027_);
v_unused_3028_ = lean_ctor_get(v_snd_2842_, 0);
lean_dec(v_unused_3028_);
v___x_2856_ = v_snd_2842_;
v_isShared_2857_ = v_isSharedCheck_3025_;
goto v_resetjp_2855_;
}
else
{
lean_dec(v_snd_2842_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_3025_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2862_; 
v___x_2858_ = lean_array_fget(v_array_2846_, v_start_2847_);
v___x_2859_ = lean_unsigned_to_nat(1u);
v___x_2860_ = lean_nat_add(v_start_2847_, v___x_2859_);
lean_dec(v_start_2847_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 1, v___x_2860_);
v___x_2862_ = v___x_2856_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_array_2846_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v___x_2860_);
lean_ctor_set(v_reuseFailAlloc_3024_, 2, v_stop_2848_);
v___x_2862_ = v_reuseFailAlloc_3024_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
uint8_t v___x_2863_; 
v___x_2863_ = lean_unbox(v___x_2858_);
lean_dec(v___x_2858_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2865_; 
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 1, v___x_2862_);
lean_ctor_set(v___x_2844_, 0, v___x_2849_);
v___x_2865_ = v___x_2844_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2849_);
lean_ctor_set(v_reuseFailAlloc_2866_, 1, v___x_2862_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
v_a_2836_ = v___x_2865_;
goto v___jp_2835_;
}
}
else
{
lean_object* v_a_2867_; lean_object* v_____x_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___x_2905_; 
v_a_2867_ = lean_array_uget_borrowed(v_as_2820_, v_i_2822_);
lean_inc(v___y_2833_);
lean_inc_ref(v___y_2832_);
lean_inc(v___y_2831_);
lean_inc_ref(v___y_2830_);
lean_inc(v_a_2867_);
v___x_2905_ = lean_infer_type(v_a_2867_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_3015_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_2908_ = v___x_2905_;
v_isShared_2909_ = v_isSharedCheck_3015_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2905_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_3015_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2910_; 
v___x_2910_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_a_2906_);
if (lean_obj_tag(v___x_2910_) == 1)
{
lean_object* v_val_2911_; lean_object* v_snd_2912_; lean_object* v_fst_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_3009_; 
lean_del_object(v___x_2908_);
v_val_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_val_2911_);
lean_dec_ref_known(v___x_2910_, 1);
v_snd_2912_ = lean_ctor_get(v_val_2911_, 1);
v_fst_2913_ = lean_ctor_get(v_val_2911_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v_val_2911_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_2915_ = v_val_2911_;
v_isShared_2916_ = v_isSharedCheck_3009_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_snd_2912_);
lean_inc(v_fst_2913_);
lean_dec(v_val_2911_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_3009_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v_fst_2917_; lean_object* v_snd_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_3008_; 
v_fst_2917_ = lean_ctor_get(v_snd_2912_, 0);
v_snd_2918_ = lean_ctor_get(v_snd_2912_, 1);
v_isSharedCheck_3008_ = !lean_is_exclusive(v_snd_2912_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_2920_ = v_snd_2912_;
v_isShared_2921_ = v_isSharedCheck_3008_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_snd_2918_);
lean_inc(v_fst_2917_);
lean_dec(v_snd_2912_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_3008_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2922_; 
lean_inc(v_fst_2917_);
v___x_2922_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_fst_2917_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v_options_2978_; uint8_t v_hasTrace_2979_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2923_);
lean_dec_ref_known(v___x_2922_, 1);
v_options_2978_ = lean_ctor_get(v___y_2832_, 2);
v_hasTrace_2979_ = lean_ctor_get_uint8(v_options_2978_, sizeof(void*)*1);
if (v_hasTrace_2979_ == 0)
{
lean_del_object(v___x_2915_);
v___y_2925_ = v___y_2824_;
v___y_2926_ = v___y_2825_;
v___y_2927_ = v___y_2826_;
v___y_2928_ = v___y_2827_;
v___y_2929_ = v___y_2828_;
v___y_2930_ = v___y_2829_;
v___y_2931_ = v___y_2830_;
v___y_2932_ = v___y_2831_;
v___y_2933_ = v___y_2832_;
v___y_2934_ = v___y_2833_;
goto v___jp_2924_;
}
else
{
lean_object* v_inheritedTraceOptions_2980_; lean_object* v_cls_2981_; lean_object* v___x_2982_; uint8_t v___x_2983_; 
v_inheritedTraceOptions_2980_ = lean_ctor_get(v___y_2832_, 13);
v_cls_2981_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2));
v___x_2982_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3);
v___x_2983_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2980_, v_options_2978_, v___x_2982_);
if (v___x_2983_ == 0)
{
lean_del_object(v___x_2915_);
v___y_2925_ = v___y_2824_;
v___y_2926_ = v___y_2825_;
v___y_2927_ = v___y_2826_;
v___y_2928_ = v___y_2827_;
v___y_2929_ = v___y_2828_;
v___y_2930_ = v___y_2829_;
v___y_2931_ = v___y_2830_;
v___y_2932_ = v___y_2831_;
v___y_2933_ = v___y_2832_;
v___y_2934_ = v___y_2833_;
goto v___jp_2924_;
}
else
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2987_; 
lean_inc(v_a_2923_);
v___x_2984_ = l_Lean_MessageData_ofExpr(v_a_2923_);
v___x_2985_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__5);
if (v_isShared_2916_ == 0)
{
lean_ctor_set_tag(v___x_2915_, 7);
lean_ctor_set(v___x_2915_, 1, v___x_2985_);
lean_ctor_set(v___x_2915_, 0, v___x_2984_);
v___x_2987_ = v___x_2915_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2984_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v___x_2985_);
v___x_2987_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
lean_inc(v_snd_2918_);
v___x_2988_ = l_Lean_MessageData_ofExpr(v_snd_2918_);
v___x_2989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2987_);
lean_ctor_set(v___x_2989_, 1, v___x_2988_);
v___x_2990_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_2981_, v___x_2989_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_dec_ref_known(v___x_2990_, 1);
v___y_2925_ = v___y_2824_;
v___y_2926_ = v___y_2825_;
v___y_2927_ = v___y_2826_;
v___y_2928_ = v___y_2827_;
v___y_2929_ = v___y_2828_;
v___y_2930_ = v___y_2829_;
v___y_2931_ = v___y_2830_;
v___y_2932_ = v___y_2831_;
v___y_2933_ = v___y_2832_;
v___y_2934_ = v___y_2833_;
goto v___jp_2924_;
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_dec(v_a_2923_);
lean_del_object(v___x_2920_);
lean_dec(v_snd_2918_);
lean_dec(v_fst_2917_);
lean_dec(v_fst_2913_);
lean_dec_ref(v___x_2862_);
lean_del_object(v___x_2844_);
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2990_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2990_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
}
}
v___jp_2924_:
{
lean_object* v___x_2935_; 
lean_inc(v_a_2923_);
v___x_2935_ = l_Lean_Meta_isDefEqD(v_a_2923_, v_snd_2918_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2969_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2938_ = v___x_2935_;
v_isShared_2939_ = v_isSharedCheck_2969_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2935_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2969_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
uint8_t v___x_2940_; 
v___x_2940_ = lean_unbox(v_a_2936_);
lean_dec(v_a_2936_);
if (v___x_2940_ == 0)
{
lean_object* v___x_2941_; lean_object* v___x_2943_; 
lean_dec(v_a_2923_);
lean_dec(v_fst_2917_);
lean_dec(v_fst_2913_);
lean_del_object(v___x_2844_);
v___x_2941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0));
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 1, v___x_2862_);
lean_ctor_set(v___x_2920_, 0, v___x_2941_);
v___x_2943_ = v___x_2920_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2941_);
lean_ctor_set(v_reuseFailAlloc_2947_, 1, v___x_2862_);
v___x_2943_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
lean_object* v___x_2945_; 
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 0, v___x_2943_);
v___x_2945_ = v___x_2938_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2943_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
else
{
lean_del_object(v___x_2938_);
lean_del_object(v___x_2920_);
if (lean_obj_tag(v_fst_2913_) == 0)
{
uint8_t v___x_2948_; lean_object* v___x_2949_; 
v___x_2948_ = 0;
v___x_2949_ = l_Lean_Meta_Grind_proveEq_x3f(v_fst_2917_, v_a_2923_, v___x_2948_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref_known(v___x_2949_, 1);
v_____x_2869_ = v_a_2950_;
v___y_2870_ = v___y_2931_;
v___y_2871_ = v___y_2932_;
v___y_2872_ = v___y_2933_;
v___y_2873_ = v___y_2934_;
goto v___jp_2868_;
}
else
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
lean_dec_ref(v___x_2862_);
lean_del_object(v___x_2844_);
v_a_2951_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2949_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2949_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_a_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
else
{
lean_object* v___x_2959_; 
lean_dec_ref_known(v_fst_2913_, 1);
v___x_2959_ = l_Lean_Meta_Grind_proveHEq_x3f(v_fst_2917_, v_a_2923_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
lean_dec_ref_known(v___x_2959_, 1);
v_____x_2869_ = v_a_2960_;
v___y_2870_ = v___y_2931_;
v___y_2871_ = v___y_2932_;
v___y_2872_ = v___y_2933_;
v___y_2873_ = v___y_2934_;
goto v___jp_2868_;
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_dec_ref(v___x_2862_);
lean_del_object(v___x_2844_);
v_a_2961_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2959_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2959_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_dec(v_a_2923_);
lean_del_object(v___x_2920_);
lean_dec(v_fst_2917_);
lean_dec(v_fst_2913_);
lean_dec_ref(v___x_2862_);
lean_del_object(v___x_2844_);
v_a_2970_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2935_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2935_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
lean_del_object(v___x_2920_);
lean_dec(v_snd_2918_);
lean_dec(v_fst_2917_);
lean_del_object(v___x_2915_);
lean_dec(v_fst_2913_);
lean_dec_ref(v___x_2862_);
lean_del_object(v___x_2844_);
v_a_3000_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2922_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2922_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
}
}
else
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3013_; 
lean_dec(v___x_2910_);
lean_del_object(v___x_2844_);
v___x_3010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0));
v___x_3011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
lean_ctor_set(v___x_3011_, 1, v___x_2862_);
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 0, v___x_3011_);
v___x_3013_ = v___x_2908_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3011_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec_ref(v___x_2862_);
lean_del_object(v___x_2844_);
v_a_3016_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_2905_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_2905_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
v___jp_2868_:
{
if (lean_obj_tag(v_____x_2869_) == 1)
{
lean_object* v_val_2874_; lean_object* v___x_2875_; 
v_val_2874_ = lean_ctor_get(v_____x_2869_, 0);
lean_inc(v_val_2874_);
lean_dec_ref_known(v_____x_2869_, 1);
lean_inc(v_a_2867_);
v___x_2875_ = l_Lean_Meta_isExprDefEq(v_a_2867_, v_val_2874_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2891_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2891_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2891_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
uint8_t v___x_2880_; 
v___x_2880_ = lean_unbox(v_a_2876_);
lean_dec(v_a_2876_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2881_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0));
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 1, v___x_2862_);
lean_ctor_set(v___x_2844_, 0, v___x_2881_);
v___x_2883_ = v___x_2844_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2881_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v___x_2862_);
v___x_2883_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
lean_object* v___x_2885_; 
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2883_);
v___x_2885_ = v___x_2878_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2883_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
else
{
lean_object* v___x_2889_; 
lean_del_object(v___x_2878_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 1, v___x_2862_);
lean_ctor_set(v___x_2844_, 0, v___x_2849_);
v___x_2889_ = v___x_2844_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2849_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v___x_2862_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
v_a_2836_ = v___x_2889_;
goto v___jp_2835_;
}
}
}
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_dec_ref(v___x_2862_);
lean_del_object(v___x_2844_);
v_a_2892_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2875_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2875_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
else
{
lean_object* v___x_2900_; lean_object* v___x_2902_; 
lean_dec(v_____x_2869_);
v___x_2900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0));
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 1, v___x_2862_);
lean_ctor_set(v___x_2844_, 0, v___x_2900_);
v___x_2902_ = v___x_2844_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2900_);
lean_ctor_set(v_reuseFailAlloc_2904_, 1, v___x_2862_);
v___x_2902_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
lean_object* v___x_2903_; 
v___x_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
return v___x_2903_;
}
}
}
}
}
}
}
}
}
v___jp_2835_:
{
size_t v___x_2837_; size_t v___x_2838_; 
v___x_2837_ = ((size_t)1ULL);
v___x_2838_ = lean_usize_add(v_i_2822_, v___x_2837_);
v_i_2822_ = v___x_2838_;
v_b_2823_ = v_a_2836_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___boxed(lean_object* v_as_3031_, lean_object* v_sz_3032_, lean_object* v_i_3033_, lean_object* v_b_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
size_t v_sz_boxed_3046_; size_t v_i_boxed_3047_; lean_object* v_res_3048_; 
v_sz_boxed_3046_ = lean_unbox_usize(v_sz_3032_);
lean_dec(v_sz_3032_);
v_i_boxed_3047_ = lean_unbox_usize(v_i_3033_);
lean_dec(v_i_3033_);
v_res_3048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(v_as_3031_, v_sz_boxed_3046_, v_i_boxed_3047_, v_b_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec(v___y_3035_);
lean_dec_ref(v_as_3031_);
return v_res_3048_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = ((lean_object*)(l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__0));
v___x_3051_ = l_Lean_stringToMessageData(v___x_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1(lean_object* v_arg_3052_, uint8_t v___x_3053_, lean_object* v_e_3054_, lean_object* v___f_3055_, lean_object* v_cls_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v___x_3068_; 
lean_inc_ref(v_arg_3052_);
v___x_3068_ = l_Lean_Meta_forallMetaTelescope(v_arg_3052_, v___x_3053_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3069_; lean_object* v_fst_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3187_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_a_3069_);
lean_dec_ref_known(v___x_3068_, 1);
v_fst_3070_ = lean_ctor_get(v_a_3069_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v_a_3069_);
if (v_isSharedCheck_3187_ == 0)
{
lean_object* v_unused_3188_; 
v_unused_3188_ = lean_ctor_get(v_a_3069_, 1);
lean_dec(v_unused_3188_);
v___x_3072_ = v_a_3069_;
v_isShared_3073_ = v_isSharedCheck_3187_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_fst_3070_);
lean_dec(v_a_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3187_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3080_; 
v___x_3074_ = l_Lean_Meta_mkGenDiseqMask(v_arg_3052_);
lean_dec_ref(v_arg_3052_);
v___x_3075_ = lean_unsigned_to_nat(0u);
v___x_3076_ = lean_array_get_size(v___x_3074_);
v___x_3077_ = l_Array_toSubarray___redArg(v___x_3074_, v___x_3075_, v___x_3076_);
v___x_3078_ = lean_box(0);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 1, v___x_3077_);
lean_ctor_set(v___x_3072_, 0, v___x_3078_);
v___x_3080_ = v___x_3072_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v___x_3078_);
lean_ctor_set(v_reuseFailAlloc_3186_, 1, v___x_3077_);
v___x_3080_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
size_t v_sz_3081_; size_t v___x_3082_; lean_object* v___x_3083_; 
v_sz_3081_ = lean_array_size(v_fst_3070_);
v___x_3082_ = ((size_t)0ULL);
v___x_3083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(v_fst_3070_, v_sz_3081_, v___x_3082_, v___x_3080_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3177_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3086_ = v___x_3083_;
v_isShared_3087_ = v_isSharedCheck_3177_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3083_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3177_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v_fst_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3175_; 
v_fst_3088_ = lean_ctor_get(v_a_3084_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v_a_3084_);
if (v_isSharedCheck_3175_ == 0)
{
lean_object* v_unused_3176_; 
v_unused_3176_ = lean_ctor_get(v_a_3084_, 1);
lean_dec(v_unused_3176_);
v___x_3090_ = v_a_3084_;
v_isShared_3091_ = v_isSharedCheck_3175_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_fst_3088_);
lean_dec(v_a_3084_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3175_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
if (lean_obj_tag(v_fst_3088_) == 0)
{
lean_object* v___x_3092_; 
lean_del_object(v___x_3086_);
lean_inc_ref(v_e_3054_);
v___x_3092_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_3054_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v_a_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3162_; 
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc(v_a_3093_);
lean_dec_ref_known(v___x_3092_, 1);
v___x_3094_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3054_, v_a_3093_);
v___x_3095_ = l_Lean_mkAppN(v___x_3094_, v_fst_3070_);
lean_dec(v_fst_3070_);
v___x_3096_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(v___x_3095_, v___y_3064_);
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3099_ = v___x_3096_;
v_isShared_3100_ = v_isSharedCheck_3162_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3096_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3162_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3106_; 
lean_inc(v_a_3097_);
v___x_3106_ = l_Lean_Meta_hasAssignableMVar(v_a_3097_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3153_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3109_ = v___x_3106_;
v_isShared_3110_ = v_isSharedCheck_3153_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3153_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
uint8_t v___x_3111_; 
v___x_3111_ = lean_unbox(v_a_3107_);
lean_dec(v_a_3107_);
if (v___x_3111_ == 0)
{
lean_object* v_inheritedTraceOptions_3112_; lean_object* v___x_3113_; 
lean_del_object(v___x_3109_);
v_inheritedTraceOptions_3112_ = lean_ctor_get(v___y_3065_, 13);
lean_inc(v___y_3066_);
lean_inc_ref(v___y_3065_);
lean_inc(v___y_3064_);
lean_inc_ref(v___y_3063_);
lean_inc(v___y_3062_);
lean_inc_ref(v___y_3061_);
lean_inc(v___y_3060_);
lean_inc_ref(v___y_3059_);
lean_inc(v___y_3058_);
lean_inc(v___y_3057_);
lean_inc_ref(v_inheritedTraceOptions_3112_);
v___x_3113_ = lean_apply_12(v___f_3055_, v_inheritedTraceOptions_3112_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, lean_box(0));
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; uint8_t v___x_3115_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3114_);
lean_dec_ref_known(v___x_3113_, 1);
v___x_3115_ = lean_unbox(v_a_3114_);
lean_dec(v_a_3114_);
if (v___x_3115_ == 0)
{
lean_del_object(v___x_3090_);
lean_dec(v_cls_3056_);
goto v___jp_3101_;
}
else
{
lean_object* v___x_3116_; 
lean_inc(v___y_3066_);
lean_inc_ref(v___y_3065_);
lean_inc(v___y_3064_);
lean_inc_ref(v___y_3063_);
lean_inc(v_a_3097_);
v___x_3116_ = lean_infer_type(v_a_3097_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3121_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_a_3117_);
lean_dec_ref_known(v___x_3116_, 1);
lean_inc(v_a_3097_);
v___x_3118_ = l_Lean_MessageData_ofExpr(v_a_3097_);
v___x_3119_ = lean_obj_once(&l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1, &l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1_once, _init_l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1);
if (v_isShared_3091_ == 0)
{
lean_ctor_set_tag(v___x_3090_, 7);
lean_ctor_set(v___x_3090_, 1, v___x_3119_);
lean_ctor_set(v___x_3090_, 0, v___x_3118_);
v___x_3121_ = v___x_3090_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3118_);
lean_ctor_set(v_reuseFailAlloc_3133_, 1, v___x_3119_);
v___x_3121_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3122_ = l_Lean_MessageData_ofExpr(v_a_3117_);
v___x_3123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3121_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
v___x_3124_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3056_, v___x_3123_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_dec_ref_known(v___x_3124_, 1);
goto v___jp_3101_;
}
else
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
lean_del_object(v___x_3099_);
lean_dec(v_a_3097_);
v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_3124_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3124_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3128_ == 0)
{
v___x_3130_ = v___x_3127_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
lean_del_object(v___x_3099_);
lean_dec(v_a_3097_);
lean_del_object(v___x_3090_);
lean_dec(v_cls_3056_);
v_a_3134_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3136_ = v___x_3116_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3116_);
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
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_del_object(v___x_3099_);
lean_dec(v_a_3097_);
lean_del_object(v___x_3090_);
lean_dec(v_cls_3056_);
v_a_3142_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3113_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3113_);
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
else
{
lean_object* v___x_3151_; 
lean_del_object(v___x_3099_);
lean_dec(v_a_3097_);
lean_del_object(v___x_3090_);
lean_dec(v_cls_3056_);
lean_dec_ref(v___f_3055_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 0, v___x_3078_);
v___x_3151_ = v___x_3109_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3078_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_del_object(v___x_3099_);
lean_dec(v_a_3097_);
lean_del_object(v___x_3090_);
lean_dec(v_cls_3056_);
lean_dec_ref(v___f_3055_);
v_a_3154_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3106_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3106_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
v___jp_3101_:
{
lean_object* v___x_3102_; lean_object* v___x_3104_; 
v___x_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3102_, 0, v_a_3097_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 0, v___x_3102_);
v___x_3104_ = v___x_3099_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_del_object(v___x_3090_);
lean_dec(v_fst_3070_);
lean_dec(v_cls_3056_);
lean_dec_ref(v___f_3055_);
lean_dec_ref(v_e_3054_);
v_a_3163_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3092_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3092_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
else
{
lean_object* v_val_3171_; lean_object* v___x_3173_; 
lean_del_object(v___x_3090_);
lean_dec(v_fst_3070_);
lean_dec(v_cls_3056_);
lean_dec_ref(v___f_3055_);
lean_dec_ref(v_e_3054_);
v_val_3171_ = lean_ctor_get(v_fst_3088_, 0);
lean_inc(v_val_3171_);
lean_dec_ref_known(v_fst_3088_, 1);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 0, v_val_3171_);
v___x_3173_ = v___x_3086_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_val_3171_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_dec(v_fst_3070_);
lean_dec(v_cls_3056_);
lean_dec_ref(v___f_3055_);
lean_dec_ref(v_e_3054_);
v_a_3178_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3083_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3083_);
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
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec(v_cls_3056_);
lean_dec_ref(v___f_3055_);
lean_dec_ref(v_e_3054_);
lean_dec_ref(v_arg_3052_);
v_a_3189_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3068_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3068_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1___boxed(lean_object* v_arg_3197_, lean_object* v___x_3198_, lean_object* v_e_3199_, lean_object* v___f_3200_, lean_object* v_cls_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
uint8_t v___x_91763__boxed_3213_; lean_object* v_res_3214_; 
v___x_91763__boxed_3213_ = lean_unbox(v___x_3198_);
v_res_3214_ = l_Lean_Meta_Grind_tryToProveFalse___lam__1(v_arg_3197_, v___x_91763__boxed_3213_, v_e_3199_, v___f_3200_, v_cls_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec(v___y_3202_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse(lean_object* v_e_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_){
_start:
{
lean_object* v_inheritedTraceOptions_3232_; lean_object* v_cls_3233_; lean_object* v___f_3234_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___x_3286_; lean_object* v_a_3287_; uint8_t v___x_3288_; 
v_inheritedTraceOptions_3232_ = lean_ctor_get(v_a_3226_, 13);
v_cls_3233_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2));
v___f_3234_ = ((lean_object*)(l_Lean_Meta_Grind_tryToProveFalse___closed__0));
v___x_3286_ = l_Lean_Meta_Grind_tryToProveFalse___lam__0(v_cls_3233_, v_inheritedTraceOptions_3232_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3287_);
lean_dec_ref(v___x_3286_);
v___x_3288_ = lean_unbox(v_a_3287_);
lean_dec(v_a_3287_);
if (v___x_3288_ == 0)
{
v___y_3236_ = v_a_3218_;
v___y_3237_ = v_a_3219_;
v___y_3238_ = v_a_3220_;
v___y_3239_ = v_a_3221_;
v___y_3240_ = v_a_3222_;
v___y_3241_ = v_a_3223_;
v___y_3242_ = v_a_3224_;
v___y_3243_ = v_a_3225_;
v___y_3244_ = v_a_3226_;
v___y_3245_ = v_a_3227_;
goto v___jp_3235_;
}
else
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Lean_Meta_Grind_updateLastTag(v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v___x_3290_; lean_object* v___x_3291_; 
lean_dec_ref_known(v___x_3289_, 1);
lean_inc_ref(v_e_3217_);
v___x_3290_ = l_Lean_MessageData_ofExpr(v_e_3217_);
v___x_3291_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3233_, v___x_3290_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_dec_ref_known(v___x_3291_, 1);
v___y_3236_ = v_a_3218_;
v___y_3237_ = v_a_3219_;
v___y_3238_ = v_a_3220_;
v___y_3239_ = v_a_3221_;
v___y_3240_ = v_a_3222_;
v___y_3241_ = v_a_3223_;
v___y_3242_ = v_a_3224_;
v___y_3243_ = v_a_3225_;
v___y_3244_ = v_a_3226_;
v___y_3245_ = v_a_3227_;
goto v___jp_3235_;
}
else
{
lean_dec_ref(v_e_3217_);
return v___x_3291_;
}
}
else
{
lean_dec_ref(v_e_3217_);
return v___x_3289_;
}
}
v___jp_3229_:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = lean_box(0);
v___x_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
return v___x_3231_;
}
v___jp_3235_:
{
lean_object* v___x_3246_; 
lean_inc_ref(v_e_3217_);
v___x_3246_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3217_, v___y_3243_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v___x_3248_; uint8_t v___x_3249_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3246_, 1);
v___x_3248_ = l_Lean_Expr_cleanupAnnotations(v_a_3247_);
v___x_3249_ = l_Lean_Expr_isApp(v___x_3248_);
if (v___x_3249_ == 0)
{
lean_dec_ref(v___x_3248_);
lean_dec_ref(v_e_3217_);
goto v___jp_3229_;
}
else
{
lean_object* v_arg_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; uint8_t v___x_3253_; 
v_arg_3250_ = lean_ctor_get(v___x_3248_, 1);
lean_inc_ref(v_arg_3250_);
v___x_3251_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3248_);
v___x_3252_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3253_ = l_Lean_Expr_isConstOf(v___x_3251_, v___x_3252_);
lean_dec_ref(v___x_3251_);
if (v___x_3253_ == 0)
{
lean_dec_ref(v_arg_3250_);
lean_dec_ref(v_e_3217_);
goto v___jp_3229_;
}
else
{
uint8_t v___x_3254_; lean_object* v___x_3255_; lean_object* v___f_3256_; uint8_t v___x_3257_; lean_object* v___x_3258_; 
v___x_3254_ = 0;
v___x_3255_ = lean_box(v___x_3254_);
v___f_3256_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_tryToProveFalse___lam__1___boxed), 16, 5);
lean_closure_set(v___f_3256_, 0, v_arg_3250_);
lean_closure_set(v___f_3256_, 1, v___x_3255_);
lean_closure_set(v___f_3256_, 2, v_e_3217_);
lean_closure_set(v___f_3256_, 3, v___f_3234_);
lean_closure_set(v___f_3256_, 4, v_cls_3233_);
v___x_3257_ = 0;
v___x_3258_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(v___f_3256_, v___x_3257_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3269_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3261_ = v___x_3258_;
v_isShared_3262_ = v_isSharedCheck_3269_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3258_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3269_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
if (lean_obj_tag(v_a_3259_) == 1)
{
lean_object* v_val_3263_; lean_object* v___x_3264_; 
lean_del_object(v___x_3261_);
v_val_3263_ = lean_ctor_get(v_a_3259_, 0);
lean_inc(v_val_3263_);
lean_dec_ref_known(v_a_3259_, 1);
v___x_3264_ = l_Lean_Meta_Grind_closeGoal(v_val_3263_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
return v___x_3264_;
}
else
{
lean_object* v___x_3265_; lean_object* v___x_3267_; 
lean_dec(v_a_3259_);
v___x_3265_ = lean_box(0);
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 0, v___x_3265_);
v___x_3267_ = v___x_3261_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v___x_3265_);
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
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
v_a_3270_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3258_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3258_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
}
}
else
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3285_; 
lean_dec_ref(v_e_3217_);
v_a_3278_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3280_ = v___x_3246_;
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3246_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3283_; 
if (v_isShared_3281_ == 0)
{
v___x_3283_ = v___x_3280_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___boxed(lean_object* v_e_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_);
lean_dec(v_a_3302_);
lean_dec_ref(v_a_3301_);
lean_dec(v_a_3300_);
lean_dec_ref(v_a_3299_);
lean_dec(v_a_3298_);
lean_dec_ref(v_a_3297_);
lean_dec(v_a_3296_);
lean_dec_ref(v_a_3295_);
lean_dec(v_a_3294_);
lean_dec(v_a_3293_);
return v_res_3304_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1(void){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3306_ = ((lean_object*)(l_Lean_Meta_Grind_propagateMatchCondUp___closed__0));
v___x_3307_ = l_Lean_stringToMessageData(v___x_3306_);
return v___x_3307_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3(void){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = ((lean_object*)(l_Lean_Meta_Grind_propagateMatchCondUp___closed__2));
v___x_3310_ = l_Lean_stringToMessageData(v___x_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp(lean_object* v_e_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v_options_3337_; lean_object* v_inheritedTraceOptions_3338_; uint8_t v_hasTrace_3339_; lean_object* v_cls_3340_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; 
v_options_3337_ = lean_ctor_get(v_a_3320_, 2);
v_inheritedTraceOptions_3338_ = lean_ctor_get(v_a_3320_, 13);
v_hasTrace_3339_ = lean_ctor_get_uint8(v_options_3337_, sizeof(void*)*1);
v_cls_3340_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
if (v_hasTrace_3339_ == 0)
{
v___y_3342_ = v_a_3312_;
v___y_3343_ = v_a_3313_;
v___y_3344_ = v_a_3314_;
v___y_3345_ = v_a_3315_;
v___y_3346_ = v_a_3316_;
v___y_3347_ = v_a_3317_;
v___y_3348_ = v_a_3318_;
v___y_3349_ = v_a_3319_;
v___y_3350_ = v_a_3320_;
v___y_3351_ = v_a_3321_;
goto v___jp_3341_;
}
else
{
lean_object* v___x_3447_; uint8_t v___x_3448_; 
v___x_3447_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_3448_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3338_, v_options_3337_, v___x_3447_);
if (v___x_3448_ == 0)
{
v___y_3342_ = v_a_3312_;
v___y_3343_ = v_a_3313_;
v___y_3344_ = v_a_3314_;
v___y_3345_ = v_a_3315_;
v___y_3346_ = v_a_3316_;
v___y_3347_ = v_a_3317_;
v___y_3348_ = v_a_3318_;
v___y_3349_ = v_a_3319_;
v___y_3350_ = v_a_3320_;
v___y_3351_ = v_a_3321_;
goto v___jp_3341_;
}
else
{
lean_object* v___x_3449_; 
v___x_3449_ = l_Lean_Meta_Grind_updateLastTag(v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
lean_dec_ref_known(v___x_3449_, 1);
v___x_3450_ = lean_obj_once(&l_Lean_Meta_Grind_propagateMatchCondUp___closed__3, &l_Lean_Meta_Grind_propagateMatchCondUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3);
lean_inc_ref(v_e_3311_);
v___x_3451_ = l_Lean_indentExpr(v_e_3311_);
v___x_3452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3450_);
lean_ctor_set(v___x_3452_, 1, v___x_3451_);
v___x_3453_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3340_, v___x_3452_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_dec_ref_known(v___x_3453_, 1);
v___y_3342_ = v_a_3312_;
v___y_3343_ = v_a_3313_;
v___y_3344_ = v_a_3314_;
v___y_3345_ = v_a_3315_;
v___y_3346_ = v_a_3316_;
v___y_3347_ = v_a_3317_;
v___y_3348_ = v_a_3318_;
v___y_3349_ = v_a_3319_;
v___y_3350_ = v_a_3320_;
v___y_3351_ = v_a_3321_;
goto v___jp_3341_;
}
else
{
lean_dec_ref(v_e_3311_);
return v___x_3453_;
}
}
else
{
lean_dec_ref(v_e_3311_);
return v___x_3449_;
}
}
}
v___jp_3323_:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3324_ = lean_box(0);
v___x_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
return v___x_3325_;
}
v___jp_3326_:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; 
lean_inc_ref(v_e_3311_);
v___x_3335_ = l_Lean_Meta_mkEqTrueCore(v_e_3311_, v___y_3327_);
v___x_3336_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_3311_, v___x_3335_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
return v___x_3336_;
}
v___jp_3341_:
{
lean_object* v___x_3352_; 
lean_inc_ref(v_e_3311_);
v___x_3352_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3311_, v___y_3342_, v___y_3346_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; uint8_t v___x_3354_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_a_3353_);
lean_dec_ref_known(v___x_3352_, 1);
v___x_3354_ = lean_unbox(v_a_3353_);
lean_dec(v_a_3353_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; 
lean_inc_ref(v_e_3311_);
v___x_3355_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3311_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3410_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3358_ = v___x_3355_;
v_isShared_3359_ = v_isSharedCheck_3410_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3355_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3410_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
uint8_t v___x_3360_; 
v___x_3360_ = lean_unbox(v_a_3356_);
lean_dec(v_a_3356_);
if (v___x_3360_ == 0)
{
lean_object* v___x_3361_; lean_object* v___x_3363_; 
lean_dec_ref(v_e_3311_);
v___x_3361_ = lean_box(0);
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 0, v___x_3361_);
v___x_3363_ = v___x_3358_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3361_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
else
{
lean_object* v___x_3365_; 
lean_del_object(v___x_3358_);
lean_inc_ref(v_e_3311_);
v___x_3365_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_3311_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v_a_3366_; 
v_a_3366_ = lean_ctor_get(v___x_3365_, 0);
lean_inc(v_a_3366_);
lean_dec_ref_known(v___x_3365_, 1);
if (lean_obj_tag(v_a_3366_) == 1)
{
lean_object* v_options_3367_; uint8_t v_hasTrace_3368_; 
v_options_3367_ = lean_ctor_get(v___y_3350_, 2);
v_hasTrace_3368_ = lean_ctor_get_uint8(v_options_3367_, sizeof(void*)*1);
if (v_hasTrace_3368_ == 0)
{
lean_object* v_val_3369_; 
v_val_3369_ = lean_ctor_get(v_a_3366_, 0);
lean_inc(v_val_3369_);
lean_dec_ref_known(v_a_3366_, 1);
v___y_3327_ = v_val_3369_;
v___y_3328_ = v___y_3342_;
v___y_3329_ = v___y_3344_;
v___y_3330_ = v___y_3346_;
v___y_3331_ = v___y_3348_;
v___y_3332_ = v___y_3349_;
v___y_3333_ = v___y_3350_;
v___y_3334_ = v___y_3351_;
goto v___jp_3326_;
}
else
{
lean_object* v_val_3370_; lean_object* v_inheritedTraceOptions_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v_val_3370_ = lean_ctor_get(v_a_3366_, 0);
lean_inc(v_val_3370_);
lean_dec_ref_known(v_a_3366_, 1);
v_inheritedTraceOptions_3371_ = lean_ctor_get(v___y_3350_, 13);
v___x_3372_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_3373_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3371_, v_options_3367_, v___x_3372_);
if (v___x_3373_ == 0)
{
v___y_3327_ = v_val_3370_;
v___y_3328_ = v___y_3342_;
v___y_3329_ = v___y_3344_;
v___y_3330_ = v___y_3346_;
v___y_3331_ = v___y_3348_;
v___y_3332_ = v___y_3349_;
v___y_3333_ = v___y_3350_;
v___y_3334_ = v___y_3351_;
goto v___jp_3326_;
}
else
{
lean_object* v___x_3374_; 
v___x_3374_ = l_Lean_Meta_Grind_updateLastTag(v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v___x_3375_; 
lean_dec_ref_known(v___x_3374_, 1);
lean_inc(v___y_3351_);
lean_inc_ref(v___y_3350_);
lean_inc(v___y_3349_);
lean_inc_ref(v___y_3348_);
lean_inc(v_val_3370_);
v___x_3375_ = lean_infer_type(v_val_3370_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_a_3376_);
lean_dec_ref_known(v___x_3375_, 1);
v___x_3377_ = l_Lean_MessageData_ofExpr(v_a_3376_);
v___x_3378_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3340_, v___x_3377_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_dec_ref_known(v___x_3378_, 1);
v___y_3327_ = v_val_3370_;
v___y_3328_ = v___y_3342_;
v___y_3329_ = v___y_3344_;
v___y_3330_ = v___y_3346_;
v___y_3331_ = v___y_3348_;
v___y_3332_ = v___y_3349_;
v___y_3333_ = v___y_3350_;
v___y_3334_ = v___y_3351_;
goto v___jp_3326_;
}
else
{
lean_dec(v_val_3370_);
lean_dec_ref(v_e_3311_);
return v___x_3378_;
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
lean_dec(v_val_3370_);
lean_dec_ref(v_e_3311_);
v_a_3379_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3375_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3375_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
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
lean_dec(v_val_3370_);
lean_dec_ref(v_e_3311_);
return v___x_3374_;
}
}
}
}
else
{
lean_object* v___x_3387_; 
lean_dec(v_a_3366_);
v___x_3387_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_3346_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; uint8_t v___x_3389_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3388_);
lean_dec_ref_known(v___x_3387_, 1);
v___x_3389_ = lean_unbox(v_a_3388_);
lean_dec(v_a_3388_);
if (v___x_3389_ == 0)
{
lean_dec_ref(v_e_3311_);
goto v___jp_3323_;
}
else
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3390_ = lean_obj_once(&l_Lean_Meta_Grind_propagateMatchCondUp___closed__1, &l_Lean_Meta_Grind_propagateMatchCondUp___closed__1_once, _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1);
v___x_3391_ = l_Lean_indentExpr(v_e_3311_);
v___x_3392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3390_);
lean_ctor_set(v___x_3392_, 1, v___x_3391_);
v___x_3393_ = l_Lean_Meta_Sym_reportIssue(v___x_3392_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_dec_ref_known(v___x_3393_, 1);
goto v___jp_3323_;
}
else
{
return v___x_3393_;
}
}
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
lean_dec_ref(v_e_3311_);
v_a_3394_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3387_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3387_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec_ref(v_e_3311_);
v_a_3402_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3365_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3365_);
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
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec_ref(v_e_3311_);
v_a_3411_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3355_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3355_);
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
else
{
lean_object* v___x_3419_; 
lean_inc_ref(v_e_3311_);
v___x_3419_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3311_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3430_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3422_ = v___x_3419_;
v_isShared_3423_ = v_isSharedCheck_3430_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3419_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3430_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
uint8_t v___x_3424_; 
v___x_3424_ = lean_unbox(v_a_3420_);
lean_dec(v_a_3420_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; 
lean_del_object(v___x_3422_);
v___x_3425_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3311_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
return v___x_3425_;
}
else
{
lean_object* v___x_3426_; lean_object* v___x_3428_; 
lean_dec_ref(v_e_3311_);
v___x_3426_ = lean_box(0);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v___x_3426_);
v___x_3428_ = v___x_3422_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
else
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
lean_dec_ref(v_e_3311_);
v_a_3431_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3433_ = v___x_3419_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3419_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3431_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
}
else
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3446_; 
lean_dec_ref(v_e_3311_);
v_a_3439_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3441_ = v___x_3352_;
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3352_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___boxed(lean_object* v_e_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_){
_start:
{
lean_object* v_res_3466_; 
v_res_3466_ = l_Lean_Meta_Grind_propagateMatchCondUp(v_e_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_);
lean_dec(v_a_3464_);
lean_dec_ref(v_a_3463_);
lean_dec(v_a_3462_);
lean_dec_ref(v_a_3461_);
lean_dec(v_a_3460_);
lean_dec_ref(v_a_3459_);
lean_dec(v_a_3458_);
lean_dec_ref(v_a_3457_);
lean_dec(v_a_3456_);
lean_dec(v_a_3455_);
return v_res_3466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3468_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3469_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondUp___boxed), 12, 0);
v___x_3470_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3468_, v___x_3469_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8____boxed(lean_object* v_a_3471_){
_start:
{
lean_object* v_res_3472_; 
v_res_3472_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_();
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown(lean_object* v_e_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_){
_start:
{
lean_object* v___x_3485_; 
lean_inc_ref(v_e_3473_);
v___x_3485_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3473_, v_a_3474_, v_a_3478_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3515_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3488_ = v___x_3485_;
v_isShared_3489_ = v_isSharedCheck_3515_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3485_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3515_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
uint8_t v___x_3490_; 
v___x_3490_ = lean_unbox(v_a_3486_);
lean_dec(v_a_3486_);
if (v___x_3490_ == 0)
{
lean_object* v___x_3491_; lean_object* v___x_3493_; 
lean_dec_ref(v_e_3473_);
v___x_3491_ = lean_box(0);
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 0, v___x_3491_);
v___x_3493_ = v___x_3488_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3491_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
else
{
lean_object* v___x_3495_; 
lean_del_object(v___x_3488_);
lean_inc_ref(v_e_3473_);
v___x_3495_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3506_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3498_ = v___x_3495_;
v_isShared_3499_ = v_isSharedCheck_3506_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3495_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3506_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
uint8_t v___x_3500_; 
v___x_3500_ = lean_unbox(v_a_3496_);
lean_dec(v_a_3496_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; 
lean_del_object(v___x_3498_);
v___x_3501_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
return v___x_3501_;
}
else
{
lean_object* v___x_3502_; lean_object* v___x_3504_; 
lean_dec_ref(v_e_3473_);
v___x_3502_ = lean_box(0);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 0, v___x_3502_);
v___x_3504_ = v___x_3498_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3502_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
else
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3514_; 
lean_dec_ref(v_e_3473_);
v_a_3507_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3509_ = v___x_3495_;
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3495_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_a_3507_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
}
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
lean_dec_ref(v_e_3473_);
v_a_3516_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3485_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3485_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___boxed(lean_object* v_e_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Lean_Meta_Grind_propagateMatchCondDown(v_e_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec_ref(v_a_3529_);
lean_dec(v_a_3528_);
lean_dec_ref(v_a_3527_);
lean_dec(v_a_3526_);
lean_dec(v_a_3525_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3538_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3539_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondDown___boxed), 12, 0);
v___x_3540_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3538_, v___x_3539_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8____boxed(lean_object* v_a_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_();
return v_res_3542_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ProveEq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MatchCond(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_();
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
