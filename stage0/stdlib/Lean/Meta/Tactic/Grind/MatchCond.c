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
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_bool_not(uint8_t);
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
v___x_414_ = l_Lean_Meta_Sym_shareCommon(v___x_413_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
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
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_872_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_872_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_872_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_872_;
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
lean_dec(v_a_747_);
if (v___x_748_ == 0)
{
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
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_762_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_762_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_762_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_762_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
uint8_t v___x_756_; uint8_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_756_ = lean_expr_eqv(v_a_750_, v_a_752_);
lean_dec(v_a_752_);
lean_dec(v_a_750_);
v___x_757_ = lean_bool_not(v___x_756_);
v___x_758_ = lean_box(v___x_757_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_758_);
v___x_760_ = v___x_754_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_a_750_);
v_a_763_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_751_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_751_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v_rhs_720_);
v_a_771_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_749_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_749_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
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
lean_object* v___x_779_; lean_object* v___x_781_; 
lean_dec_ref(v_self_744_);
lean_dec_ref(v_rhs_720_);
v___x_779_ = lean_box(v_ctor_738_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_779_);
v___x_781_ = v___x_736_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v_self_783_; lean_object* v___x_784_; 
lean_del_object(v___x_736_);
v_self_783_ = lean_ctor_get(v_a_734_, 0);
lean_inc_ref_n(v_self_783_, 2);
lean_dec(v_a_734_);
v___x_784_ = l_Lean_Meta_isConstructorApp_x3f(v_self_783_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_863_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_863_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_863_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_863_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
if (lean_obj_tag(v_a_785_) == 1)
{
lean_object* v_val_789_; lean_object* v___x_790_; 
lean_del_object(v___x_787_);
v_val_789_ = lean_ctor_get(v_a_785_, 0);
lean_inc(v_val_789_);
lean_dec_ref_known(v_a_785_, 1);
lean_inc_ref(v_rhs_720_);
v___x_790_ = l_Lean_Meta_isConstructorApp_x3f(v_rhs_720_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_850_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_850_ == 0)
{
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_850_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_850_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
if (lean_obj_tag(v_a_791_) == 1)
{
lean_object* v_toConstantVal_795_; lean_object* v_val_796_; lean_object* v_toConstantVal_797_; lean_object* v_numParams_798_; lean_object* v_numFields_799_; lean_object* v_name_800_; lean_object* v_name_801_; uint8_t v___x_802_; 
v_toConstantVal_795_ = lean_ctor_get(v_val_789_, 0);
lean_inc_ref(v_toConstantVal_795_);
v_val_796_ = lean_ctor_get(v_a_791_, 0);
lean_inc(v_val_796_);
lean_dec_ref_known(v_a_791_, 1);
v_toConstantVal_797_ = lean_ctor_get(v_val_796_, 0);
lean_inc_ref(v_toConstantVal_797_);
lean_dec(v_val_796_);
v_numParams_798_ = lean_ctor_get(v_val_789_, 3);
lean_inc(v_numParams_798_);
v_numFields_799_ = lean_ctor_get(v_val_789_, 4);
lean_inc(v_numFields_799_);
lean_dec(v_val_789_);
v_name_800_ = lean_ctor_get(v_toConstantVal_795_, 0);
lean_inc(v_name_800_);
lean_dec_ref(v_toConstantVal_795_);
v_name_801_ = lean_ctor_get(v_toConstantVal_797_, 0);
lean_inc(v_name_801_);
lean_dec_ref(v_toConstantVal_797_);
v___x_802_ = lean_name_eq(v_name_800_, v_name_801_);
lean_dec(v_name_801_);
lean_dec(v_name_800_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_805_; 
lean_dec(v_numFields_799_);
lean_dec(v_numParams_798_);
lean_dec_ref(v_self_783_);
lean_dec_ref(v_rhs_720_);
v___x_803_ = lean_box(v_ctor_738_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_803_);
v___x_805_ = v___x_793_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
else
{
if (v___x_732_ == 0)
{
lean_object* v_nargs_807_; lean_object* v_nargs_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v_dummy_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
lean_del_object(v___x_793_);
v_nargs_807_ = l_Lean_Expr_getAppNumArgs(v_self_783_);
v_nargs_808_ = l_Lean_Expr_getAppNumArgs(v_rhs_720_);
v___x_809_ = lean_nat_add(v_numParams_798_, v_numFields_799_);
lean_dec(v_numFields_799_);
v___x_810_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0));
v_dummy_811_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0);
lean_inc(v_nargs_807_);
v___x_812_ = lean_mk_array(v_nargs_807_, v_dummy_811_);
v___x_813_ = lean_unsigned_to_nat(1u);
v___x_814_ = lean_nat_sub(v_nargs_807_, v___x_813_);
lean_dec(v_nargs_807_);
v___x_815_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_783_, v___x_812_, v___x_814_);
lean_inc(v_nargs_808_);
v___x_816_ = lean_mk_array(v_nargs_808_, v_dummy_811_);
v___x_817_ = lean_nat_sub(v_nargs_808_, v___x_813_);
lean_dec(v_nargs_808_);
v___x_818_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_rhs_720_, v___x_816_, v___x_817_);
v___x_819_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v___x_809_, v___x_815_, v___x_818_, v_ctor_738_, v_numParams_798_, v___x_810_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
lean_dec_ref(v___x_818_);
lean_dec_ref(v___x_815_);
lean_dec(v___x_809_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_833_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_833_ == 0)
{
v___x_822_ = v___x_819_;
v_isShared_823_ = v_isSharedCheck_833_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_833_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v_fst_824_; 
v_fst_824_ = lean_ctor_get(v_a_820_, 0);
lean_inc(v_fst_824_);
lean_dec(v_a_820_);
if (lean_obj_tag(v_fst_824_) == 0)
{
lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_825_ = lean_box(v___x_732_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_825_);
v___x_827_ = v___x_822_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
else
{
lean_object* v_val_829_; lean_object* v___x_831_; 
v_val_829_ = lean_ctor_get(v_fst_824_, 0);
lean_inc(v_val_829_);
lean_dec_ref_known(v_fst_824_, 1);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v_val_829_);
v___x_831_ = v___x_822_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_val_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
v_a_834_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_819_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_819_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
else
{
lean_object* v___x_842_; lean_object* v___x_844_; 
lean_dec(v_numFields_799_);
lean_dec(v_numParams_798_);
lean_dec_ref(v_self_783_);
lean_dec_ref(v_rhs_720_);
v___x_842_ = lean_box(v_ctor_738_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_842_);
v___x_844_ = v___x_793_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
else
{
lean_object* v___x_846_; lean_object* v___x_848_; 
lean_dec(v_a_791_);
lean_dec(v_val_789_);
lean_dec_ref(v_self_783_);
lean_dec_ref(v_rhs_720_);
v___x_846_ = lean_box(v___x_732_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_846_);
v___x_848_ = v___x_793_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec(v_val_789_);
lean_dec_ref(v_self_783_);
lean_dec_ref(v_rhs_720_);
v_a_851_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_790_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_790_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
else
{
lean_object* v___x_859_; lean_object* v___x_861_; 
lean_dec(v_a_785_);
lean_dec_ref(v_self_783_);
lean_dec_ref(v_rhs_720_);
v___x_859_ = lean_box(v___x_732_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_859_);
v___x_861_ = v___x_787_;
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
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_dec_ref(v_self_783_);
lean_dec_ref(v_rhs_720_);
v_a_864_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_784_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_784_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec_ref(v_rhs_720_);
v_a_873_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_733_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_733_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
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
uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
lean_dec_ref(v_rhs_720_);
lean_dec_ref(v_lhs_719_);
v___x_881_ = 0;
v___x_882_ = lean_box(v___x_881_);
v___x_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
return v___x_883_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(lean_object* v_upperBound_884_, lean_object* v___x_885_, lean_object* v___x_886_, uint8_t v___x_887_, lean_object* v_a_888_, lean_object* v_b_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
uint8_t v___x_901_; 
v___x_901_ = lean_nat_dec_lt(v_a_888_, v_upperBound_884_);
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
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
lean_dec_ref(v_b_889_);
v___x_903_ = l_Lean_instInhabitedExpr;
v___x_904_ = lean_array_get_borrowed(v___x_903_, v___x_885_, v_a_888_);
v___x_905_ = lean_array_get_borrowed(v___x_903_, v___x_886_, v_a_888_);
lean_inc(v___x_905_);
lean_inc(v___x_904_);
v___x_906_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v___x_904_, v___x_905_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_923_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_923_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_923_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_923_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_911_ = lean_box(0);
v___x_912_ = lean_unbox(v_a_907_);
lean_dec(v_a_907_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
lean_del_object(v___x_909_);
v___x_913_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0));
v___x_914_ = lean_unsigned_to_nat(1u);
v___x_915_ = lean_nat_add(v_a_888_, v___x_914_);
lean_dec(v_a_888_);
v_a_888_ = v___x_915_;
v_b_889_ = v___x_913_;
goto _start;
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
lean_dec(v_a_888_);
v___x_917_ = lean_box(v___x_887_);
v___x_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
lean_ctor_set(v___x_919_, 1, v___x_911_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_919_);
v___x_921_ = v___x_909_;
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
v_a_924_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_906_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_906_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_932_ = _args[0];
lean_object* v___x_933_ = _args[1];
lean_object* v___x_934_ = _args[2];
lean_object* v___x_935_ = _args[3];
lean_object* v_a_936_ = _args[4];
lean_object* v_b_937_ = _args[5];
lean_object* v___y_938_ = _args[6];
lean_object* v___y_939_ = _args[7];
lean_object* v___y_940_ = _args[8];
lean_object* v___y_941_ = _args[9];
lean_object* v___y_942_ = _args[10];
lean_object* v___y_943_ = _args[11];
lean_object* v___y_944_ = _args[12];
lean_object* v___y_945_ = _args[13];
lean_object* v___y_946_ = _args[14];
lean_object* v___y_947_ = _args[15];
lean_object* v___y_948_ = _args[16];
_start:
{
uint8_t v___x_28831__boxed_949_; lean_object* v_res_950_; 
v___x_28831__boxed_949_ = lean_unbox(v___x_935_);
v_res_950_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v_upperBound_932_, v___x_933_, v___x_934_, v___x_28831__boxed_949_, v_a_936_, v_b_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___x_934_);
lean_dec_ref(v___x_933_);
lean_dec(v_upperBound_932_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___boxed(lean_object* v_lhs_951_, lean_object* v_rhs_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v_lhs_951_, v_rhs_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec(v_a_953_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(lean_object* v_upperBound_965_, lean_object* v___x_966_, lean_object* v___x_967_, uint8_t v___x_968_, lean_object* v_inst_969_, lean_object* v_R_970_, lean_object* v_a_971_, lean_object* v_b_972_, lean_object* v_c_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v_upperBound_965_, v___x_966_, v___x_967_, v___x_968_, v_a_971_, v_b_972_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_986_ = _args[0];
lean_object* v___x_987_ = _args[1];
lean_object* v___x_988_ = _args[2];
lean_object* v___x_989_ = _args[3];
lean_object* v_inst_990_ = _args[4];
lean_object* v_R_991_ = _args[5];
lean_object* v_a_992_ = _args[6];
lean_object* v_b_993_ = _args[7];
lean_object* v_c_994_ = _args[8];
lean_object* v___y_995_ = _args[9];
lean_object* v___y_996_ = _args[10];
lean_object* v___y_997_ = _args[11];
lean_object* v___y_998_ = _args[12];
lean_object* v___y_999_ = _args[13];
lean_object* v___y_1000_ = _args[14];
lean_object* v___y_1001_ = _args[15];
lean_object* v___y_1002_ = _args[16];
lean_object* v___y_1003_ = _args[17];
lean_object* v___y_1004_ = _args[18];
lean_object* v___y_1005_ = _args[19];
_start:
{
uint8_t v___x_29223__boxed_1006_; lean_object* v_res_1007_; 
v___x_29223__boxed_1006_ = lean_unbox(v___x_989_);
v_res_1007_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(v_upperBound_986_, v___x_987_, v___x_988_, v___x_29223__boxed_1006_, v_inst_990_, v_R_991_, v_a_992_, v_b_993_, v_c_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___x_988_);
lean_dec_ref(v___x_987_);
lean_dec(v_upperBound_986_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(lean_object* v_e_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_e_1008_);
if (lean_obj_tag(v___x_1020_) == 1)
{
lean_object* v_val_1021_; lean_object* v_snd_1022_; lean_object* v_fst_1023_; lean_object* v_snd_1024_; lean_object* v___x_1025_; 
v_val_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_val_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v_snd_1022_ = lean_ctor_get(v_val_1021_, 1);
lean_inc(v_snd_1022_);
lean_dec(v_val_1021_);
v_fst_1023_ = lean_ctor_get(v_snd_1022_, 0);
lean_inc(v_fst_1023_);
v_snd_1024_ = lean_ctor_get(v_snd_1022_, 1);
lean_inc(v_snd_1024_);
lean_dec(v_snd_1022_);
v___x_1025_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v_fst_1023_, v_snd_1024_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1025_;
}
else
{
uint8_t v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_dec(v___x_1020_);
v___x_1026_ = 0;
v___x_1027_ = lean_box(v___x_1026_);
v___x_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
return v___x_1028_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp___boxed(lean_object* v_e_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_e_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec(v_a_1031_);
lean_dec(v_a_1030_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(uint8_t v___x_1042_, lean_object* v_snd_1043_, lean_object* v_____r_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1056_ = lean_box(v___x_1042_);
v___x_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v_snd_1043_);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
v___x_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0___boxed(lean_object* v___x_1061_, lean_object* v_snd_1062_, lean_object* v_____r_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
uint8_t v___x_32338__boxed_1075_; lean_object* v_res_1076_; 
v___x_32338__boxed_1075_ = lean_unbox(v___x_1061_);
v_res_1076_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_32338__boxed_1075_, v_snd_1062_, v_____r_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec(v___y_1064_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(lean_object* v_msgData_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v___x_1083_; lean_object* v_env_1084_; lean_object* v___x_1085_; lean_object* v_mctx_1086_; lean_object* v_lctx_1087_; lean_object* v_options_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1083_ = lean_st_ref_get(v___y_1081_);
v_env_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc_ref(v_env_1084_);
lean_dec(v___x_1083_);
v___x_1085_ = lean_st_ref_get(v___y_1079_);
v_mctx_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc_ref(v_mctx_1086_);
lean_dec(v___x_1085_);
v_lctx_1087_ = lean_ctor_get(v___y_1078_, 2);
v_options_1088_ = lean_ctor_get(v___y_1080_, 2);
lean_inc_ref(v_options_1088_);
lean_inc_ref(v_lctx_1087_);
v___x_1089_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1089_, 0, v_env_1084_);
lean_ctor_set(v___x_1089_, 1, v_mctx_1086_);
lean_ctor_set(v___x_1089_, 2, v_lctx_1087_);
lean_ctor_set(v___x_1089_, 3, v_options_1088_);
v___x_1090_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
lean_ctor_set(v___x_1090_, 1, v_msgData_1077_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0___boxed(lean_object* v_msgData_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(v_msgData_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
return v_res_1098_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1099_; double v___x_1100_; 
v___x_1099_ = lean_unsigned_to_nat(0u);
v___x_1100_ = lean_float_of_nat(v___x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(lean_object* v_cls_1104_, lean_object* v_msg_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_ref_1111_; lean_object* v___x_1112_; lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1157_; 
v_ref_1111_ = lean_ctor_get(v___y_1108_, 5);
v___x_1112_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(v_msg_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1115_ = v___x_1112_;
v_isShared_1116_ = v_isSharedCheck_1157_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1157_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v_traceState_1118_; lean_object* v_env_1119_; lean_object* v_nextMacroScope_1120_; lean_object* v_ngen_1121_; lean_object* v_auxDeclNGen_1122_; lean_object* v_cache_1123_; lean_object* v_messages_1124_; lean_object* v_infoState_1125_; lean_object* v_snapshotTasks_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1156_; 
v___x_1117_ = lean_st_ref_take(v___y_1109_);
v_traceState_1118_ = lean_ctor_get(v___x_1117_, 4);
v_env_1119_ = lean_ctor_get(v___x_1117_, 0);
v_nextMacroScope_1120_ = lean_ctor_get(v___x_1117_, 1);
v_ngen_1121_ = lean_ctor_get(v___x_1117_, 2);
v_auxDeclNGen_1122_ = lean_ctor_get(v___x_1117_, 3);
v_cache_1123_ = lean_ctor_get(v___x_1117_, 5);
v_messages_1124_ = lean_ctor_get(v___x_1117_, 6);
v_infoState_1125_ = lean_ctor_get(v___x_1117_, 7);
v_snapshotTasks_1126_ = lean_ctor_get(v___x_1117_, 8);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1128_ = v___x_1117_;
v_isShared_1129_ = v_isSharedCheck_1156_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_snapshotTasks_1126_);
lean_inc(v_infoState_1125_);
lean_inc(v_messages_1124_);
lean_inc(v_cache_1123_);
lean_inc(v_traceState_1118_);
lean_inc(v_auxDeclNGen_1122_);
lean_inc(v_ngen_1121_);
lean_inc(v_nextMacroScope_1120_);
lean_inc(v_env_1119_);
lean_dec(v___x_1117_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1156_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
uint64_t v_tid_1130_; lean_object* v_traces_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1155_; 
v_tid_1130_ = lean_ctor_get_uint64(v_traceState_1118_, sizeof(void*)*1);
v_traces_1131_ = lean_ctor_get(v_traceState_1118_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_traceState_1118_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1133_ = v_traceState_1118_;
v_isShared_1134_ = v_isSharedCheck_1155_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_traces_1131_);
lean_dec(v_traceState_1118_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1155_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; double v___x_1136_; uint8_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0);
v___x_1137_ = 0;
v___x_1138_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1));
v___x_1139_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1139_, 0, v_cls_1104_);
lean_ctor_set(v___x_1139_, 1, v___x_1135_);
lean_ctor_set(v___x_1139_, 2, v___x_1138_);
lean_ctor_set_float(v___x_1139_, sizeof(void*)*3, v___x_1136_);
lean_ctor_set_float(v___x_1139_, sizeof(void*)*3 + 8, v___x_1136_);
lean_ctor_set_uint8(v___x_1139_, sizeof(void*)*3 + 16, v___x_1137_);
v___x_1140_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__2));
v___x_1141_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1139_);
lean_ctor_set(v___x_1141_, 1, v_a_1113_);
lean_ctor_set(v___x_1141_, 2, v___x_1140_);
lean_inc(v_ref_1111_);
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v_ref_1111_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = l_Lean_PersistentArray_push___redArg(v_traces_1131_, v___x_1142_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1143_);
v___x_1145_ = v___x_1133_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1143_);
lean_ctor_set_uint64(v_reuseFailAlloc_1154_, sizeof(void*)*1, v_tid_1130_);
v___x_1145_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 4, v___x_1145_);
v___x_1147_ = v___x_1128_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_env_1119_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_nextMacroScope_1120_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_ngen_1121_);
lean_ctor_set(v_reuseFailAlloc_1153_, 3, v_auxDeclNGen_1122_);
lean_ctor_set(v_reuseFailAlloc_1153_, 4, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1153_, 5, v_cache_1123_);
lean_ctor_set(v_reuseFailAlloc_1153_, 6, v_messages_1124_);
lean_ctor_set(v_reuseFailAlloc_1153_, 7, v_infoState_1125_);
lean_ctor_set(v_reuseFailAlloc_1153_, 8, v_snapshotTasks_1126_);
v___x_1147_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1148_ = lean_st_ref_set(v___y_1109_, v___x_1147_);
v___x_1149_ = lean_box(0);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1149_);
v___x_1151_ = v___x_1115_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___boxed(lean_object* v_cls_1158_, lean_object* v_msg_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1158_, v_msg_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
return v_res_1165_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1176_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_1177_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5));
v___x_1178_ = l_Lean_Name_append(v___x_1177_, v___x_1176_);
return v___x_1178_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__7));
v___x_1181_ = l_Lean_stringToMessageData(v___x_1180_);
return v___x_1181_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10(void){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__9));
v___x_1184_ = l_Lean_stringToMessageData(v___x_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(uint8_t v___x_1185_, lean_object* v_a_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___y_1199_; lean_object* v_snd_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1281_; 
v_snd_1219_ = lean_ctor_get(v_a_1186_, 1);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_a_1186_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v_a_1186_, 0);
lean_dec(v_unused_1282_);
v___x_1221_ = v_a_1186_;
v_isShared_1222_ = v_isSharedCheck_1281_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_snd_1219_);
lean_dec(v_a_1186_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1281_;
goto v_resetjp_1220_;
}
v___jp_1198_:
{
if (lean_obj_tag(v___y_1199_) == 0)
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1210_; 
v_a_1200_ = lean_ctor_get(v___y_1199_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___y_1199_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1202_ = v___y_1199_;
v_isShared_1203_ = v_isSharedCheck_1210_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___y_1199_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1210_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
if (lean_obj_tag(v_a_1200_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1206_; 
v_a_1204_ = lean_ctor_get(v_a_1200_, 0);
lean_inc(v_a_1204_);
lean_dec_ref_known(v_a_1200_, 1);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v_a_1204_);
v___x_1206_ = v___x_1202_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
else
{
lean_object* v_a_1208_; 
lean_del_object(v___x_1202_);
v_a_1208_ = lean_ctor_get(v_a_1200_, 0);
lean_inc(v_a_1208_);
lean_dec_ref_known(v_a_1200_, 1);
v_a_1186_ = v_a_1208_;
goto _start;
}
}
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
v_a_1211_ = lean_ctor_get(v___y_1199_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___y_1199_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___y_1199_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___y_1199_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_box(0);
if (lean_obj_tag(v_snd_1219_) == 7)
{
lean_object* v_binderType_1224_; lean_object* v_body_1225_; lean_object* v___x_1226_; 
v_binderType_1224_ = lean_ctor_get(v_snd_1219_, 1);
v_body_1225_ = lean_ctor_get(v_snd_1219_, 2);
lean_inc_ref(v_binderType_1224_);
v___x_1226_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_binderType_1224_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; uint8_t v___x_1228_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v___x_1226_, 1);
v___x_1228_ = lean_unbox(v_a_1227_);
lean_dec(v_a_1227_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1230_; 
lean_inc_ref(v_body_1225_);
lean_dec_ref_known(v_snd_1219_, 3);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 1, v_body_1225_);
lean_ctor_set(v___x_1221_, 0, v___x_1223_);
v___x_1230_ = v___x_1221_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_body_1225_);
v___x_1230_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
v_a_1186_ = v___x_1230_;
goto _start;
}
}
else
{
lean_object* v_options_1233_; lean_object* v_inheritedTraceOptions_1234_; uint8_t v_hasTrace_1235_; 
lean_del_object(v___x_1221_);
v_options_1233_ = lean_ctor_get(v___y_1195_, 2);
v_inheritedTraceOptions_1234_ = lean_ctor_get(v___y_1195_, 13);
v_hasTrace_1235_ = lean_ctor_get_uint8(v_options_1233_, sizeof(void*)*1);
if (v_hasTrace_1235_ == 0)
{
goto v___jp_1236_;
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___x_1239_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_1240_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_1241_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1234_, v_options_1233_, v___x_1240_);
if (v___x_1241_ == 0)
{
goto v___jp_1236_;
}
else
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_Meta_Grind_updateLastTag(v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_dec_ref_known(v___x_1242_, 1);
v___x_1243_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8);
lean_inc_ref(v_snd_1219_);
v___x_1244_ = l_Lean_indentExpr(v_snd_1219_);
v___x_1245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1243_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
v___x_1246_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10);
v___x_1247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1245_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
lean_inc_ref(v_binderType_1224_);
v___x_1248_ = l_Lean_indentExpr(v_binderType_1224_);
v___x_1249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_1239_, v___x_1249_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v___x_1252_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
lean_dec_ref_known(v___x_1250_, 1);
v___x_1252_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_1185_, v_snd_1219_, v_a_1251_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
v___y_1199_ = v___x_1252_;
goto v___jp_1198_;
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec_ref_known(v_snd_1219_, 3);
v_a_1253_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1250_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1250_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_dec_ref_known(v_snd_1219_, 3);
v_a_1261_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1242_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1242_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
v___jp_1236_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = lean_box(0);
v___x_1238_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_1185_, v_snd_1219_, v___x_1237_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
v___y_1199_ = v___x_1238_;
goto v___jp_1198_;
}
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec_ref_known(v_snd_1219_, 3);
lean_del_object(v___x_1221_);
v_a_1269_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1226_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1226_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
else
{
lean_object* v___x_1278_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1223_);
v___x_1278_ = v___x_1221_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_snd_1219_);
v___x_1278_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1279_; 
v___x_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
return v___x_1279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___boxed(lean_object* v___x_1283_, lean_object* v_a_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
uint8_t v___x_32551__boxed_1296_; lean_object* v_res_1297_; 
v___x_32551__boxed_1296_ = lean_unbox(v___x_1283_);
v_res_1297_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_32551__boxed_1296_, v_a_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec(v___y_1285_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(lean_object* v_e_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1298_, v_a_1306_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1353_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1353_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1353_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1321_ = l_Lean_Expr_cleanupAnnotations(v_a_1311_);
v___x_1322_ = l_Lean_Expr_isApp(v___x_1321_);
if (v___x_1322_ == 0)
{
lean_dec_ref(v___x_1321_);
goto v___jp_1315_;
}
else
{
lean_object* v_arg_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v_arg_1323_ = lean_ctor_get(v___x_1321_, 1);
lean_inc_ref(v_arg_1323_);
v___x_1324_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1321_);
v___x_1325_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_1326_ = l_Lean_Expr_isConstOf(v___x_1324_, v___x_1325_);
lean_dec_ref(v___x_1324_);
if (v___x_1326_ == 0)
{
lean_dec_ref(v_arg_1323_);
goto v___jp_1315_;
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
lean_del_object(v___x_1313_);
v___x_1327_ = lean_box(0);
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
lean_ctor_set(v___x_1328_, 1, v_arg_1323_);
v___x_1329_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_1326_, v___x_1328_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1344_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1344_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1344_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v_fst_1334_; 
v_fst_1334_ = lean_ctor_get(v_a_1330_, 0);
lean_inc(v_fst_1334_);
lean_dec(v_a_1330_);
if (lean_obj_tag(v_fst_1334_) == 0)
{
uint8_t v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1335_ = 0;
v___x_1336_ = lean_box(v___x_1335_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1336_);
v___x_1338_ = v___x_1332_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
else
{
lean_object* v_val_1340_; lean_object* v___x_1342_; 
v_val_1340_ = lean_ctor_get(v_fst_1334_, 0);
lean_inc(v_val_1340_);
lean_dec_ref_known(v_fst_1334_, 1);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v_val_1340_);
v___x_1342_ = v___x_1332_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_val_1340_);
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
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
v_a_1345_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1329_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1329_);
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
}
}
v___jp_1315_:
{
uint8_t v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1316_ = 0;
v___x_1317_ = lean_box(v___x_1316_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1317_);
v___x_1319_ = v___x_1313_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
v_a_1354_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1310_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1310_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied___boxed(lean_object* v_e_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec(v_a_1363_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(lean_object* v_cls_1375_, lean_object* v_msg_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1375_, v_msg_1376_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___boxed(lean_object* v_cls_1389_, lean_object* v_msg_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(v_cls_1389_, v_msg_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec(v___y_1391_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(uint8_t v___x_1403_, lean_object* v_inst_1404_, lean_object* v_a_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_1403_, v_a_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___boxed(lean_object* v___x_1418_, lean_object* v_inst_1419_, lean_object* v_a_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
uint8_t v___x_32922__boxed_1432_; lean_object* v_res_1433_; 
v___x_32922__boxed_1432_ = lean_unbox(v___x_1418_);
v_res_1433_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(v___x_32922__boxed_1432_, v_inst_1419_, v_a_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec(v___y_1421_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(lean_object* v_k_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v_b_1441_, lean_object* v_c_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v___x_1448_; 
lean_inc(v___y_1446_);
lean_inc_ref(v___y_1445_);
lean_inc(v___y_1444_);
lean_inc_ref(v___y_1443_);
lean_inc(v___y_1440_);
lean_inc_ref(v___y_1439_);
lean_inc(v___y_1438_);
lean_inc_ref(v___y_1437_);
lean_inc(v___y_1436_);
lean_inc(v___y_1435_);
v___x_1448_ = lean_apply_13(v_k_1434_, v_b_1441_, v_c_1442_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, lean_box(0));
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed(lean_object* v_k_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v_b_1456_, lean_object* v_c_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(v_k_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v_b_1456_, v_c_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec(v___y_1450_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(lean_object* v_type_1464_, lean_object* v_k_1465_, uint8_t v_cleanupAnnotations_1466_, uint8_t v_whnfType_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___f_1479_; lean_object* v___x_1480_; 
lean_inc(v___y_1473_);
lean_inc_ref(v___y_1472_);
lean_inc(v___y_1471_);
lean_inc_ref(v___y_1470_);
lean_inc(v___y_1469_);
lean_inc(v___y_1468_);
v___f_1479_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1479_, 0, v_k_1465_);
lean_closure_set(v___f_1479_, 1, v___y_1468_);
lean_closure_set(v___f_1479_, 2, v___y_1469_);
lean_closure_set(v___f_1479_, 3, v___y_1470_);
lean_closure_set(v___f_1479_, 4, v___y_1471_);
lean_closure_set(v___f_1479_, 5, v___y_1472_);
lean_closure_set(v___f_1479_, 6, v___y_1473_);
v___x_1480_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1464_, v___f_1479_, v_cleanupAnnotations_1466_, v_whnfType_1467_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
if (lean_obj_tag(v___x_1480_) == 0)
{
return v___x_1480_;
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___boxed(lean_object* v_type_1489_, lean_object* v_k_1490_, lean_object* v_cleanupAnnotations_1491_, lean_object* v_whnfType_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1504_; uint8_t v_whnfType_boxed_1505_; lean_object* v_res_1506_; 
v_cleanupAnnotations_boxed_1504_ = lean_unbox(v_cleanupAnnotations_1491_);
v_whnfType_boxed_1505_ = lean_unbox(v_whnfType_1492_);
v_res_1506_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_1489_, v_k_1490_, v_cleanupAnnotations_boxed_1504_, v_whnfType_boxed_1505_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec(v___y_1493_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(lean_object* v_00_u03b1_1507_, lean_object* v_type_1508_, lean_object* v_k_1509_, uint8_t v_cleanupAnnotations_1510_, uint8_t v_whnfType_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_1508_, v_k_1509_, v_cleanupAnnotations_1510_, v_whnfType_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___boxed(lean_object* v_00_u03b1_1524_, lean_object* v_type_1525_, lean_object* v_k_1526_, lean_object* v_cleanupAnnotations_1527_, lean_object* v_whnfType_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1540_; uint8_t v_whnfType_boxed_1541_; lean_object* v_res_1542_; 
v_cleanupAnnotations_boxed_1540_ = lean_unbox(v_cleanupAnnotations_1527_);
v_whnfType_boxed_1541_ = lean_unbox(v_whnfType_1528_);
v_res_1542_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(v_00_u03b1_1524_, v_type_1525_, v_k_1526_, v_cleanupAnnotations_boxed_1540_, v_whnfType_boxed_1541_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec(v___y_1529_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed(lean_object* v_e_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_xs_1549_, lean_object* v_x_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
uint8_t v_a_95196__boxed_1562_; lean_object* v_res_1563_; 
v_a_95196__boxed_1562_ = lean_unbox(v_a_1547_);
v_res_1563_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(v_e_1546_, v_a_95196__boxed_1562_, v_a_1548_, v_xs_1549_, v_x_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v_x_1550_);
lean_dec_ref(v_xs_1549_);
return v_res_1563_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1(void){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__0));
v___x_1566_ = l_Lean_stringToMessageData(v___x_1565_);
return v___x_1566_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__2));
v___x_1569_ = l_Lean_stringToMessageData(v___x_1568_);
return v___x_1569_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__4));
v___x_1572_ = l_Lean_stringToMessageData(v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(lean_object* v_e_1573_, lean_object* v_h_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
uint8_t v___y_1590_; lean_object* v___y_1591_; uint8_t v___y_1592_; lean_object* v___y_1593_; uint8_t v___y_1594_; lean_object* v_h_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; uint8_t v___y_1792_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v_options_1966_; uint8_t v_hasTrace_1967_; 
v_options_1966_ = lean_ctor_get(v_a_1583_, 2);
v_hasTrace_1967_ = lean_ctor_get_uint8(v_options_1966_, sizeof(void*)*1);
if (v_hasTrace_1967_ == 0)
{
v___y_1869_ = v_a_1575_;
v___y_1870_ = v_a_1576_;
v___y_1871_ = v_a_1577_;
v___y_1872_ = v_a_1578_;
v___y_1873_ = v_a_1579_;
v___y_1874_ = v_a_1580_;
v___y_1875_ = v_a_1581_;
v___y_1876_ = v_a_1582_;
v___y_1877_ = v_a_1583_;
v___y_1878_ = v_a_1584_;
goto v___jp_1868_;
}
else
{
lean_object* v_inheritedTraceOptions_1968_; lean_object* v_cls_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
v_inheritedTraceOptions_1968_ = lean_ctor_get(v_a_1583_, 13);
v_cls_1969_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_1970_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_1971_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1968_, v_options_1966_, v___x_1970_);
if (v___x_1971_ == 0)
{
v___y_1869_ = v_a_1575_;
v___y_1870_ = v_a_1576_;
v___y_1871_ = v_a_1577_;
v___y_1872_ = v_a_1578_;
v___y_1873_ = v_a_1579_;
v___y_1874_ = v_a_1580_;
v___y_1875_ = v_a_1581_;
v___y_1876_ = v_a_1582_;
v___y_1877_ = v_a_1583_;
v___y_1878_ = v_a_1584_;
goto v___jp_1868_;
}
else
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Lean_Meta_Grind_updateLastTag(v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v___x_1973_; 
lean_dec_ref_known(v___x_1972_, 1);
lean_inc(v_a_1584_);
lean_inc_ref(v_a_1583_);
lean_inc(v_a_1582_);
lean_inc_ref(v_a_1581_);
lean_inc_ref(v_h_1574_);
v___x_1973_ = lean_infer_type(v_h_1574_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref_known(v___x_1973_, 1);
v___x_1975_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5);
v___x_1976_ = l_Lean_MessageData_ofExpr(v_a_1974_);
v___x_1977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1975_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1969_, v___x_1977_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_dec_ref_known(v___x_1978_, 1);
v___y_1869_ = v_a_1575_;
v___y_1870_ = v_a_1576_;
v___y_1871_ = v_a_1577_;
v___y_1872_ = v_a_1578_;
v___y_1873_ = v_a_1579_;
v___y_1874_ = v_a_1580_;
v___y_1875_ = v_a_1581_;
v___y_1876_ = v_a_1582_;
v___y_1877_ = v_a_1583_;
v___y_1878_ = v_a_1584_;
goto v___jp_1868_;
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
lean_dec_ref(v_h_1574_);
lean_dec_ref(v_e_1573_);
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1978_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1978_);
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
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec_ref(v_h_1574_);
lean_dec_ref(v_e_1573_);
v_a_1987_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1973_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1973_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec_ref(v_h_1574_);
lean_dec_ref(v_e_1573_);
v_a_1995_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1972_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1972_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
v___jp_1586_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = lean_box(0);
v___x_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
return v___x_1588_;
}
v___jp_1589_:
{
if (v___y_1594_ == 0)
{
lean_dec_ref(v_e_1573_);
if (v___y_1592_ == 0)
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
lean_dec_ref(v_h_1595_);
lean_dec_ref(v___y_1593_);
lean_dec_ref(v___y_1591_);
v___x_1606_ = lean_box(0);
v___x_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
return v___x_1607_;
}
else
{
lean_object* v___x_1608_; 
lean_inc_ref(v___y_1593_);
v___x_1608_ = l_Lean_Meta_normLitValue(v___y_1593_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1610_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___x_1608_, 1);
lean_inc_ref(v___y_1591_);
v___x_1610_ = l_Lean_Meta_normLitValue(v___y_1591_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1651_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1651_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1651_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
uint8_t v___x_1615_; uint8_t v___x_1616_; 
v___x_1615_ = lean_expr_eqv(v_a_1609_, v_a_1611_);
lean_dec(v_a_1611_);
lean_dec(v_a_1609_);
v___x_1616_ = lean_bool_not(v___x_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1619_; 
lean_dec_ref(v_h_1595_);
lean_dec_ref(v___y_1593_);
lean_dec_ref(v___y_1591_);
v___x_1617_ = lean_box(0);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v___x_1617_);
v___x_1619_ = v___x_1613_;
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
else
{
lean_object* v___x_1621_; 
lean_del_object(v___x_1613_);
v___x_1621_ = l_Lean_Meta_mkEq(v___y_1593_, v___y_1591_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v___x_1623_ = l_Lean_mkNot(v_a_1622_);
v___x_1624_ = l_Lean_Meta_mkDecideProof(v___x_1623_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1634_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1627_ = v___x_1624_;
v_isShared_1628_ = v_isSharedCheck_1634_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1634_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
v___x_1629_ = l_Lean_Expr_app___override(v_a_1625_, v_h_1595_);
v___x_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1630_);
v___x_1632_ = v___x_1627_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_dec_ref(v_h_1595_);
v_a_1635_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1624_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1624_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
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
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec_ref(v_h_1595_);
v_a_1643_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1621_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1621_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec(v_a_1609_);
lean_dec_ref(v_h_1595_);
lean_dec_ref(v___y_1593_);
lean_dec_ref(v___y_1591_);
v_a_1652_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1610_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1610_);
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
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec_ref(v_h_1595_);
lean_dec_ref(v___y_1593_);
lean_dec_ref(v___y_1591_);
v_a_1660_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1608_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1608_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
else
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_Meta_isConstructorApp_x3f(v___y_1593_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1769_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1769_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1769_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
if (lean_obj_tag(v_a_1669_) == 1)
{
lean_object* v_val_1673_; lean_object* v___x_1674_; 
lean_del_object(v___x_1671_);
v_val_1673_ = lean_ctor_get(v_a_1669_, 0);
lean_inc(v_val_1673_);
lean_dec_ref_known(v_a_1669_, 1);
v___x_1674_ = l_Lean_Meta_isConstructorApp_x3f(v___y_1591_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1756_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1677_ = v___x_1674_;
v_isShared_1678_ = v_isSharedCheck_1756_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1674_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1756_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
if (lean_obj_tag(v_a_1675_) == 1)
{
lean_object* v_val_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1751_; 
lean_del_object(v___x_1677_);
v_val_1679_ = lean_ctor_get(v_a_1675_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_a_1675_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1681_ = v_a_1675_;
v_isShared_1682_ = v_isSharedCheck_1751_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_val_1679_);
lean_dec(v_a_1675_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1751_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_1600_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1685_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref_known(v___x_1683_, 1);
v___x_1685_ = l_Lean_Meta_mkNoConfusion(v_a_1684_, v_h_1595_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_toConstantVal_1686_; lean_object* v_toConstantVal_1687_; lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1734_; 
v_toConstantVal_1686_ = lean_ctor_get(v_val_1673_, 0);
lean_inc_ref(v_toConstantVal_1686_);
lean_dec(v_val_1673_);
v_toConstantVal_1687_ = lean_ctor_get(v_val_1679_, 0);
lean_inc_ref(v_toConstantVal_1687_);
lean_dec(v_val_1679_);
v_a_1688_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1690_ = v___x_1685_;
v_isShared_1691_ = v_isSharedCheck_1734_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1685_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1734_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v_name_1692_; lean_object* v_name_1693_; uint8_t v___x_1694_; 
v_name_1692_ = lean_ctor_get(v_toConstantVal_1686_, 0);
lean_inc(v_name_1692_);
lean_dec_ref(v_toConstantVal_1686_);
v_name_1693_ = lean_ctor_get(v_toConstantVal_1687_, 0);
lean_inc(v_name_1693_);
lean_dec_ref(v_toConstantVal_1687_);
v___x_1694_ = lean_name_eq(v_name_1692_, v_name_1693_);
lean_dec(v_name_1693_);
lean_dec(v_name_1692_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1696_; 
lean_dec_ref(v_e_1573_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v_a_1688_);
v___x_1696_ = v___x_1681_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1688_);
v___x_1696_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1698_; 
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v___x_1696_);
v___x_1698_ = v___x_1690_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
else
{
lean_object* v___x_1701_; 
lean_del_object(v___x_1690_);
lean_del_object(v___x_1681_);
lean_inc(v___y_1605_);
lean_inc_ref(v___y_1604_);
lean_inc(v___y_1603_);
lean_inc_ref(v___y_1602_);
lean_inc(v_a_1688_);
v___x_1701_ = lean_infer_type(v_a_1688_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; lean_object* v___x_1703_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1702_);
lean_dec_ref_known(v___x_1701_, 1);
v___x_1703_ = l_Lean_Meta_whnfD(v_a_1702_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1717_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1706_ = v___x_1703_;
v_isShared_1707_ = v_isSharedCheck_1717_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1703_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1717_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
if (lean_obj_tag(v_a_1704_) == 7)
{
lean_object* v_binderType_1708_; lean_object* v___x_1709_; lean_object* v___f_1710_; uint8_t v___x_1711_; lean_object* v___x_1712_; 
lean_del_object(v___x_1706_);
v_binderType_1708_ = lean_ctor_get(v_a_1704_, 1);
lean_inc_ref(v_binderType_1708_);
lean_dec_ref_known(v_a_1704_, 3);
v___x_1709_ = lean_box(v___y_1590_);
v___f_1710_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed), 16, 3);
lean_closure_set(v___f_1710_, 0, v_e_1573_);
lean_closure_set(v___f_1710_, 1, v___x_1709_);
lean_closure_set(v___f_1710_, 2, v_a_1688_);
v___x_1711_ = 0;
v___x_1712_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_binderType_1708_, v___f_1710_, v___x_1711_, v___x_1711_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
return v___x_1712_;
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
lean_dec(v_a_1704_);
lean_dec(v_a_1688_);
lean_dec_ref(v_e_1573_);
v___x_1713_ = lean_box(0);
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 0, v___x_1713_);
v___x_1715_ = v___x_1706_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
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
lean_dec(v_a_1688_);
lean_dec_ref(v_e_1573_);
v_a_1718_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1703_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1703_);
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
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec(v_a_1688_);
lean_dec_ref(v_e_1573_);
v_a_1726_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1701_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1701_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_del_object(v___x_1681_);
lean_dec(v_val_1679_);
lean_dec(v_val_1673_);
lean_dec_ref(v_e_1573_);
v_a_1735_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1685_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1685_);
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
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
lean_del_object(v___x_1681_);
lean_dec(v_val_1679_);
lean_dec(v_val_1673_);
lean_dec_ref(v_h_1595_);
lean_dec_ref(v_e_1573_);
v_a_1743_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1683_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1683_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1754_; 
lean_dec(v_a_1675_);
lean_dec(v_val_1673_);
lean_dec_ref(v_h_1595_);
lean_dec_ref(v_e_1573_);
v___x_1752_ = lean_box(0);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1752_);
v___x_1754_ = v___x_1677_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
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
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec(v_val_1673_);
lean_dec_ref(v_h_1595_);
lean_dec_ref(v_e_1573_);
v_a_1757_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1674_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1674_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1767_; 
lean_dec(v_a_1669_);
lean_dec_ref(v_h_1595_);
lean_dec_ref(v___y_1591_);
lean_dec_ref(v_e_1573_);
v___x_1765_ = lean_box(0);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1765_);
v___x_1767_ = v___x_1671_;
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
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec_ref(v_h_1595_);
lean_dec_ref(v___y_1591_);
lean_dec_ref(v_e_1573_);
v_a_1770_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1668_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1668_);
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
}
v___jp_1778_:
{
lean_object* v_self_1793_; uint8_t v_interpreted_1794_; uint8_t v_ctor_1795_; lean_object* v___x_1796_; 
v_self_1793_ = lean_ctor_get(v___y_1779_, 0);
lean_inc_ref_n(v_self_1793_, 2);
v_interpreted_1794_ = lean_ctor_get_uint8(v___y_1779_, sizeof(void*)*12 + 1);
v_ctor_1795_ = lean_ctor_get_uint8(v___y_1779_, sizeof(void*)*12 + 2);
lean_dec_ref(v___y_1779_);
lean_inc_ref(v___y_1782_);
v___x_1796_ = l_Lean_Meta_Grind_hasSameType(v_self_1793_, v___y_1782_, v___y_1781_, v___y_1783_, v___y_1786_, v___y_1791_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1859_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1859_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1859_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
uint8_t v___x_1801_; 
v___x_1801_ = lean_unbox(v_a_1797_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
lean_dec(v_a_1797_);
lean_dec_ref(v_self_1793_);
lean_dec_ref(v___y_1788_);
lean_dec_ref(v___y_1782_);
lean_dec_ref(v_h_1574_);
lean_dec_ref(v_e_1573_);
v___x_1802_ = lean_box(0);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1802_);
v___x_1804_ = v___x_1799_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
else
{
lean_del_object(v___x_1799_);
if (v___y_1792_ == 0)
{
lean_object* v___x_1806_; 
lean_inc(v___y_1791_);
lean_inc_ref(v___y_1786_);
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1781_);
lean_inc(v___y_1785_);
lean_inc_ref(v___y_1784_);
lean_inc(v___y_1789_);
lean_inc_ref(v___y_1787_);
lean_inc(v___y_1780_);
lean_inc(v___y_1790_);
lean_inc_ref(v_self_1793_);
v___x_1806_ = lean_grind_mk_eq_proof(v_self_1793_, v___y_1788_, v___y_1790_, v___y_1780_, v___y_1787_, v___y_1789_, v___y_1784_, v___y_1785_, v___y_1781_, v___y_1783_, v___y_1786_, v___y_1791_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1808_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_a_1807_);
lean_dec_ref_known(v___x_1806_, 1);
v___x_1808_ = l_Lean_Meta_mkEqTrans(v_a_1807_, v_h_1574_, v___y_1781_, v___y_1783_, v___y_1786_, v___y_1791_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; uint8_t v___x_1810_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1808_, 1);
v___x_1810_ = lean_unbox(v_a_1797_);
lean_dec(v_a_1797_);
v___y_1590_ = v___x_1810_;
v___y_1591_ = v___y_1782_;
v___y_1592_ = v_interpreted_1794_;
v___y_1593_ = v_self_1793_;
v___y_1594_ = v_ctor_1795_;
v_h_1595_ = v_a_1809_;
v___y_1596_ = v___y_1790_;
v___y_1597_ = v___y_1780_;
v___y_1598_ = v___y_1787_;
v___y_1599_ = v___y_1789_;
v___y_1600_ = v___y_1784_;
v___y_1601_ = v___y_1785_;
v___y_1602_ = v___y_1781_;
v___y_1603_ = v___y_1783_;
v___y_1604_ = v___y_1786_;
v___y_1605_ = v___y_1791_;
goto v___jp_1589_;
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec(v_a_1797_);
lean_dec_ref(v_self_1793_);
lean_dec_ref(v___y_1782_);
lean_dec_ref(v_e_1573_);
v_a_1811_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1808_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1808_);
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
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec(v_a_1797_);
lean_dec_ref(v_self_1793_);
lean_dec_ref(v___y_1782_);
lean_dec_ref(v_h_1574_);
lean_dec_ref(v_e_1573_);
v_a_1819_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1806_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1806_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
else
{
lean_object* v___x_1827_; 
lean_inc(v___y_1791_);
lean_inc_ref(v___y_1786_);
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1781_);
lean_inc(v___y_1785_);
lean_inc_ref(v___y_1784_);
lean_inc(v___y_1789_);
lean_inc_ref(v___y_1787_);
lean_inc(v___y_1780_);
lean_inc(v___y_1790_);
lean_inc_ref(v_self_1793_);
v___x_1827_ = lean_grind_mk_heq_proof(v_self_1793_, v___y_1788_, v___y_1790_, v___y_1780_, v___y_1787_, v___y_1789_, v___y_1784_, v___y_1785_, v___y_1781_, v___y_1783_, v___y_1786_, v___y_1791_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1829_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_a_1828_);
lean_dec_ref_known(v___x_1827_, 1);
v___x_1829_ = l_Lean_Meta_mkHEqTrans(v_a_1828_, v_h_1574_, v___y_1781_, v___y_1783_, v___y_1786_, v___y_1791_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_a_1830_);
lean_dec_ref_known(v___x_1829_, 1);
v___x_1831_ = 0;
v___x_1832_ = l_Lean_Meta_mkEqOfHEq(v_a_1830_, v___x_1831_, v___y_1781_, v___y_1783_, v___y_1786_, v___y_1791_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; uint8_t v___x_1834_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1832_, 1);
v___x_1834_ = lean_unbox(v_a_1797_);
lean_dec(v_a_1797_);
v___y_1590_ = v___x_1834_;
v___y_1591_ = v___y_1782_;
v___y_1592_ = v_interpreted_1794_;
v___y_1593_ = v_self_1793_;
v___y_1594_ = v_ctor_1795_;
v_h_1595_ = v_a_1833_;
v___y_1596_ = v___y_1790_;
v___y_1597_ = v___y_1780_;
v___y_1598_ = v___y_1787_;
v___y_1599_ = v___y_1789_;
v___y_1600_ = v___y_1784_;
v___y_1601_ = v___y_1785_;
v___y_1602_ = v___y_1781_;
v___y_1603_ = v___y_1783_;
v___y_1604_ = v___y_1786_;
v___y_1605_ = v___y_1791_;
goto v___jp_1589_;
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_dec(v_a_1797_);
lean_dec_ref(v_self_1793_);
lean_dec_ref(v___y_1782_);
lean_dec_ref(v_e_1573_);
v_a_1835_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1832_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1832_);
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
lean_dec(v_a_1797_);
lean_dec_ref(v_self_1793_);
lean_dec_ref(v___y_1782_);
lean_dec_ref(v_e_1573_);
v_a_1843_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1829_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1829_);
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
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec(v_a_1797_);
lean_dec_ref(v_self_1793_);
lean_dec_ref(v___y_1782_);
lean_dec_ref(v_h_1574_);
lean_dec_ref(v_e_1573_);
v_a_1851_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1827_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1827_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec_ref(v_self_1793_);
lean_dec_ref(v___y_1788_);
lean_dec_ref(v___y_1782_);
lean_dec_ref(v_h_1574_);
lean_dec_ref(v_e_1573_);
v_a_1860_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1796_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1796_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
v___jp_1868_:
{
lean_object* v___x_1879_; 
lean_inc(v___y_1878_);
lean_inc_ref(v___y_1877_);
lean_inc(v___y_1876_);
lean_inc_ref(v___y_1875_);
lean_inc_ref(v_h_1574_);
v___x_1879_ = lean_infer_type(v_h_1574_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1957_; 
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1882_ = v___x_1879_;
v_isShared_1883_ = v_isSharedCheck_1957_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1879_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1957_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1884_; 
v___x_1884_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_a_1880_);
if (lean_obj_tag(v___x_1884_) == 1)
{
lean_object* v_val_1885_; lean_object* v_snd_1886_; lean_object* v_fst_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1952_; 
lean_del_object(v___x_1882_);
v_val_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_val_1885_);
lean_dec_ref_known(v___x_1884_, 1);
v_snd_1886_ = lean_ctor_get(v_val_1885_, 1);
v_fst_1887_ = lean_ctor_get(v_val_1885_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_val_1885_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1889_ = v_val_1885_;
v_isShared_1890_ = v_isSharedCheck_1952_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_snd_1886_);
lean_inc(v_fst_1887_);
lean_dec(v_val_1885_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1952_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v_fst_1891_; lean_object* v_snd_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1951_; 
v_fst_1891_ = lean_ctor_get(v_snd_1886_, 0);
v_snd_1892_ = lean_ctor_get(v_snd_1886_, 1);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_snd_1886_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1894_ = v_snd_1886_;
v_isShared_1895_ = v_isSharedCheck_1951_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_snd_1892_);
lean_inc(v_fst_1891_);
lean_dec(v_snd_1886_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1951_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Lean_Meta_Sym_shareCommon(v_fst_1891_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1898_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref_known(v___x_1896_, 1);
v___x_1898_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_a_1897_, v___y_1869_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1898_, 1);
if (lean_obj_tag(v_a_1899_) == 1)
{
lean_del_object(v___x_1894_);
lean_del_object(v___x_1889_);
if (lean_obj_tag(v_fst_1887_) == 0)
{
lean_object* v_val_1900_; uint8_t v___x_1901_; 
v_val_1900_ = lean_ctor_get(v_a_1899_, 0);
lean_inc(v_val_1900_);
lean_dec_ref_known(v_a_1899_, 1);
v___x_1901_ = 0;
v___y_1779_ = v_val_1900_;
v___y_1780_ = v___y_1870_;
v___y_1781_ = v___y_1875_;
v___y_1782_ = v_snd_1892_;
v___y_1783_ = v___y_1876_;
v___y_1784_ = v___y_1873_;
v___y_1785_ = v___y_1874_;
v___y_1786_ = v___y_1877_;
v___y_1787_ = v___y_1871_;
v___y_1788_ = v_a_1897_;
v___y_1789_ = v___y_1872_;
v___y_1790_ = v___y_1869_;
v___y_1791_ = v___y_1878_;
v___y_1792_ = v___x_1901_;
goto v___jp_1778_;
}
else
{
lean_object* v_val_1902_; uint8_t v___x_1903_; 
lean_dec_ref_known(v_fst_1887_, 1);
v_val_1902_ = lean_ctor_get(v_a_1899_, 0);
lean_inc(v_val_1902_);
lean_dec_ref_known(v_a_1899_, 1);
v___x_1903_ = 1;
v___y_1779_ = v_val_1902_;
v___y_1780_ = v___y_1870_;
v___y_1781_ = v___y_1875_;
v___y_1782_ = v_snd_1892_;
v___y_1783_ = v___y_1876_;
v___y_1784_ = v___y_1873_;
v___y_1785_ = v___y_1874_;
v___y_1786_ = v___y_1877_;
v___y_1787_ = v___y_1871_;
v___y_1788_ = v_a_1897_;
v___y_1789_ = v___y_1872_;
v___y_1790_ = v___y_1869_;
v___y_1791_ = v___y_1878_;
v___y_1792_ = v___x_1903_;
goto v___jp_1778_;
}
}
else
{
lean_object* v___x_1904_; 
lean_dec(v_a_1899_);
lean_dec(v_snd_1892_);
lean_dec(v_fst_1887_);
lean_dec_ref(v_h_1574_);
v___x_1904_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1873_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; uint8_t v_verbose_1906_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
v_verbose_1906_ = lean_ctor_get_uint8(v_a_1905_, 0);
lean_dec(v_a_1905_);
if (v_verbose_1906_ == 0)
{
lean_dec(v_a_1897_);
lean_del_object(v___x_1894_);
lean_del_object(v___x_1889_);
lean_dec_ref(v_e_1573_);
goto v___jp_1586_;
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1907_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1);
v___x_1908_ = l_Lean_indentExpr(v_a_1897_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set_tag(v___x_1894_, 7);
lean_ctor_set(v___x_1894_, 1, v___x_1908_);
lean_ctor_set(v___x_1894_, 0, v___x_1907_);
v___x_1910_ = v___x_1894_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1907_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1911_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3);
if (v_isShared_1890_ == 0)
{
lean_ctor_set_tag(v___x_1889_, 7);
lean_ctor_set(v___x_1889_, 1, v___x_1911_);
lean_ctor_set(v___x_1889_, 0, v___x_1910_);
v___x_1913_ = v___x_1889_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1910_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = l_Lean_indentExpr(v_e_1573_);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = l_Lean_Meta_Sym_reportIssue(v___x_1915_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_dec_ref_known(v___x_1916_, 1);
goto v___jp_1586_;
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1916_);
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
lean_dec(v_a_1897_);
lean_del_object(v___x_1894_);
lean_del_object(v___x_1889_);
lean_dec_ref(v_e_1573_);
v_a_1927_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1904_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1904_);
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
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_dec(v_a_1897_);
lean_del_object(v___x_1894_);
lean_dec(v_snd_1892_);
lean_del_object(v___x_1889_);
lean_dec(v_fst_1887_);
lean_dec_ref(v_h_1574_);
lean_dec_ref(v_e_1573_);
v_a_1935_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1898_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1898_);
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
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_del_object(v___x_1894_);
lean_dec(v_snd_1892_);
lean_del_object(v___x_1889_);
lean_dec(v_fst_1887_);
lean_dec_ref(v_h_1574_);
lean_dec_ref(v_e_1573_);
v_a_1943_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1896_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1896_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
}
else
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
lean_dec(v___x_1884_);
lean_dec_ref(v_h_1574_);
lean_dec_ref(v_e_1573_);
v___x_1953_ = lean_box(0);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v___x_1953_);
v___x_1955_ = v___x_1882_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1953_);
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
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec_ref(v_h_1574_);
lean_dec_ref(v_e_1573_);
v_a_1958_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1879_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1879_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(lean_object* v_e_2003_, lean_object* v_xs_2004_, uint8_t v_a_2005_, lean_object* v_a_2006_, lean_object* v_as_2007_, size_t v_sz_2008_, size_t v_i_2009_, lean_object* v_b_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
uint8_t v___x_2022_; 
v___x_2022_ = lean_usize_dec_lt(v_i_2009_, v_sz_2008_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; 
lean_dec_ref(v_a_2006_);
lean_dec_ref(v_e_2003_);
v___x_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2023_, 0, v_b_2010_);
return v___x_2023_;
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2025_; 
lean_dec_ref(v_b_2010_);
v_a_2024_ = lean_array_uget_borrowed(v_as_2007_, v_i_2009_);
lean_inc(v_a_2024_);
lean_inc_ref(v_e_2003_);
v___x_2025_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2003_, v_a_2024_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2027_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2025_, 1);
v___x_2027_ = lean_box(0);
if (lean_obj_tag(v_a_2026_) == 1)
{
lean_object* v_val_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2057_; 
lean_dec_ref(v_e_2003_);
v_val_2028_ = lean_ctor_get(v_a_2026_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_a_2026_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2030_ = v_a_2026_;
v_isShared_2031_ = v_isSharedCheck_2057_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_val_2028_);
lean_dec(v_a_2026_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2057_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
uint8_t v___x_2032_; uint8_t v___x_2033_; lean_object* v___x_2034_; 
v___x_2032_ = 0;
v___x_2033_ = 1;
v___x_2034_ = l_Lean_Meta_mkLambdaFVars(v_xs_2004_, v_val_2028_, v___x_2032_, v_a_2005_, v___x_2032_, v_a_2005_, v___x_2033_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2048_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2037_ = v___x_2034_;
v_isShared_2038_ = v_isSharedCheck_2048_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2034_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2048_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2039_ = l_Lean_Expr_app___override(v_a_2006_, v_a_2035_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2039_);
v___x_2041_ = v___x_2030_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2045_; 
v___x_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
v___x_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
lean_ctor_set(v___x_2043_, 1, v___x_2027_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v___x_2043_);
v___x_2045_ = v___x_2037_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_del_object(v___x_2030_);
lean_dec_ref(v_a_2006_);
v_a_2049_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2034_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2034_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
else
{
lean_object* v___x_2058_; size_t v___x_2059_; size_t v___x_2060_; 
lean_dec(v_a_2026_);
v___x_2058_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v___x_2059_ = ((size_t)1ULL);
v___x_2060_ = lean_usize_add(v_i_2009_, v___x_2059_);
v_i_2009_ = v___x_2060_;
v_b_2010_ = v___x_2058_;
goto _start;
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec_ref(v_a_2006_);
lean_dec_ref(v_e_2003_);
v_a_2062_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2025_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2025_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(lean_object* v_e_2070_, uint8_t v_a_2071_, lean_object* v_a_2072_, lean_object* v_xs_2073_, lean_object* v_x_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; size_t v_sz_2088_; size_t v___x_2089_; lean_object* v___x_2090_; 
v___x_2086_ = lean_box(0);
v___x_2087_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_sz_2088_ = lean_array_size(v_xs_2073_);
v___x_2089_ = ((size_t)0ULL);
v___x_2090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_2070_, v_xs_2073_, v_a_2071_, v_a_2072_, v_xs_2073_, v_sz_2088_, v___x_2089_, v___x_2087_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2103_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2093_ = v___x_2090_;
v_isShared_2094_ = v_isSharedCheck_2103_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2090_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2103_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v_fst_2095_; 
v_fst_2095_ = lean_ctor_get(v_a_2091_, 0);
lean_inc(v_fst_2095_);
lean_dec(v_a_2091_);
if (lean_obj_tag(v_fst_2095_) == 0)
{
lean_object* v___x_2097_; 
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v___x_2086_);
v___x_2097_ = v___x_2093_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2086_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
else
{
lean_object* v_val_2099_; lean_object* v___x_2101_; 
v_val_2099_ = lean_ctor_get(v_fst_2095_, 0);
lean_inc(v_val_2099_);
lean_dec_ref_known(v_fst_2095_, 1);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v_val_2099_);
v___x_2101_ = v___x_2093_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_val_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
v_a_2104_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2090_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2090_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_e_2112_ = _args[0];
lean_object* v_xs_2113_ = _args[1];
lean_object* v_a_2114_ = _args[2];
lean_object* v_a_2115_ = _args[3];
lean_object* v_as_2116_ = _args[4];
lean_object* v_sz_2117_ = _args[5];
lean_object* v_i_2118_ = _args[6];
lean_object* v_b_2119_ = _args[7];
lean_object* v___y_2120_ = _args[8];
lean_object* v___y_2121_ = _args[9];
lean_object* v___y_2122_ = _args[10];
lean_object* v___y_2123_ = _args[11];
lean_object* v___y_2124_ = _args[12];
lean_object* v___y_2125_ = _args[13];
lean_object* v___y_2126_ = _args[14];
lean_object* v___y_2127_ = _args[15];
lean_object* v___y_2128_ = _args[16];
lean_object* v___y_2129_ = _args[17];
lean_object* v___y_2130_ = _args[18];
_start:
{
uint8_t v_a_95220__boxed_2131_; size_t v_sz_boxed_2132_; size_t v_i_boxed_2133_; lean_object* v_res_2134_; 
v_a_95220__boxed_2131_ = lean_unbox(v_a_2114_);
v_sz_boxed_2132_ = lean_unbox_usize(v_sz_2117_);
lean_dec(v_sz_2117_);
v_i_boxed_2133_ = lean_unbox_usize(v_i_2118_);
lean_dec(v_i_2118_);
v_res_2134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_2112_, v_xs_2113_, v_a_95220__boxed_2131_, v_a_2115_, v_as_2116_, v_sz_boxed_2132_, v_i_boxed_2133_, v_b_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v_as_2116_);
lean_dec_ref(v_xs_2113_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___boxed(lean_object* v_e_2135_, lean_object* v_h_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2135_, v_h_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
lean_dec(v_a_2144_);
lean_dec_ref(v_a_2143_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec(v_a_2137_);
return v_res_2148_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__0));
v___x_2151_ = l_Lean_stringToMessageData(v___x_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(lean_object* v_e_2152_, lean_object* v_xs_2153_, uint8_t v___x_2154_, lean_object* v_as_2155_, size_t v_sz_2156_, size_t v_i_2157_, lean_object* v_b_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v_a_2171_; uint8_t v___x_2175_; 
v___x_2175_ = lean_usize_dec_lt(v_i_2157_, v_sz_2156_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; 
lean_dec_ref(v_e_2152_);
v___x_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2176_, 0, v_b_2158_);
return v___x_2176_;
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2178_; 
lean_dec_ref(v_b_2158_);
v_a_2177_ = lean_array_uget_borrowed(v_as_2155_, v_i_2157_);
lean_inc(v___y_2168_);
lean_inc_ref(v___y_2167_);
lean_inc(v___y_2166_);
lean_inc_ref(v___y_2165_);
lean_inc(v_a_2177_);
v___x_2178_ = lean_infer_type(v_a_2177_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2180_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc_n(v_a_2179_, 2);
lean_dec_ref_known(v___x_2178_, 1);
v___x_2180_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_a_2179_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; uint8_t v___x_2234_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2180_, 1);
v___x_2182_ = lean_box(0);
v___x_2183_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v___x_2234_ = lean_unbox(v_a_2181_);
lean_dec(v_a_2181_);
if (v___x_2234_ == 0)
{
lean_dec(v_a_2179_);
v_a_2171_ = v___x_2183_;
goto v___jp_2170_;
}
else
{
lean_object* v_options_2235_; uint8_t v_hasTrace_2236_; 
v_options_2235_ = lean_ctor_get(v___y_2167_, 2);
v_hasTrace_2236_ = lean_ctor_get_uint8(v_options_2235_, sizeof(void*)*1);
if (v_hasTrace_2236_ == 0)
{
lean_dec(v_a_2179_);
v___y_2185_ = v___y_2159_;
v___y_2186_ = v___y_2160_;
v___y_2187_ = v___y_2161_;
v___y_2188_ = v___y_2162_;
v___y_2189_ = v___y_2163_;
v___y_2190_ = v___y_2164_;
v___y_2191_ = v___y_2165_;
v___y_2192_ = v___y_2166_;
v___y_2193_ = v___y_2167_;
v___y_2194_ = v___y_2168_;
goto v___jp_2184_;
}
else
{
lean_object* v_inheritedTraceOptions_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v_inheritedTraceOptions_2237_ = lean_ctor_get(v___y_2167_, 13);
v___x_2238_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_2239_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_2240_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2237_, v_options_2235_, v___x_2239_);
if (v___x_2240_ == 0)
{
lean_dec(v_a_2179_);
v___y_2185_ = v___y_2159_;
v___y_2186_ = v___y_2160_;
v___y_2187_ = v___y_2161_;
v___y_2188_ = v___y_2162_;
v___y_2189_ = v___y_2163_;
v___y_2190_ = v___y_2164_;
v___y_2191_ = v___y_2165_;
v___y_2192_ = v___y_2166_;
v___y_2193_ = v___y_2167_;
v___y_2194_ = v___y_2168_;
goto v___jp_2184_;
}
else
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_Meta_Grind_updateLastTag(v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
lean_dec_ref_known(v___x_2241_, 1);
v___x_2242_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1);
v___x_2243_ = l_Lean_MessageData_ofExpr(v_a_2179_);
v___x_2244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2242_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_2238_, v___x_2244_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_dec_ref_known(v___x_2245_, 1);
v___y_2185_ = v___y_2159_;
v___y_2186_ = v___y_2160_;
v___y_2187_ = v___y_2161_;
v___y_2188_ = v___y_2162_;
v___y_2189_ = v___y_2163_;
v___y_2190_ = v___y_2164_;
v___y_2191_ = v___y_2165_;
v___y_2192_ = v___y_2166_;
v___y_2193_ = v___y_2167_;
v___y_2194_ = v___y_2168_;
goto v___jp_2184_;
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec_ref(v_e_2152_);
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2245_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2245_);
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
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_dec(v_a_2179_);
lean_dec_ref(v_e_2152_);
v_a_2254_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2241_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2241_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
}
}
v___jp_2184_:
{
lean_object* v___x_2195_; 
lean_inc(v_a_2177_);
lean_inc_ref(v_e_2152_);
v___x_2195_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2152_, v_a_2177_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref_known(v___x_2195_, 1);
if (lean_obj_tag(v_a_2196_) == 1)
{
lean_object* v_val_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v_e_2152_);
v_val_2197_ = lean_ctor_get(v_a_2196_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_a_2196_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2199_ = v_a_2196_;
v_isShared_2200_ = v_isSharedCheck_2225_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_val_2197_);
lean_dec(v_a_2196_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2225_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
uint8_t v___x_2201_; uint8_t v___x_2202_; lean_object* v___x_2203_; 
v___x_2201_ = 0;
v___x_2202_ = 1;
v___x_2203_ = l_Lean_Meta_mkLambdaFVars(v_xs_2153_, v_val_2197_, v___x_2201_, v___x_2154_, v___x_2201_, v___x_2154_, v___x_2202_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2216_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2216_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2216_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v_a_2204_);
v___x_2209_ = v___x_2199_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
v___x_2211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
lean_ctor_set(v___x_2211_, 1, v___x_2182_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2211_);
v___x_2213_ = v___x_2206_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_del_object(v___x_2199_);
v_a_2217_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2203_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2203_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
else
{
lean_dec(v_a_2196_);
v_a_2171_ = v___x_2183_;
goto v___jp_2170_;
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec_ref(v_e_2152_);
v_a_2226_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2195_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2195_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_dec(v_a_2179_);
lean_dec_ref(v_e_2152_);
v_a_2262_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2180_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2180_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec_ref(v_e_2152_);
v_a_2270_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2178_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2178_);
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
v___jp_2170_:
{
size_t v___x_2172_; size_t v___x_2173_; 
v___x_2172_ = ((size_t)1ULL);
v___x_2173_ = lean_usize_add(v_i_2157_, v___x_2172_);
lean_inc_ref(v_a_2171_);
v_i_2157_ = v___x_2173_;
v_b_2158_ = v_a_2171_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_e_2278_ = _args[0];
lean_object* v_xs_2279_ = _args[1];
lean_object* v___x_2280_ = _args[2];
lean_object* v_as_2281_ = _args[3];
lean_object* v_sz_2282_ = _args[4];
lean_object* v_i_2283_ = _args[5];
lean_object* v_b_2284_ = _args[6];
lean_object* v___y_2285_ = _args[7];
lean_object* v___y_2286_ = _args[8];
lean_object* v___y_2287_ = _args[9];
lean_object* v___y_2288_ = _args[10];
lean_object* v___y_2289_ = _args[11];
lean_object* v___y_2290_ = _args[12];
lean_object* v___y_2291_ = _args[13];
lean_object* v___y_2292_ = _args[14];
lean_object* v___y_2293_ = _args[15];
lean_object* v___y_2294_ = _args[16];
lean_object* v___y_2295_ = _args[17];
_start:
{
uint8_t v___x_30331__boxed_2296_; size_t v_sz_boxed_2297_; size_t v_i_boxed_2298_; lean_object* v_res_2299_; 
v___x_30331__boxed_2296_ = lean_unbox(v___x_2280_);
v_sz_boxed_2297_ = lean_unbox_usize(v_sz_2282_);
lean_dec(v_sz_2282_);
v_i_boxed_2298_ = lean_unbox_usize(v_i_2283_);
lean_dec(v_i_2283_);
v_res_2299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2278_, v_xs_2279_, v___x_30331__boxed_2296_, v_as_2281_, v_sz_boxed_2297_, v_i_boxed_2298_, v_b_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v_as_2281_);
lean_dec_ref(v_xs_2279_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(lean_object* v_e_2300_, uint8_t v___x_2301_, lean_object* v_xs_2302_, lean_object* v_x_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; size_t v_sz_2317_; size_t v___x_2318_; lean_object* v___x_2319_; 
v___x_2315_ = lean_box(0);
v___x_2316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_sz_2317_ = lean_array_size(v_xs_2302_);
v___x_2318_ = ((size_t)0ULL);
v___x_2319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2300_, v_xs_2302_, v___x_2301_, v_xs_2302_, v_sz_2317_, v___x_2318_, v___x_2316_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2332_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2322_ = v___x_2319_;
v_isShared_2323_ = v_isSharedCheck_2332_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2319_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2332_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v_fst_2324_; 
v_fst_2324_ = lean_ctor_get(v_a_2320_, 0);
lean_inc(v_fst_2324_);
lean_dec(v_a_2320_);
if (lean_obj_tag(v_fst_2324_) == 0)
{
lean_object* v___x_2326_; 
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v___x_2315_);
v___x_2326_ = v___x_2322_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2315_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
else
{
lean_object* v_val_2328_; lean_object* v___x_2330_; 
v_val_2328_ = lean_ctor_get(v_fst_2324_, 0);
lean_inc(v_val_2328_);
lean_dec_ref_known(v_fst_2324_, 1);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v_val_2328_);
v___x_2330_ = v___x_2322_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_val_2328_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
v_a_2333_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2319_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2319_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed(lean_object* v_e_2341_, lean_object* v___x_2342_, lean_object* v_xs_2343_, lean_object* v_x_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
uint8_t v___x_30583__boxed_2356_; lean_object* v_res_2357_; 
v___x_30583__boxed_2356_ = lean_unbox(v___x_2342_);
v_res_2357_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(v_e_2341_, v___x_30583__boxed_2356_, v_xs_2343_, v_x_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v_x_2344_);
lean_dec_ref(v_xs_2343_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(lean_object* v_e_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v___x_2370_; 
lean_inc_ref(v_e_2358_);
v___x_2370_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2358_, v_a_2366_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2390_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2373_ = v___x_2370_;
v_isShared_2374_ = v_isSharedCheck_2390_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2370_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2390_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2380_; uint8_t v___x_2381_; 
v___x_2380_ = l_Lean_Expr_cleanupAnnotations(v_a_2371_);
v___x_2381_ = l_Lean_Expr_isApp(v___x_2380_);
if (v___x_2381_ == 0)
{
lean_dec_ref(v___x_2380_);
lean_dec_ref(v_e_2358_);
goto v___jp_2375_;
}
else
{
lean_object* v_arg_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; 
v_arg_2382_ = lean_ctor_get(v___x_2380_, 1);
lean_inc_ref(v_arg_2382_);
v___x_2383_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2380_);
v___x_2384_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_2385_ = l_Lean_Expr_isConstOf(v___x_2383_, v___x_2384_);
lean_dec_ref(v___x_2383_);
if (v___x_2385_ == 0)
{
lean_dec_ref(v_arg_2382_);
lean_dec_ref(v_e_2358_);
goto v___jp_2375_;
}
else
{
lean_object* v___x_2386_; lean_object* v___f_2387_; uint8_t v___x_2388_; lean_object* v___x_2389_; 
lean_del_object(v___x_2373_);
v___x_2386_ = lean_box(v___x_2385_);
v___f_2387_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed), 15, 2);
lean_closure_set(v___f_2387_, 0, v_e_2358_);
lean_closure_set(v___f_2387_, 1, v___x_2386_);
v___x_2388_ = 0;
v___x_2389_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_arg_2382_, v___f_2387_, v___x_2388_, v___x_2388_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
return v___x_2389_;
}
}
v___jp_2375_:
{
lean_object* v___x_2376_; lean_object* v___x_2378_; 
v___x_2376_ = lean_box(0);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v___x_2376_);
v___x_2378_ = v___x_2373_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2376_);
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
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_dec_ref(v_e_2358_);
v_a_2391_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2370_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2370_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___boxed(lean_object* v_e_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
lean_dec(v_a_2401_);
lean_dec(v_a_2400_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(lean_object* v_e_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v___x_2424_; 
lean_inc_ref(v_e_2412_);
v___x_2424_ = l_Lean_Meta_Grind_getRootENode___redArg(v_e_2412_, v_a_2413_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2492_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2492_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2492_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
uint8_t v_ctor_2429_; 
v_ctor_2429_ = lean_ctor_get_uint8(v_a_2425_, sizeof(void*)*12 + 2);
if (v_ctor_2429_ == 0)
{
uint8_t v_interpreted_2430_; 
v_interpreted_2430_ = lean_ctor_get_uint8(v_a_2425_, sizeof(void*)*12 + 1);
if (v_interpreted_2430_ == 0)
{
lean_object* v___x_2432_; 
lean_dec(v_a_2425_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v_e_2412_);
v___x_2432_ = v___x_2427_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_e_2412_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
else
{
lean_object* v_self_2434_; lean_object* v___x_2436_; 
lean_dec_ref(v_e_2412_);
v_self_2434_ = lean_ctor_get(v_a_2425_, 0);
lean_inc_ref(v_self_2434_);
lean_dec(v_a_2425_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v_self_2434_);
v___x_2436_ = v___x_2427_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_self_2434_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
else
{
lean_object* v_self_2438_; lean_object* v___x_2439_; 
lean_del_object(v___x_2427_);
lean_dec_ref(v_e_2412_);
v_self_2438_ = lean_ctor_get(v_a_2425_, 0);
lean_inc_ref_n(v_self_2438_, 2);
lean_dec(v_a_2425_);
v___x_2439_ = l_Lean_Meta_isConstructorApp_x3f(v_self_2438_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2483_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2442_ = v___x_2439_;
v_isShared_2443_ = v_isSharedCheck_2483_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2439_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2483_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
if (lean_obj_tag(v_a_2440_) == 1)
{
lean_object* v_val_2444_; lean_object* v_numParams_2445_; lean_object* v_numFields_2446_; lean_object* v_nargs_2447_; lean_object* v___x_2448_; lean_object* v_dummy_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
lean_del_object(v___x_2442_);
v_val_2444_ = lean_ctor_get(v_a_2440_, 0);
lean_inc(v_val_2444_);
lean_dec_ref_known(v_a_2440_, 1);
v_numParams_2445_ = lean_ctor_get(v_val_2444_, 3);
lean_inc(v_numParams_2445_);
v_numFields_2446_ = lean_ctor_get(v_val_2444_, 4);
lean_inc(v_numFields_2446_);
lean_dec(v_val_2444_);
v_nargs_2447_ = l_Lean_Expr_getAppNumArgs(v_self_2438_);
v___x_2448_ = lean_nat_add(v_numParams_2445_, v_numFields_2446_);
lean_dec(v_numFields_2446_);
v_dummy_2449_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0);
lean_inc(v_nargs_2447_);
v___x_2450_ = lean_mk_array(v_nargs_2447_, v_dummy_2449_);
v___x_2451_ = lean_unsigned_to_nat(1u);
v___x_2452_ = lean_nat_sub(v_nargs_2447_, v___x_2451_);
lean_dec(v_nargs_2447_);
lean_inc_ref(v_self_2438_);
v___x_2453_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_2438_, v___x_2450_, v___x_2452_);
v___x_2454_ = 0;
v___x_2455_ = lean_box(v___x_2454_);
v___x_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2453_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v___x_2448_, v_ctor_2429_, v_numParams_2445_, v___x_2456_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
lean_dec(v___x_2448_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2471_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2460_ = v___x_2457_;
v_isShared_2461_ = v_isSharedCheck_2471_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2457_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2471_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v_snd_2462_; uint8_t v___x_2463_; 
v_snd_2462_ = lean_ctor_get(v_a_2458_, 1);
v___x_2463_ = lean_unbox(v_snd_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2465_; 
lean_dec(v_a_2458_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v_self_2438_);
v___x_2465_ = v___x_2460_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_self_2438_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
else
{
lean_object* v_fst_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
lean_del_object(v___x_2460_);
v_fst_2467_ = lean_ctor_get(v_a_2458_, 0);
lean_inc(v_fst_2467_);
lean_dec(v_a_2458_);
v___x_2468_ = l_Lean_Expr_getAppFn(v_self_2438_);
lean_dec_ref(v_self_2438_);
v___x_2469_ = l_Lean_mkAppN(v___x_2468_, v_fst_2467_);
lean_dec(v_fst_2467_);
v___x_2470_ = l_Lean_Meta_Sym_shareCommon(v___x_2469_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
return v___x_2470_;
}
}
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_dec_ref(v_self_2438_);
v_a_2472_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2457_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2457_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
else
{
lean_object* v___x_2481_; 
lean_dec(v_a_2440_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 0, v_self_2438_);
v___x_2481_ = v___x_2442_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_self_2438_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec_ref(v_self_2438_);
v_a_2484_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2439_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2439_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
}
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_dec_ref(v_e_2412_);
v_a_2493_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2424_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2424_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(lean_object* v_upperBound_2501_, uint8_t v___x_2502_, lean_object* v_a_2503_, lean_object* v_b_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
uint8_t v___x_2516_; 
v___x_2516_ = lean_nat_dec_lt(v_a_2503_, v_upperBound_2501_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; 
lean_dec(v_a_2503_);
v___x_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2517_, 0, v_b_2504_);
return v___x_2517_;
}
else
{
lean_object* v_fst_2518_; lean_object* v_snd_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2549_; 
v_fst_2518_ = lean_ctor_get(v_b_2504_, 0);
v_snd_2519_ = lean_ctor_get(v_b_2504_, 1);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_b_2504_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2521_ = v_b_2504_;
v_isShared_2522_ = v_isSharedCheck_2549_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_snd_2519_);
lean_inc(v_fst_2518_);
lean_dec(v_b_2504_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2549_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = l_Lean_instInhabitedExpr;
v___x_2524_ = lean_array_get_borrowed(v___x_2523_, v_fst_2518_, v_a_2503_);
lean_inc(v___x_2524_);
v___x_2525_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v___x_2524_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v_a_2528_; uint8_t v___x_2532_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2525_, 1);
v___x_2532_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2524_, v_a_2526_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2536_; 
lean_dec(v_snd_2519_);
v___x_2533_ = lean_array_set(v_fst_2518_, v_a_2503_, v_a_2526_);
v___x_2534_ = lean_box(v___x_2502_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 1, v___x_2534_);
lean_ctor_set(v___x_2521_, 0, v___x_2533_);
v___x_2536_ = v___x_2521_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v___x_2534_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
v_a_2528_ = v___x_2536_;
goto v___jp_2527_;
}
}
else
{
lean_object* v___x_2539_; 
lean_dec(v_a_2526_);
if (v_isShared_2522_ == 0)
{
v___x_2539_ = v___x_2521_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_fst_2518_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v_snd_2519_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
v_a_2528_ = v___x_2539_;
goto v___jp_2527_;
}
}
v___jp_2527_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = lean_unsigned_to_nat(1u);
v___x_2530_ = lean_nat_add(v_a_2503_, v___x_2529_);
lean_dec(v_a_2503_);
v_a_2503_ = v___x_2530_;
v_b_2504_ = v_a_2528_;
goto _start;
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_del_object(v___x_2521_);
lean_dec(v_snd_2519_);
lean_dec(v_fst_2518_);
lean_dec(v_a_2503_);
v_a_2541_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2525_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2525_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
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
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg___boxed(lean_object* v_upperBound_2550_, lean_object* v___x_2551_, lean_object* v_a_2552_, lean_object* v_b_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
uint8_t v___x_15930__boxed_2565_; lean_object* v_res_2566_; 
v___x_15930__boxed_2565_ = lean_unbox(v___x_2551_);
v_res_2566_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2550_, v___x_15930__boxed_2565_, v_a_2552_, v_b_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec(v_upperBound_2550_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go___boxed(lean_object* v_e_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_e_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_);
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
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(lean_object* v_upperBound_2580_, uint8_t v___x_2581_, lean_object* v_inst_2582_, lean_object* v_R_2583_, lean_object* v_a_2584_, lean_object* v_b_2585_, lean_object* v_c_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v___x_2598_; 
v___x_2598_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2580_, v___x_2581_, v_a_2584_, v_b_2585_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_2599_ = _args[0];
lean_object* v___x_2600_ = _args[1];
lean_object* v_inst_2601_ = _args[2];
lean_object* v_R_2602_ = _args[3];
lean_object* v_a_2603_ = _args[4];
lean_object* v_b_2604_ = _args[5];
lean_object* v_c_2605_ = _args[6];
lean_object* v___y_2606_ = _args[7];
lean_object* v___y_2607_ = _args[8];
lean_object* v___y_2608_ = _args[9];
lean_object* v___y_2609_ = _args[10];
lean_object* v___y_2610_ = _args[11];
lean_object* v___y_2611_ = _args[12];
lean_object* v___y_2612_ = _args[13];
lean_object* v___y_2613_ = _args[14];
lean_object* v___y_2614_ = _args[15];
lean_object* v___y_2615_ = _args[16];
lean_object* v___y_2616_ = _args[17];
_start:
{
uint8_t v___x_16171__boxed_2617_; lean_object* v_res_2618_; 
v___x_16171__boxed_2617_ = lean_unbox(v___x_2600_);
v_res_2618_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(v_upperBound_2599_, v___x_16171__boxed_2617_, v_inst_2601_, v_R_2602_, v_a_2603_, v_b_2604_, v_c_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec(v_upperBound_2599_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(lean_object* v_e_2619_, lean_object* v___y_2620_){
_start:
{
uint8_t v___x_2622_; uint8_t v___x_2623_; 
v___x_2622_ = l_Lean_Expr_hasMVar(v_e_2619_);
v___x_2623_ = lean_bool_not(v___x_2622_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; lean_object* v_mctx_2625_; lean_object* v___x_2626_; lean_object* v_fst_2627_; lean_object* v_snd_2628_; lean_object* v___x_2629_; lean_object* v_cache_2630_; lean_object* v_zetaDeltaFVarIds_2631_; lean_object* v_postponed_2632_; lean_object* v_diag_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2642_; 
v___x_2624_ = lean_st_ref_get(v___y_2620_);
v_mctx_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc_ref(v_mctx_2625_);
lean_dec(v___x_2624_);
v___x_2626_ = l_Lean_instantiateMVarsCore(v_mctx_2625_, v_e_2619_);
v_fst_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_fst_2627_);
v_snd_2628_ = lean_ctor_get(v___x_2626_, 1);
lean_inc(v_snd_2628_);
lean_dec_ref(v___x_2626_);
v___x_2629_ = lean_st_ref_take(v___y_2620_);
v_cache_2630_ = lean_ctor_get(v___x_2629_, 1);
v_zetaDeltaFVarIds_2631_ = lean_ctor_get(v___x_2629_, 2);
v_postponed_2632_ = lean_ctor_get(v___x_2629_, 3);
v_diag_2633_ = lean_ctor_get(v___x_2629_, 4);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2642_ == 0)
{
lean_object* v_unused_2643_; 
v_unused_2643_ = lean_ctor_get(v___x_2629_, 0);
lean_dec(v_unused_2643_);
v___x_2635_ = v___x_2629_;
v_isShared_2636_ = v_isSharedCheck_2642_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_diag_2633_);
lean_inc(v_postponed_2632_);
lean_inc(v_zetaDeltaFVarIds_2631_);
lean_inc(v_cache_2630_);
lean_dec(v___x_2629_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2642_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 0, v_snd_2628_);
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_snd_2628_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v_cache_2630_);
lean_ctor_set(v_reuseFailAlloc_2641_, 2, v_zetaDeltaFVarIds_2631_);
lean_ctor_set(v_reuseFailAlloc_2641_, 3, v_postponed_2632_);
lean_ctor_set(v_reuseFailAlloc_2641_, 4, v_diag_2633_);
v___x_2638_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2639_ = lean_st_ref_set(v___y_2620_, v___x_2638_);
v___x_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2640_, 0, v_fst_2627_);
return v___x_2640_;
}
}
}
else
{
lean_object* v___x_2644_; 
v___x_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2644_, 0, v_e_2619_);
return v___x_2644_;
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
uint8_t v___x_91947__boxed_3213_; lean_object* v_res_3214_; 
v___x_91947__boxed_3213_ = lean_unbox(v___x_3198_);
v_res_3214_ = l_Lean_Meta_Grind_tryToProveFalse___lam__1(v_arg_3197_, v___x_91947__boxed_3213_, v_e_3199_, v___f_3200_, v_cls_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
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
lean_object* v___x_3448_; uint8_t v___x_3449_; 
v___x_3448_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_3449_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3338_, v_options_3337_, v___x_3448_);
if (v___x_3449_ == 0)
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
lean_object* v___x_3450_; 
v___x_3450_ = l_Lean_Meta_Grind_updateLastTag(v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; 
lean_dec_ref_known(v___x_3450_, 1);
v___x_3451_ = lean_obj_once(&l_Lean_Meta_Grind_propagateMatchCondUp___closed__3, &l_Lean_Meta_Grind_propagateMatchCondUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3);
lean_inc_ref(v_e_3311_);
v___x_3452_ = l_Lean_indentExpr(v_e_3311_);
v___x_3453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3451_);
lean_ctor_set(v___x_3453_, 1, v___x_3452_);
v___x_3454_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3340_, v___x_3453_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_dec_ref_known(v___x_3454_, 1);
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
return v___x_3454_;
}
}
else
{
lean_dec_ref(v_e_3311_);
return v___x_3450_;
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
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3411_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3358_ = v___x_3355_;
v_isShared_3359_ = v_isSharedCheck_3411_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3355_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3411_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
uint8_t v___x_3360_; uint8_t v___x_3361_; 
v___x_3360_ = lean_unbox(v_a_3356_);
lean_dec(v_a_3356_);
v___x_3361_ = lean_bool_not(v___x_3360_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3362_; 
lean_del_object(v___x_3358_);
lean_inc_ref(v_e_3311_);
v___x_3362_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_3311_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
if (lean_obj_tag(v_a_3363_) == 1)
{
lean_object* v_options_3364_; uint8_t v_hasTrace_3365_; 
v_options_3364_ = lean_ctor_get(v___y_3350_, 2);
v_hasTrace_3365_ = lean_ctor_get_uint8(v_options_3364_, sizeof(void*)*1);
if (v_hasTrace_3365_ == 0)
{
lean_object* v_val_3366_; 
v_val_3366_ = lean_ctor_get(v_a_3363_, 0);
lean_inc(v_val_3366_);
lean_dec_ref_known(v_a_3363_, 1);
v___y_3327_ = v_val_3366_;
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
lean_object* v_val_3367_; lean_object* v_inheritedTraceOptions_3368_; lean_object* v___x_3369_; uint8_t v___x_3370_; 
v_val_3367_ = lean_ctor_get(v_a_3363_, 0);
lean_inc(v_val_3367_);
lean_dec_ref_known(v_a_3363_, 1);
v_inheritedTraceOptions_3368_ = lean_ctor_get(v___y_3350_, 13);
v___x_3369_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_3370_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3368_, v_options_3364_, v___x_3369_);
if (v___x_3370_ == 0)
{
v___y_3327_ = v_val_3367_;
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
lean_object* v___x_3371_; 
v___x_3371_ = l_Lean_Meta_Grind_updateLastTag(v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v___x_3372_; 
lean_dec_ref_known(v___x_3371_, 1);
lean_inc(v___y_3351_);
lean_inc_ref(v___y_3350_);
lean_inc(v___y_3349_);
lean_inc_ref(v___y_3348_);
lean_inc(v_val_3367_);
v___x_3372_ = lean_infer_type(v_val_3367_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc(v_a_3373_);
lean_dec_ref_known(v___x_3372_, 1);
v___x_3374_ = l_Lean_MessageData_ofExpr(v_a_3373_);
v___x_3375_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3340_, v___x_3374_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_dec_ref_known(v___x_3375_, 1);
v___y_3327_ = v_val_3367_;
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
lean_dec(v_val_3367_);
lean_dec_ref(v_e_3311_);
return v___x_3375_;
}
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
lean_dec(v_val_3367_);
lean_dec_ref(v_e_3311_);
v_a_3376_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3372_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3372_);
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
lean_dec(v_val_3367_);
lean_dec_ref(v_e_3311_);
return v___x_3371_;
}
}
}
}
else
{
lean_object* v___x_3384_; 
lean_dec(v_a_3363_);
v___x_3384_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_3346_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; uint8_t v_verbose_3386_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3384_, 1);
v_verbose_3386_ = lean_ctor_get_uint8(v_a_3385_, 0);
lean_dec(v_a_3385_);
if (v_verbose_3386_ == 0)
{
lean_dec_ref(v_e_3311_);
goto v___jp_3323_;
}
else
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3387_ = lean_obj_once(&l_Lean_Meta_Grind_propagateMatchCondUp___closed__1, &l_Lean_Meta_Grind_propagateMatchCondUp___closed__1_once, _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1);
v___x_3388_ = l_Lean_indentExpr(v_e_3311_);
v___x_3389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3387_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
v___x_3390_ = l_Lean_Meta_Sym_reportIssue(v___x_3389_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_dec_ref_known(v___x_3390_, 1);
goto v___jp_3323_;
}
else
{
return v___x_3390_;
}
}
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
lean_dec_ref(v_e_3311_);
v_a_3391_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3384_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3384_);
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
else
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_dec_ref(v_e_3311_);
v_a_3399_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3362_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3362_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
else
{
lean_object* v___x_3407_; lean_object* v___x_3409_; 
lean_dec_ref(v_e_3311_);
v___x_3407_ = lean_box(0);
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 0, v___x_3407_);
v___x_3409_ = v___x_3358_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3407_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
else
{
lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
lean_dec_ref(v_e_3311_);
v_a_3412_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3355_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3355_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
}
else
{
lean_object* v___x_3420_; 
lean_inc_ref(v_e_3311_);
v___x_3420_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3311_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3431_; 
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3423_ = v___x_3420_;
v_isShared_3424_ = v_isSharedCheck_3431_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3420_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3431_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
uint8_t v___x_3425_; 
v___x_3425_ = lean_unbox(v_a_3421_);
lean_dec(v_a_3421_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; 
lean_del_object(v___x_3423_);
v___x_3426_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3311_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
return v___x_3426_;
}
else
{
lean_object* v___x_3427_; lean_object* v___x_3429_; 
lean_dec_ref(v_e_3311_);
v___x_3427_ = lean_box(0);
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 0, v___x_3427_);
v___x_3429_ = v___x_3423_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3427_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
else
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
lean_dec_ref(v_e_3311_);
v_a_3432_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3434_ = v___x_3420_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3420_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3432_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
}
else
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_dec_ref(v_e_3311_);
v_a_3440_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___x_3352_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3352_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___boxed(lean_object* v_e_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_Meta_Grind_propagateMatchCondUp(v_e_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_);
lean_dec(v_a_3465_);
lean_dec_ref(v_a_3464_);
lean_dec(v_a_3463_);
lean_dec_ref(v_a_3462_);
lean_dec(v_a_3461_);
lean_dec_ref(v_a_3460_);
lean_dec(v_a_3459_);
lean_dec_ref(v_a_3458_);
lean_dec(v_a_3457_);
lean_dec(v_a_3456_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3469_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3470_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondUp___boxed), 12, 0);
v___x_3471_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3469_, v___x_3470_);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8____boxed(lean_object* v_a_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_();
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown(lean_object* v_e_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_){
_start:
{
lean_object* v___x_3486_; 
lean_inc_ref(v_e_3474_);
v___x_3486_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3474_, v_a_3475_, v_a_3479_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3516_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3489_ = v___x_3486_;
v_isShared_3490_ = v_isSharedCheck_3516_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3486_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3516_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
uint8_t v___x_3491_; 
v___x_3491_ = lean_unbox(v_a_3487_);
lean_dec(v_a_3487_);
if (v___x_3491_ == 0)
{
lean_object* v___x_3492_; lean_object* v___x_3494_; 
lean_dec_ref(v_e_3474_);
v___x_3492_ = lean_box(0);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 0, v___x_3492_);
v___x_3494_ = v___x_3489_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3492_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
else
{
lean_object* v___x_3496_; 
lean_del_object(v___x_3489_);
lean_inc_ref(v_e_3474_);
v___x_3496_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3507_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3499_ = v___x_3496_;
v_isShared_3500_ = v_isSharedCheck_3507_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3496_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3507_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
uint8_t v___x_3501_; 
v___x_3501_ = lean_unbox(v_a_3497_);
lean_dec(v_a_3497_);
if (v___x_3501_ == 0)
{
lean_object* v___x_3502_; 
lean_del_object(v___x_3499_);
v___x_3502_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_);
return v___x_3502_;
}
else
{
lean_object* v___x_3503_; lean_object* v___x_3505_; 
lean_dec_ref(v_e_3474_);
v___x_3503_ = lean_box(0);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v___x_3503_);
v___x_3505_ = v___x_3499_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v___x_3503_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec_ref(v_e_3474_);
v_a_3508_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3496_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3496_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
}
}
else
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
lean_dec_ref(v_e_3474_);
v_a_3517_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3519_ = v___x_3486_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3486_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3517_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___boxed(lean_object* v_e_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Lean_Meta_Grind_propagateMatchCondDown(v_e_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_);
lean_dec(v_a_3535_);
lean_dec_ref(v_a_3534_);
lean_dec(v_a_3533_);
lean_dec_ref(v_a_3532_);
lean_dec(v_a_3531_);
lean_dec_ref(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_a_3528_);
lean_dec(v_a_3527_);
lean_dec(v_a_3526_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3540_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondDown___boxed), 12, 0);
v___x_3541_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3539_, v___x_3540_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8____boxed(lean_object* v_a_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_();
return v_res_3543_;
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
