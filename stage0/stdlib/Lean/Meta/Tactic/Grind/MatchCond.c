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
lean_inc_ref(v_fst_104_);
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
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0(lean_object* v_k_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v_b_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
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
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_203_ = stack[0].m_obj;
lean_object* v___y_204_ = stack[1].m_obj;
lean_object* v___y_205_ = stack[2].m_obj;
lean_object* v___y_206_ = stack[3].m_obj;
lean_object* v___y_207_ = stack[4].m_obj;
lean_object* v___y_208_ = stack[5].m_obj;
lean_object* v___y_209_ = stack[6].m_obj;
lean_object* v_b_210_ = stack[7].m_obj;
lean_object* v___y_211_ = stack[8].m_obj;
lean_object* v___y_212_ = stack[9].m_obj;
lean_object* v___y_213_ = stack[10].m_obj;
lean_object* v___y_214_ = stack[11].m_obj;
lean_object* v_res_217_;
v_res_217_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0(v_k_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v_b_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
stack->m_obj
 = v_res_217_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v_b_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0(v_k_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v_b_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec(v___y_219_);
return v_res_231_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(lean_object* v_name_232_, uint8_t v_bi_233_, lean_object* v_type_234_, lean_object* v_k_235_, uint8_t v_kind_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v___f_248_; lean_object* v___x_249_; 
lean_inc(v___y_242_);
lean_inc_ref(v___y_241_);
lean_inc(v___y_240_);
lean_inc_ref(v___y_239_);
lean_inc(v___y_238_);
lean_inc(v___y_237_);
v___f_248_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_248_, 0, v_k_235_);
lean_closure_set(v___f_248_, 1, v___y_237_);
lean_closure_set(v___f_248_, 2, v___y_238_);
lean_closure_set(v___f_248_, 3, v___y_239_);
lean_closure_set(v___f_248_, 4, v___y_240_);
lean_closure_set(v___f_248_, 5, v___y_241_);
lean_closure_set(v___f_248_, 6, v___y_242_);
v___x_249_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_232_, v_bi_233_, v_type_234_, v___f_248_, v_kind_236_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
if (lean_obj_tag(v___x_249_) == 0)
{
return v___x_249_;
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_232_ = stack[0].m_obj;
uint8_t v_bi_233_ = stack[1].m_num;
lean_object* v_type_234_ = stack[2].m_obj;
lean_object* v_k_235_ = stack[3].m_obj;
uint8_t v_kind_236_ = stack[4].m_num;
lean_object* v___y_237_ = stack[5].m_obj;
lean_object* v___y_238_ = stack[6].m_obj;
lean_object* v___y_239_ = stack[7].m_obj;
lean_object* v___y_240_ = stack[8].m_obj;
lean_object* v___y_241_ = stack[9].m_obj;
lean_object* v___y_242_ = stack[10].m_obj;
lean_object* v___y_243_ = stack[11].m_obj;
lean_object* v___y_244_ = stack[12].m_obj;
lean_object* v___y_245_ = stack[13].m_obj;
lean_object* v___y_246_ = stack[14].m_obj;
lean_object* v_res_258_;
v_res_258_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_232_, v_bi_233_, v_type_234_, v_k_235_, v_kind_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
stack->m_obj
 = v_res_258_;
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
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(lean_object* v_name_278_, lean_object* v_type_279_, lean_object* v_k_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
uint8_t v___x_292_; uint8_t v___x_293_; lean_object* v___x_294_; 
v___x_292_ = 0;
v___x_293_ = 0;
v___x_294_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_278_, v___x_292_, v_type_279_, v_k_280_, v___x_293_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
return v___x_294_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_278_ = stack[0].m_obj;
lean_object* v_type_279_ = stack[1].m_obj;
lean_object* v_k_280_ = stack[2].m_obj;
lean_object* v___y_281_ = stack[3].m_obj;
lean_object* v___y_282_ = stack[4].m_obj;
lean_object* v___y_283_ = stack[5].m_obj;
lean_object* v___y_284_ = stack[6].m_obj;
lean_object* v___y_285_ = stack[7].m_obj;
lean_object* v___y_286_ = stack[8].m_obj;
lean_object* v___y_287_ = stack[9].m_obj;
lean_object* v___y_288_ = stack[10].m_obj;
lean_object* v___y_289_ = stack[11].m_obj;
lean_object* v___y_290_ = stack[12].m_obj;
lean_object* v_res_295_;
v_res_295_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v_name_278_, v_type_279_, v_k_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
stack->m_obj
 = v_res_295_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg___boxed(lean_object* v_name_296_, lean_object* v_type_297_, lean_object* v_k_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v_name_296_, v_type_297_, v_k_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec(v___y_299_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed(lean_object** _args){
lean_object* v_i_314_ = _args[0];
lean_object* v_xs_315_ = _args[1];
lean_object* v_tys_316_ = _args[2];
lean_object* v_tysxs_317_ = _args[3];
lean_object* v_args_318_ = _args[4];
lean_object* v_val_319_ = _args[5];
lean_object* v_fst_320_ = _args[6];
lean_object* v_e_321_ = _args[7];
lean_object* v_lhss_u03b1s_322_ = _args[8];
lean_object* v_ty_323_ = _args[9];
lean_object* v___y_324_ = _args[10];
lean_object* v___y_325_ = _args[11];
lean_object* v___y_326_ = _args[12];
lean_object* v___y_327_ = _args[13];
lean_object* v___y_328_ = _args[14];
lean_object* v___y_329_ = _args[15];
lean_object* v___y_330_ = _args[16];
lean_object* v___y_331_ = _args[17];
lean_object* v___y_332_ = _args[18];
lean_object* v___y_333_ = _args[19];
lean_object* v___y_334_ = _args[20];
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(v_i_314_, v_xs_315_, v_tys_316_, v_tysxs_317_, v_args_318_, v_val_319_, v_fst_320_, v_e_321_, v_lhss_u03b1s_322_, v_ty_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_325_);
lean_dec(v___y_324_);
return v_res_335_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(lean_object* v_i_339_, lean_object* v_xs_340_, lean_object* v_tys_341_, lean_object* v_tysxs_342_, lean_object* v_args_343_, lean_object* v_fst_344_, lean_object* v_e_345_, lean_object* v_lhss_u03b1s_346_, lean_object* v_x_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_359_ = lean_unsigned_to_nat(1u);
v___x_360_ = lean_nat_add(v_i_339_, v___x_359_);
lean_inc_ref(v_x_347_);
v___x_361_ = lean_array_push(v_xs_340_, v_x_347_);
v___x_362_ = lean_box(0);
v___x_363_ = lean_array_push(v_tys_341_, v___x_362_);
v___x_364_ = lean_array_push(v_tysxs_342_, v_x_347_);
v___x_365_ = lean_array_push(v_args_343_, v_fst_344_);
v___x_366_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_345_, v_lhss_u03b1s_346_, v___x_360_, v___x_361_, v___x_363_, v___x_364_, v___x_365_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
return v___x_366_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_339_ = stack[0].m_obj;
lean_object* v_xs_340_ = stack[1].m_obj;
lean_object* v_tys_341_ = stack[2].m_obj;
lean_object* v_tysxs_342_ = stack[3].m_obj;
lean_object* v_args_343_ = stack[4].m_obj;
lean_object* v_fst_344_ = stack[5].m_obj;
lean_object* v_e_345_ = stack[6].m_obj;
lean_object* v_lhss_u03b1s_346_ = stack[7].m_obj;
lean_object* v_x_347_ = stack[8].m_obj;
lean_object* v___y_348_ = stack[9].m_obj;
lean_object* v___y_349_ = stack[10].m_obj;
lean_object* v___y_350_ = stack[11].m_obj;
lean_object* v___y_351_ = stack[12].m_obj;
lean_object* v___y_352_ = stack[13].m_obj;
lean_object* v___y_353_ = stack[14].m_obj;
lean_object* v___y_354_ = stack[15].m_obj;
lean_object* v___y_355_ = stack[16].m_obj;
lean_object* v___y_356_ = stack[17].m_obj;
lean_object* v___y_357_ = stack[18].m_obj;
lean_object* v_res_367_;
v_res_367_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(v_i_339_, v_xs_340_, v_tys_341_, v_tysxs_342_, v_args_343_, v_fst_344_, v_e_345_, v_lhss_u03b1s_346_, v_x_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
stack->m_obj
 = v_res_367_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed(lean_object** _args){
lean_object* v_i_368_ = _args[0];
lean_object* v_xs_369_ = _args[1];
lean_object* v_tys_370_ = _args[2];
lean_object* v_tysxs_371_ = _args[3];
lean_object* v_args_372_ = _args[4];
lean_object* v_fst_373_ = _args[5];
lean_object* v_e_374_ = _args[6];
lean_object* v_lhss_u03b1s_375_ = _args[7];
lean_object* v_x_376_ = _args[8];
lean_object* v___y_377_ = _args[9];
lean_object* v___y_378_ = _args[10];
lean_object* v___y_379_ = _args[11];
lean_object* v___y_380_ = _args[12];
lean_object* v___y_381_ = _args[13];
lean_object* v___y_382_ = _args[14];
lean_object* v___y_383_ = _args[15];
lean_object* v___y_384_ = _args[16];
lean_object* v___y_385_ = _args[17];
lean_object* v___y_386_ = _args[18];
lean_object* v___y_387_ = _args[19];
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(v_i_368_, v_xs_369_, v_tys_370_, v_tysxs_371_, v_args_372_, v_fst_373_, v_e_374_, v_lhss_u03b1s_375_, v_x_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec(v___y_377_);
lean_dec(v_i_368_);
return v_res_388_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(lean_object* v_e_389_, lean_object* v_lhss_u03b1s_390_, lean_object* v_i_391_, lean_object* v_xs_392_, lean_object* v_tys_393_, lean_object* v_tysxs_394_, lean_object* v_args_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = lean_array_get_size(v_lhss_u03b1s_390_);
v___x_408_ = lean_nat_dec_lt(v_i_391_, v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v_eAbst_410_; uint8_t v___x_411_; uint8_t v___x_412_; lean_object* v___x_413_; 
lean_dec(v_i_391_);
lean_dec_ref(v_lhss_u03b1s_390_);
v___x_409_ = lean_unsigned_to_nat(0u);
v_eAbst_410_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_392_, v_tys_393_, v_e_389_, v___x_409_);
lean_dec_ref(v_tys_393_);
lean_dec_ref(v_xs_392_);
v___x_411_ = 1;
v___x_412_ = 1;
v___x_413_ = l_Lean_Meta_mkLambdaFVars(v_tysxs_394_, v_eAbst_410_, v___x_408_, v___x_411_, v___x_408_, v___x_411_, v___x_412_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
lean_dec_ref(v_tysxs_394_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_413_, 1);
v___x_415_ = l_Lean_mkAppN(v_a_414_, v_args_395_);
v___x_416_ = l_Lean_Meta_Sym_shareCommon(v___x_415_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_425_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_425_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_425_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_425_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v_args_395_);
lean_ctor_set(v___x_421_, 1, v_a_417_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_421_);
v___x_423_ = v___x_419_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec_ref(v_args_395_);
v_a_426_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_416_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_416_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec_ref(v_args_395_);
v_a_434_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_413_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_413_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
else
{
lean_object* v___x_442_; lean_object* v_snd_443_; 
v___x_442_ = lean_array_fget_borrowed(v_lhss_u03b1s_390_, v_i_391_);
v_snd_443_ = lean_ctor_get(v___x_442_, 1);
if (lean_obj_tag(v_snd_443_) == 1)
{
lean_object* v_fst_444_; lean_object* v_val_445_; lean_object* v___f_446_; lean_object* v___x_447_; 
v_fst_444_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_fst_444_);
v_val_445_ = lean_ctor_get(v_snd_443_, 0);
lean_inc_n(v_val_445_, 2);
lean_inc(v_i_391_);
v___f_446_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed), 21, 9);
lean_closure_set(v___f_446_, 0, v_i_391_);
lean_closure_set(v___f_446_, 1, v_xs_392_);
lean_closure_set(v___f_446_, 2, v_tys_393_);
lean_closure_set(v___f_446_, 3, v_tysxs_394_);
lean_closure_set(v___f_446_, 4, v_args_395_);
lean_closure_set(v___f_446_, 5, v_val_445_);
lean_closure_set(v___f_446_, 6, v_fst_444_);
lean_closure_set(v___f_446_, 7, v_e_389_);
lean_closure_set(v___f_446_, 8, v_lhss_u03b1s_390_);
lean_inc(v_a_405_);
lean_inc_ref(v_a_404_);
lean_inc(v_a_403_);
lean_inc_ref(v_a_402_);
v___x_447_ = lean_infer_type(v_val_445_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_447_, 1);
v___x_449_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__1));
v___x_450_ = lean_name_append_index_after(v___x_449_, v_i_391_);
v___x_451_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v___x_450_, v_a_448_, v___f_446_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
return v___x_451_;
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_dec_ref(v___f_446_);
lean_dec(v_i_391_);
v_a_452_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_447_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_447_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
else
{
lean_object* v_fst_460_; lean_object* v___f_461_; lean_object* v___x_462_; 
v_fst_460_ = lean_ctor_get(v___x_442_, 0);
lean_inc_n(v_fst_460_, 2);
lean_inc(v_i_391_);
v___f_461_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed), 20, 8);
lean_closure_set(v___f_461_, 0, v_i_391_);
lean_closure_set(v___f_461_, 1, v_xs_392_);
lean_closure_set(v___f_461_, 2, v_tys_393_);
lean_closure_set(v___f_461_, 3, v_tysxs_394_);
lean_closure_set(v___f_461_, 4, v_args_395_);
lean_closure_set(v___f_461_, 5, v_fst_460_);
lean_closure_set(v___f_461_, 6, v_e_389_);
lean_closure_set(v___f_461_, 7, v_lhss_u03b1s_390_);
lean_inc(v_a_405_);
lean_inc_ref(v_a_404_);
lean_inc(v_a_403_);
lean_inc_ref(v_a_402_);
v___x_462_ = lean_infer_type(v_fst_460_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
v___x_464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1));
v___x_465_ = lean_name_append_index_after(v___x_464_, v_i_391_);
v___x_466_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v___x_465_, v_a_463_, v___f_461_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
return v___x_466_;
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec_ref(v___f_461_);
lean_dec(v_i_391_);
v_a_467_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_462_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_462_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_389_ = stack[0].m_obj;
lean_object* v_lhss_u03b1s_390_ = stack[1].m_obj;
lean_object* v_i_391_ = stack[2].m_obj;
lean_object* v_xs_392_ = stack[3].m_obj;
lean_object* v_tys_393_ = stack[4].m_obj;
lean_object* v_tysxs_394_ = stack[5].m_obj;
lean_object* v_args_395_ = stack[6].m_obj;
lean_object* v_a_396_ = stack[7].m_obj;
lean_object* v_a_397_ = stack[8].m_obj;
lean_object* v_a_398_ = stack[9].m_obj;
lean_object* v_a_399_ = stack[10].m_obj;
lean_object* v_a_400_ = stack[11].m_obj;
lean_object* v_a_401_ = stack[12].m_obj;
lean_object* v_a_402_ = stack[13].m_obj;
lean_object* v_a_403_ = stack[14].m_obj;
lean_object* v_a_404_ = stack[15].m_obj;
lean_object* v_a_405_ = stack[16].m_obj;
lean_object* v_res_475_;
v_res_475_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_389_, v_lhss_u03b1s_390_, v_i_391_, v_xs_392_, v_tys_393_, v_tysxs_394_, v_args_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
stack->m_obj
 = v_res_475_;
}
lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(lean_object* v_i_476_, lean_object* v_xs_477_, lean_object* v_ty_478_, lean_object* v_tys_479_, lean_object* v_tysxs_480_, lean_object* v_args_481_, lean_object* v_val_482_, lean_object* v_fst_483_, lean_object* v_e_484_, lean_object* v_lhss_u03b1s_485_, lean_object* v_x_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_498_ = lean_unsigned_to_nat(1u);
v___x_499_ = lean_nat_add(v_i_476_, v___x_498_);
lean_inc_ref(v_x_486_);
v___x_500_ = lean_array_push(v_xs_477_, v_x_486_);
lean_inc_ref(v_ty_478_);
v___x_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_501_, 0, v_ty_478_);
v___x_502_ = lean_array_push(v_tys_479_, v___x_501_);
v___x_503_ = lean_array_push(v_tysxs_480_, v_ty_478_);
v___x_504_ = lean_array_push(v___x_503_, v_x_486_);
v___x_505_ = lean_array_push(v_args_481_, v_val_482_);
v___x_506_ = lean_array_push(v___x_505_, v_fst_483_);
v___x_507_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_484_, v_lhss_u03b1s_485_, v___x_499_, v___x_500_, v___x_502_, v___x_504_, v___x_506_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
return v___x_507_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_476_ = stack[0].m_obj;
lean_object* v_xs_477_ = stack[1].m_obj;
lean_object* v_ty_478_ = stack[2].m_obj;
lean_object* v_tys_479_ = stack[3].m_obj;
lean_object* v_tysxs_480_ = stack[4].m_obj;
lean_object* v_args_481_ = stack[5].m_obj;
lean_object* v_val_482_ = stack[6].m_obj;
lean_object* v_fst_483_ = stack[7].m_obj;
lean_object* v_e_484_ = stack[8].m_obj;
lean_object* v_lhss_u03b1s_485_ = stack[9].m_obj;
lean_object* v_x_486_ = stack[10].m_obj;
lean_object* v___y_487_ = stack[11].m_obj;
lean_object* v___y_488_ = stack[12].m_obj;
lean_object* v___y_489_ = stack[13].m_obj;
lean_object* v___y_490_ = stack[14].m_obj;
lean_object* v___y_491_ = stack[15].m_obj;
lean_object* v___y_492_ = stack[16].m_obj;
lean_object* v___y_493_ = stack[17].m_obj;
lean_object* v___y_494_ = stack[18].m_obj;
lean_object* v___y_495_ = stack[19].m_obj;
lean_object* v___y_496_ = stack[20].m_obj;
lean_object* v_res_508_;
v_res_508_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(v_i_476_, v_xs_477_, v_ty_478_, v_tys_479_, v_tysxs_480_, v_args_481_, v_val_482_, v_fst_483_, v_e_484_, v_lhss_u03b1s_485_, v_x_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
stack->m_obj
 = v_res_508_;
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
lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(lean_object* v_i_532_, lean_object* v_xs_533_, lean_object* v_tys_534_, lean_object* v_tysxs_535_, lean_object* v_args_536_, lean_object* v_val_537_, lean_object* v_fst_538_, lean_object* v_e_539_, lean_object* v_lhss_u03b1s_540_, lean_object* v_ty_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_532_ = stack[0].m_obj;
lean_object* v_xs_533_ = stack[1].m_obj;
lean_object* v_tys_534_ = stack[2].m_obj;
lean_object* v_tysxs_535_ = stack[3].m_obj;
lean_object* v_args_536_ = stack[4].m_obj;
lean_object* v_val_537_ = stack[5].m_obj;
lean_object* v_fst_538_ = stack[6].m_obj;
lean_object* v_e_539_ = stack[7].m_obj;
lean_object* v_lhss_u03b1s_540_ = stack[8].m_obj;
lean_object* v_ty_541_ = stack[9].m_obj;
lean_object* v___y_542_ = stack[10].m_obj;
lean_object* v___y_543_ = stack[11].m_obj;
lean_object* v___y_544_ = stack[12].m_obj;
lean_object* v___y_545_ = stack[13].m_obj;
lean_object* v___y_546_ = stack[14].m_obj;
lean_object* v___y_547_ = stack[15].m_obj;
lean_object* v___y_548_ = stack[16].m_obj;
lean_object* v___y_549_ = stack[17].m_obj;
lean_object* v___y_550_ = stack[18].m_obj;
lean_object* v___y_551_ = stack[19].m_obj;
lean_object* v_res_557_;
v_res_557_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(v_i_532_, v_xs_533_, v_tys_534_, v_tysxs_535_, v_args_536_, v_val_537_, v_fst_538_, v_e_539_, v_lhss_u03b1s_540_, v_ty_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
stack->m_obj
 = v_res_557_;
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
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0(lean_object* v_00_u03b1_577_, lean_object* v_name_578_, uint8_t v_bi_579_, lean_object* v_type_580_, lean_object* v_k_581_, uint8_t v_kind_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_578_, v_bi_579_, v_type_580_, v_k_581_, v_kind_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
return v___x_594_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_578_ = stack[1].m_obj;
uint8_t v_bi_579_ = stack[2].m_num;
lean_object* v_type_580_ = stack[3].m_obj;
lean_object* v_k_581_ = stack[4].m_obj;
uint8_t v_kind_582_ = stack[5].m_num;
lean_object* v___y_583_ = stack[6].m_obj;
lean_object* v___y_584_ = stack[7].m_obj;
lean_object* v___y_585_ = stack[8].m_obj;
lean_object* v___y_586_ = stack[9].m_obj;
lean_object* v___y_587_ = stack[10].m_obj;
lean_object* v___y_588_ = stack[11].m_obj;
lean_object* v___y_589_ = stack[12].m_obj;
lean_object* v___y_590_ = stack[13].m_obj;
lean_object* v___y_591_ = stack[14].m_obj;
lean_object* v___y_592_ = stack[15].m_obj;
lean_object* v_res_595_;
v_res_595_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0(lean_box(0), v_name_578_, v_bi_579_, v_type_580_, v_k_581_, v_kind_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
stack->m_obj
 = v_res_595_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_596_ = _args[0];
lean_object* v_name_597_ = _args[1];
lean_object* v_bi_598_ = _args[2];
lean_object* v_type_599_ = _args[3];
lean_object* v_k_600_ = _args[4];
lean_object* v_kind_601_ = _args[5];
lean_object* v___y_602_ = _args[6];
lean_object* v___y_603_ = _args[7];
lean_object* v___y_604_ = _args[8];
lean_object* v___y_605_ = _args[9];
lean_object* v___y_606_ = _args[10];
lean_object* v___y_607_ = _args[11];
lean_object* v___y_608_ = _args[12];
lean_object* v___y_609_ = _args[13];
lean_object* v___y_610_ = _args[14];
lean_object* v___y_611_ = _args[15];
lean_object* v___y_612_ = _args[16];
_start:
{
uint8_t v_bi_boxed_613_; uint8_t v_kind_boxed_614_; lean_object* v_res_615_; 
v_bi_boxed_613_ = lean_unbox(v_bi_598_);
v_kind_boxed_614_ = lean_unbox(v_kind_601_);
v_res_615_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0(v_00_u03b1_596_, v_name_597_, v_bi_boxed_613_, v_type_599_, v_k_600_, v_kind_boxed_614_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec(v___y_602_);
return v_res_615_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0(lean_object* v_00_u03b1_616_, lean_object* v_name_617_, lean_object* v_type_618_, lean_object* v_k_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v_name_617_, v_type_618_, v_k_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
return v___x_631_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_617_ = stack[1].m_obj;
lean_object* v_type_618_ = stack[2].m_obj;
lean_object* v_k_619_ = stack[3].m_obj;
lean_object* v___y_620_ = stack[4].m_obj;
lean_object* v___y_621_ = stack[5].m_obj;
lean_object* v___y_622_ = stack[6].m_obj;
lean_object* v___y_623_ = stack[7].m_obj;
lean_object* v___y_624_ = stack[8].m_obj;
lean_object* v___y_625_ = stack[9].m_obj;
lean_object* v___y_626_ = stack[10].m_obj;
lean_object* v___y_627_ = stack[11].m_obj;
lean_object* v___y_628_ = stack[12].m_obj;
lean_object* v___y_629_ = stack[13].m_obj;
lean_object* v_res_632_;
v_res_632_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0(lean_box(0), v_name_617_, v_type_618_, v_k_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
stack->m_obj
 = v_res_632_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___boxed(lean_object* v_00_u03b1_633_, lean_object* v_name_634_, lean_object* v_type_635_, lean_object* v_k_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0(v_00_u03b1_633_, v_name_634_, v_type_635_, v_k_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec(v___y_637_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter___redArg(lean_object* v_x_649_, lean_object* v_h__1_650_){
_start:
{
lean_object* v_fst_651_; lean_object* v_snd_652_; lean_object* v___x_653_; 
v_fst_651_ = lean_ctor_get(v_x_649_, 0);
lean_inc(v_fst_651_);
v_snd_652_ = lean_ctor_get(v_x_649_, 1);
lean_inc(v_snd_652_);
lean_dec_ref(v_x_649_);
v___x_653_ = lean_apply_2(v_h__1_650_, v_fst_651_, v_snd_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter(lean_object* v_motive_654_, lean_object* v_x_655_, lean_object* v_h__1_656_){
_start:
{
lean_object* v_fst_657_; lean_object* v_snd_658_; lean_object* v___x_659_; 
v_fst_657_ = lean_ctor_get(v_x_655_, 0);
lean_inc(v_fst_657_);
v_snd_658_ = lean_ctor_get(v_x_655_, 1);
lean_inc(v_snd_658_);
lean_dec_ref(v_x_655_);
v___x_659_ = lean_apply_2(v_h__1_656_, v_fst_657_, v_snd_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter___redArg(lean_object* v_00_u03b1_x3f_660_, lean_object* v_h__1_661_, lean_object* v_h__2_662_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter(lean_object* v_motive_666_, lean_object* v_00_u03b1_x3f_667_, lean_object* v_h__1_668_, lean_object* v_h__2_669_){
_start:
{
if (lean_obj_tag(v_00_u03b1_x3f_667_) == 1)
{
lean_object* v_val_670_; lean_object* v___x_671_; 
lean_dec(v_h__2_669_);
v_val_670_ = lean_ctor_get(v_00_u03b1_x3f_667_, 0);
lean_inc(v_val_670_);
lean_dec_ref_known(v_00_u03b1_x3f_667_, 1);
v___x_671_ = lean_apply_1(v_h__1_668_, v_val_670_);
return v___x_671_;
}
else
{
lean_object* v___x_672_; 
lean_dec(v_h__1_668_);
v___x_672_ = lean_apply_2(v_h__2_669_, v_00_u03b1_x3f_667_, lean_box(0));
return v___x_672_;
}
}
}
lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(lean_object* v_matchCond_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v___x_698_; uint8_t v___x_699_; 
lean_inc_ref(v_matchCond_682_);
v___x_698_ = l_Lean_Expr_cleanupAnnotations(v_matchCond_682_);
v___x_699_ = l_Lean_Expr_isApp(v___x_698_);
if (v___x_699_ == 0)
{
lean_dec_ref(v___x_698_);
goto v___jp_694_;
}
else
{
lean_object* v_arg_700_; lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v_arg_700_ = lean_ctor_get(v___x_698_, 1);
lean_inc_ref(v_arg_700_);
v___x_701_ = l_Lean_Expr_appFnCleanup___redArg(v___x_698_);
v___x_702_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_703_ = l_Lean_Expr_isConstOf(v___x_701_, v___x_702_);
lean_dec_ref(v___x_701_);
if (v___x_703_ == 0)
{
lean_dec_ref(v_arg_700_);
goto v___jp_694_;
}
else
{
lean_object* v_lhss_u03b1s_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
lean_dec_ref(v_matchCond_682_);
lean_inc_ref(v_arg_700_);
v_lhss_u03b1s_704_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss(v_arg_700_);
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0));
v___x_707_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_arg_700_, v_lhss_u03b1s_704_, v___x_705_, v___x_706_, v___x_706_, v___x_706_, v___x_706_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
return v___x_707_;
}
}
v___jp_694_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0));
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v_matchCond_682_);
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_0interp(lean_interpreter_value* stack)
{
lean_object* v_matchCond_682_ = stack[0].m_obj;
lean_object* v_a_683_ = stack[1].m_obj;
lean_object* v_a_684_ = stack[2].m_obj;
lean_object* v_a_685_ = stack[3].m_obj;
lean_object* v_a_686_ = stack[4].m_obj;
lean_object* v_a_687_ = stack[5].m_obj;
lean_object* v_a_688_ = stack[6].m_obj;
lean_object* v_a_689_ = stack[7].m_obj;
lean_object* v_a_690_ = stack[8].m_obj;
lean_object* v_a_691_ = stack[9].m_obj;
lean_object* v_a_692_ = stack[10].m_obj;
lean_object* v_res_708_;
v_res_708_ = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(v_matchCond_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
stack->m_obj
 = v_res_708_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___boxed(lean_object* v_matchCond_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(v_matchCond_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec(v_a_710_);
return v_res_721_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0(void){
_start:
{
lean_object* v___x_725_; lean_object* v_dummy_726_; 
v___x_725_ = lean_box(0);
v_dummy_726_ = l_Lean_Expr_sort___override(v___x_725_);
return v_dummy_726_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(lean_object* v_lhs_727_, lean_object* v_rhs_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
uint8_t v___x_740_; 
v___x_740_ = l_Lean_Expr_hasLooseBVars(v_lhs_727_);
if (v___x_740_ == 0)
{
uint8_t v___x_741_; lean_object* v___x_742_; 
v___x_741_ = 1;
v___x_742_ = l_Lean_Meta_Grind_getRootENode___redArg(v_lhs_727_, v_a_729_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_883_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_883_ == 0)
{
v___x_745_ = v___x_742_;
v_isShared_746_ = v_isSharedCheck_883_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_742_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_883_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
uint8_t v_ctor_747_; 
v_ctor_747_ = lean_ctor_get_uint8(v_a_743_, sizeof(void*)*12 + 2);
if (v_ctor_747_ == 0)
{
uint8_t v_interpreted_748_; 
v_interpreted_748_ = lean_ctor_get_uint8(v_a_743_, sizeof(void*)*12 + 1);
if (v_interpreted_748_ == 0)
{
lean_object* v___x_749_; lean_object* v___x_751_; 
lean_dec(v_a_743_);
lean_dec_ref(v_rhs_728_);
v___x_749_ = lean_box(v_interpreted_748_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_749_);
v___x_751_ = v___x_745_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
else
{
lean_object* v_self_753_; uint8_t v___x_754_; 
v_self_753_ = lean_ctor_get(v_a_743_, 0);
lean_inc_ref(v_self_753_);
lean_dec(v_a_743_);
v___x_754_ = l_Lean_Expr_hasLooseBVars(v_rhs_728_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; 
lean_del_object(v___x_745_);
lean_inc_ref(v_rhs_728_);
v___x_755_ = l_Lean_Meta_isLitValue(v_rhs_728_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; uint8_t v___x_757_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v___x_757_ = lean_unbox(v_a_756_);
if (v___x_757_ == 0)
{
lean_dec_ref(v_self_753_);
lean_dec_ref(v_rhs_728_);
return v___x_755_;
}
else
{
lean_object* v___x_758_; 
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_755_, 1);
v___x_758_ = l_Lean_Meta_normLitValue(v_self_753_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_760_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v___x_758_, 1);
v___x_760_ = l_Lean_Meta_normLitValue(v_rhs_728_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_773_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_773_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_773_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_773_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
uint8_t v___x_765_; 
v___x_765_ = lean_expr_eqv(v_a_759_, v_a_761_);
lean_dec(v_a_761_);
lean_dec(v_a_759_);
if (v___x_765_ == 0)
{
lean_object* v___x_767_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v_a_756_);
v___x_767_ = v___x_763_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_756_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
else
{
lean_object* v___x_769_; lean_object* v___x_771_; 
lean_dec(v_a_756_);
v___x_769_ = lean_box(v___x_754_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_769_);
v___x_771_ = v___x_763_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec(v_a_759_);
lean_dec(v_a_756_);
v_a_774_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_760_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_760_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_dec(v_a_756_);
lean_dec_ref(v_rhs_728_);
v_a_782_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_758_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_758_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
else
{
lean_dec_ref(v_self_753_);
lean_dec_ref(v_rhs_728_);
return v___x_755_;
}
}
else
{
lean_object* v___x_790_; lean_object* v___x_792_; 
lean_dec_ref(v_self_753_);
lean_dec_ref(v_rhs_728_);
v___x_790_ = lean_box(v_ctor_747_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_790_);
v___x_792_ = v___x_745_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_object* v_self_794_; lean_object* v___x_795_; 
lean_del_object(v___x_745_);
v_self_794_ = lean_ctor_get(v_a_743_, 0);
lean_inc_ref_n(v_self_794_, 2);
lean_dec(v_a_743_);
v___x_795_ = l_Lean_Meta_isConstructorApp_x3f(v_self_794_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_874_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_874_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_874_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_874_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
if (lean_obj_tag(v_a_796_) == 1)
{
lean_object* v_val_800_; lean_object* v___x_801_; 
lean_del_object(v___x_798_);
v_val_800_ = lean_ctor_get(v_a_796_, 0);
lean_inc(v_val_800_);
lean_dec_ref_known(v_a_796_, 1);
lean_inc_ref(v_rhs_728_);
v___x_801_ = l_Lean_Meta_isConstructorApp_x3f(v_rhs_728_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_861_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_861_ == 0)
{
v___x_804_ = v___x_801_;
v_isShared_805_ = v_isSharedCheck_861_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_861_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
if (lean_obj_tag(v_a_802_) == 1)
{
lean_object* v_toConstantVal_806_; lean_object* v_val_807_; lean_object* v_toConstantVal_808_; lean_object* v_numParams_809_; lean_object* v_numFields_810_; lean_object* v_name_811_; lean_object* v_name_812_; uint8_t v___x_813_; 
v_toConstantVal_806_ = lean_ctor_get(v_val_800_, 0);
lean_inc_ref(v_toConstantVal_806_);
v_val_807_ = lean_ctor_get(v_a_802_, 0);
lean_inc(v_val_807_);
lean_dec_ref_known(v_a_802_, 1);
v_toConstantVal_808_ = lean_ctor_get(v_val_807_, 0);
lean_inc_ref(v_toConstantVal_808_);
lean_dec(v_val_807_);
v_numParams_809_ = lean_ctor_get(v_val_800_, 3);
lean_inc(v_numParams_809_);
v_numFields_810_ = lean_ctor_get(v_val_800_, 4);
lean_inc(v_numFields_810_);
lean_dec(v_val_800_);
v_name_811_ = lean_ctor_get(v_toConstantVal_806_, 0);
lean_inc(v_name_811_);
lean_dec_ref(v_toConstantVal_806_);
v_name_812_ = lean_ctor_get(v_toConstantVal_808_, 0);
lean_inc(v_name_812_);
lean_dec_ref(v_toConstantVal_808_);
v___x_813_ = lean_name_eq(v_name_811_, v_name_812_);
lean_dec(v_name_812_);
lean_dec(v_name_811_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_816_; 
lean_dec(v_numFields_810_);
lean_dec(v_numParams_809_);
lean_dec_ref(v_self_794_);
lean_dec_ref(v_rhs_728_);
v___x_814_ = lean_box(v___x_741_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_814_);
v___x_816_ = v___x_804_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
else
{
if (v___x_740_ == 0)
{
lean_object* v_nargs_818_; lean_object* v_nargs_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v_dummy_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
lean_del_object(v___x_804_);
v_nargs_818_ = l_Lean_Expr_getAppNumArgs(v_self_794_);
v_nargs_819_ = l_Lean_Expr_getAppNumArgs(v_rhs_728_);
v___x_820_ = lean_nat_add(v_numParams_809_, v_numFields_810_);
lean_dec(v_numFields_810_);
v___x_821_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0));
v_dummy_822_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0);
lean_inc(v_nargs_818_);
v___x_823_ = lean_mk_array(v_nargs_818_, v_dummy_822_);
v___x_824_ = lean_unsigned_to_nat(1u);
v___x_825_ = lean_nat_sub(v_nargs_818_, v___x_824_);
lean_dec(v_nargs_818_);
v___x_826_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_794_, v___x_823_, v___x_825_);
lean_inc(v_nargs_819_);
v___x_827_ = lean_mk_array(v_nargs_819_, v_dummy_822_);
v___x_828_ = lean_nat_sub(v_nargs_819_, v___x_824_);
lean_dec(v_nargs_819_);
v___x_829_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_rhs_728_, v___x_827_, v___x_828_);
v___x_830_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v___x_820_, v___x_826_, v___x_829_, v_numParams_809_, v___x_821_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
lean_dec_ref(v___x_829_);
lean_dec_ref(v___x_826_);
lean_dec(v___x_820_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_844_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_844_ == 0)
{
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_844_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_844_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v_fst_835_; 
v_fst_835_ = lean_ctor_get(v_a_831_, 0);
lean_inc(v_fst_835_);
lean_dec(v_a_831_);
if (lean_obj_tag(v_fst_835_) == 0)
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = lean_box(v___x_740_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_836_);
v___x_838_ = v___x_833_;
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
lean_object* v_val_840_; lean_object* v___x_842_; 
v_val_840_ = lean_ctor_get(v_fst_835_, 0);
lean_inc(v_val_840_);
lean_dec_ref_known(v_fst_835_, 1);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v_val_840_);
v___x_842_ = v___x_833_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_val_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_845_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_830_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_830_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
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
lean_object* v___x_853_; lean_object* v___x_855_; 
lean_dec(v_numFields_810_);
lean_dec(v_numParams_809_);
lean_dec_ref(v_self_794_);
lean_dec_ref(v_rhs_728_);
v___x_853_ = lean_box(v___x_741_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_853_);
v___x_855_ = v___x_804_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
else
{
lean_object* v___x_857_; lean_object* v___x_859_; 
lean_dec(v_a_802_);
lean_dec(v_val_800_);
lean_dec_ref(v_self_794_);
lean_dec_ref(v_rhs_728_);
v___x_857_ = lean_box(v___x_740_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_857_);
v___x_859_ = v___x_804_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec(v_val_800_);
lean_dec_ref(v_self_794_);
lean_dec_ref(v_rhs_728_);
v_a_862_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_801_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_801_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
else
{
lean_object* v___x_870_; lean_object* v___x_872_; 
lean_dec(v_a_796_);
lean_dec_ref(v_self_794_);
lean_dec_ref(v_rhs_728_);
v___x_870_ = lean_box(v___x_740_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_870_);
v___x_872_ = v___x_798_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
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
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec_ref(v_self_794_);
lean_dec_ref(v_rhs_728_);
v_a_875_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_795_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_795_);
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
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec_ref(v_rhs_728_);
v_a_884_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_742_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_742_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
lean_dec_ref(v_rhs_728_);
lean_dec_ref(v_lhs_727_);
v___x_892_ = 0;
v___x_893_ = lean_box(v___x_892_);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_727_ = stack[0].m_obj;
lean_object* v_rhs_728_ = stack[1].m_obj;
lean_object* v_a_729_ = stack[2].m_obj;
lean_object* v_a_730_ = stack[3].m_obj;
lean_object* v_a_731_ = stack[4].m_obj;
lean_object* v_a_732_ = stack[5].m_obj;
lean_object* v_a_733_ = stack[6].m_obj;
lean_object* v_a_734_ = stack[7].m_obj;
lean_object* v_a_735_ = stack[8].m_obj;
lean_object* v_a_736_ = stack[9].m_obj;
lean_object* v_a_737_ = stack[10].m_obj;
lean_object* v_a_738_ = stack[11].m_obj;
lean_object* v_res_895_;
v_res_895_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v_lhs_727_, v_rhs_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
stack->m_obj
 = v_res_895_;
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(lean_object* v_upperBound_896_, lean_object* v___x_897_, lean_object* v___x_898_, lean_object* v_a_899_, lean_object* v_b_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
uint8_t v___x_912_; 
v___x_912_ = lean_nat_dec_lt(v_a_899_, v_upperBound_896_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; 
lean_dec(v_a_899_);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v_b_900_);
return v___x_913_;
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
lean_dec_ref(v_b_900_);
v___x_914_ = l_Lean_instInhabitedExpr;
v___x_915_ = lean_box(0);
v___x_916_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0));
v___x_917_ = lean_array_get_borrowed(v___x_914_, v___x_897_, v_a_899_);
v___x_918_ = lean_array_get_borrowed(v___x_914_, v___x_898_, v_a_899_);
lean_inc(v___x_918_);
lean_inc(v___x_917_);
v___x_919_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v___x_917_, v___x_918_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_934_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_934_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_934_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_934_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
uint8_t v___x_924_; 
v___x_924_ = lean_unbox(v_a_920_);
lean_dec(v_a_920_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; 
lean_del_object(v___x_922_);
v___x_925_ = lean_unsigned_to_nat(1u);
v___x_926_ = lean_nat_add(v_a_899_, v___x_925_);
lean_dec(v_a_899_);
v_a_899_ = v___x_926_;
v_b_900_ = v___x_916_;
goto _start;
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
lean_dec(v_a_899_);
v___x_928_ = lean_box(v___x_912_);
v___x_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v___x_915_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_930_);
v___x_932_ = v___x_922_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec(v_a_899_);
v_a_935_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_919_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_919_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_896_ = stack[0].m_obj;
lean_object* v___x_897_ = stack[1].m_obj;
lean_object* v___x_898_ = stack[2].m_obj;
lean_object* v_a_899_ = stack[3].m_obj;
lean_object* v_b_900_ = stack[4].m_obj;
lean_object* v___y_901_ = stack[5].m_obj;
lean_object* v___y_902_ = stack[6].m_obj;
lean_object* v___y_903_ = stack[7].m_obj;
lean_object* v___y_904_ = stack[8].m_obj;
lean_object* v___y_905_ = stack[9].m_obj;
lean_object* v___y_906_ = stack[10].m_obj;
lean_object* v___y_907_ = stack[11].m_obj;
lean_object* v___y_908_ = stack[12].m_obj;
lean_object* v___y_909_ = stack[13].m_obj;
lean_object* v___y_910_ = stack[14].m_obj;
lean_object* v_res_943_;
v_res_943_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v_upperBound_896_, v___x_897_, v___x_898_, v_a_899_, v_b_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
stack->m_obj
 = v_res_943_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___boxed(lean_object* v_upperBound_944_, lean_object* v___x_945_, lean_object* v___x_946_, lean_object* v_a_947_, lean_object* v_b_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v_upperBound_944_, v___x_945_, v___x_946_, v_a_947_, v_b_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___x_946_);
lean_dec_ref(v___x_945_);
lean_dec(v_upperBound_944_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___boxed(lean_object* v_lhs_961_, lean_object* v_rhs_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v_lhs_961_, v_rhs_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_a_964_);
lean_dec(v_a_963_);
return v_res_974_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(lean_object* v_upperBound_975_, lean_object* v___x_976_, lean_object* v___x_977_, lean_object* v_inst_978_, lean_object* v_R_979_, lean_object* v_a_980_, lean_object* v_b_981_, lean_object* v_c_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v_upperBound_975_, v___x_976_, v___x_977_, v_a_980_, v_b_981_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
return v___x_994_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_975_ = stack[0].m_obj;
lean_object* v___x_976_ = stack[1].m_obj;
lean_object* v___x_977_ = stack[2].m_obj;
lean_object* v_a_980_ = stack[5].m_obj;
lean_object* v_b_981_ = stack[6].m_obj;
lean_object* v___y_983_ = stack[8].m_obj;
lean_object* v___y_984_ = stack[9].m_obj;
lean_object* v___y_985_ = stack[10].m_obj;
lean_object* v___y_986_ = stack[11].m_obj;
lean_object* v___y_987_ = stack[12].m_obj;
lean_object* v___y_988_ = stack[13].m_obj;
lean_object* v___y_989_ = stack[14].m_obj;
lean_object* v___y_990_ = stack[15].m_obj;
lean_object* v___y_991_ = stack[16].m_obj;
lean_object* v___y_992_ = stack[17].m_obj;
lean_object* v_res_995_;
v_res_995_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(v_upperBound_975_, v___x_976_, v___x_977_, lean_box(0), lean_box(0), v_a_980_, v_b_981_, lean_box(0), v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
stack->m_obj
 = v_res_995_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_996_ = _args[0];
lean_object* v___x_997_ = _args[1];
lean_object* v___x_998_ = _args[2];
lean_object* v_inst_999_ = _args[3];
lean_object* v_R_1000_ = _args[4];
lean_object* v_a_1001_ = _args[5];
lean_object* v_b_1002_ = _args[6];
lean_object* v_c_1003_ = _args[7];
lean_object* v___y_1004_ = _args[8];
lean_object* v___y_1005_ = _args[9];
lean_object* v___y_1006_ = _args[10];
lean_object* v___y_1007_ = _args[11];
lean_object* v___y_1008_ = _args[12];
lean_object* v___y_1009_ = _args[13];
lean_object* v___y_1010_ = _args[14];
lean_object* v___y_1011_ = _args[15];
lean_object* v___y_1012_ = _args[16];
lean_object* v___y_1013_ = _args[17];
lean_object* v___y_1014_ = _args[18];
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(v_upperBound_996_, v___x_997_, v___x_998_, v_inst_999_, v_R_1000_, v_a_1001_, v_b_1002_, v_c_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___x_998_);
lean_dec_ref(v___x_997_);
lean_dec(v_upperBound_996_);
return v_res_1015_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(lean_object* v_e_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_e_1016_);
if (lean_obj_tag(v___x_1028_) == 1)
{
lean_object* v_val_1029_; lean_object* v_snd_1030_; lean_object* v_fst_1031_; lean_object* v_snd_1032_; lean_object* v___x_1033_; 
v_val_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_val_1029_);
lean_dec_ref_known(v___x_1028_, 1);
v_snd_1030_ = lean_ctor_get(v_val_1029_, 1);
lean_inc(v_snd_1030_);
lean_dec(v_val_1029_);
v_fst_1031_ = lean_ctor_get(v_snd_1030_, 0);
lean_inc(v_fst_1031_);
v_snd_1032_ = lean_ctor_get(v_snd_1030_, 1);
lean_inc(v_snd_1032_);
lean_dec(v_snd_1030_);
v___x_1033_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v_fst_1031_, v_snd_1032_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
return v___x_1033_;
}
else
{
uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
lean_dec(v___x_1028_);
v___x_1034_ = 0;
v___x_1035_ = lean_box(v___x_1034_);
v___x_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
return v___x_1036_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1016_ = stack[0].m_obj;
lean_object* v_a_1017_ = stack[1].m_obj;
lean_object* v_a_1018_ = stack[2].m_obj;
lean_object* v_a_1019_ = stack[3].m_obj;
lean_object* v_a_1020_ = stack[4].m_obj;
lean_object* v_a_1021_ = stack[5].m_obj;
lean_object* v_a_1022_ = stack[6].m_obj;
lean_object* v_a_1023_ = stack[7].m_obj;
lean_object* v_a_1024_ = stack[8].m_obj;
lean_object* v_a_1025_ = stack[9].m_obj;
lean_object* v_a_1026_ = stack[10].m_obj;
lean_object* v_res_1037_;
v_res_1037_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_e_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
stack->m_obj
 = v_res_1037_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp___boxed(lean_object* v_e_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_e_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec(v_a_1039_);
return v_res_1050_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(uint8_t v___x_1051_, lean_object* v_snd_1052_, lean_object* v_____r_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1065_ = lean_box(v___x_1051_);
v___x_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v_snd_1052_);
v___x_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1051_ = stack[0].m_num;
lean_object* v_snd_1052_ = stack[1].m_obj;
lean_object* v_____r_1053_ = stack[2].m_obj;
lean_object* v___y_1054_ = stack[3].m_obj;
lean_object* v___y_1055_ = stack[4].m_obj;
lean_object* v___y_1056_ = stack[5].m_obj;
lean_object* v___y_1057_ = stack[6].m_obj;
lean_object* v___y_1058_ = stack[7].m_obj;
lean_object* v___y_1059_ = stack[8].m_obj;
lean_object* v___y_1060_ = stack[9].m_obj;
lean_object* v___y_1061_ = stack[10].m_obj;
lean_object* v___y_1062_ = stack[11].m_obj;
lean_object* v___y_1063_ = stack[12].m_obj;
lean_object* v_res_1070_;
v_res_1070_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_1051_, v_snd_1052_, v_____r_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
stack->m_obj
 = v_res_1070_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0___boxed(lean_object* v___x_1071_, lean_object* v_snd_1072_, lean_object* v_____r_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
uint8_t v___x_23429__boxed_1085_; lean_object* v_res_1086_; 
v___x_23429__boxed_1085_ = lean_unbox(v___x_1071_);
v_res_1086_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_23429__boxed_1085_, v_snd_1072_, v_____r_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec(v___y_1074_);
return v_res_1086_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(lean_object* v_msgData_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___x_1093_; lean_object* v_env_1094_; uint8_t v___x_1095_; lean_object* v_env_1096_; lean_object* v___x_1097_; lean_object* v_toCold_1098_; lean_object* v_mctx_1099_; lean_object* v_lctx_1100_; lean_object* v_options_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1093_ = lean_st_ref_get(v___y_1091_);
v_env_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc_ref(v_env_1094_);
lean_dec(v___x_1093_);
v___x_1095_ = 0;
v_env_1096_ = l_Lean_Environment_setRecordingDeps(v_env_1094_, v___x_1095_);
v___x_1097_ = lean_st_ref_get(v___y_1089_);
v_toCold_1098_ = lean_ctor_get(v___y_1090_, 0);
v_mctx_1099_ = lean_ctor_get(v___x_1097_, 0);
lean_inc_ref(v_mctx_1099_);
lean_dec(v___x_1097_);
v_lctx_1100_ = lean_ctor_get(v___y_1088_, 2);
v_options_1101_ = lean_ctor_get(v_toCold_1098_, 2);
lean_inc_ref(v_options_1101_);
lean_inc_ref(v_lctx_1100_);
v___x_1102_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1102_, 0, v_env_1096_);
lean_ctor_set(v___x_1102_, 1, v_mctx_1099_);
lean_ctor_set(v___x_1102_, 2, v_lctx_1100_);
lean_ctor_set(v___x_1102_, 3, v_options_1101_);
v___x_1103_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set(v___x_1103_, 1, v_msgData_1087_);
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1087_ = stack[0].m_obj;
lean_object* v___y_1088_ = stack[1].m_obj;
lean_object* v___y_1089_ = stack[2].m_obj;
lean_object* v___y_1090_ = stack[3].m_obj;
lean_object* v___y_1091_ = stack[4].m_obj;
lean_object* v_res_1105_;
v_res_1105_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(v_msgData_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
stack->m_obj
 = v_res_1105_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0___boxed(lean_object* v_msgData_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(v_msgData_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
return v_res_1112_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1113_; double v___x_1114_; 
v___x_1113_ = lean_unsigned_to_nat(0u);
v___x_1114_ = lean_float_of_nat(v___x_1113_);
return v___x_1114_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(lean_object* v_cls_1118_, lean_object* v_msg_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_ref_1125_; lean_object* v___x_1126_; lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1172_; 
v_ref_1125_ = lean_ctor_get(v___y_1122_, 2);
v___x_1126_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(v_msg_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1129_ = v___x_1126_;
v_isShared_1130_ = v_isSharedCheck_1172_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1172_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v_traceState_1132_; lean_object* v_env_1133_; lean_object* v_nextMacroScope_1134_; lean_object* v_ngen_1135_; lean_object* v_auxDeclNGen_1136_; lean_object* v_cache_1137_; lean_object* v_recordedDeps_1138_; lean_object* v_messages_1139_; lean_object* v_infoState_1140_; lean_object* v_snapshotTasks_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1171_; 
v___x_1131_ = lean_st_ref_take(v___y_1123_);
v_traceState_1132_ = lean_ctor_get(v___x_1131_, 4);
v_env_1133_ = lean_ctor_get(v___x_1131_, 0);
v_nextMacroScope_1134_ = lean_ctor_get(v___x_1131_, 1);
v_ngen_1135_ = lean_ctor_get(v___x_1131_, 2);
v_auxDeclNGen_1136_ = lean_ctor_get(v___x_1131_, 3);
v_cache_1137_ = lean_ctor_get(v___x_1131_, 5);
v_recordedDeps_1138_ = lean_ctor_get(v___x_1131_, 6);
v_messages_1139_ = lean_ctor_get(v___x_1131_, 7);
v_infoState_1140_ = lean_ctor_get(v___x_1131_, 8);
v_snapshotTasks_1141_ = lean_ctor_get(v___x_1131_, 9);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1143_ = v___x_1131_;
v_isShared_1144_ = v_isSharedCheck_1171_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_snapshotTasks_1141_);
lean_inc(v_infoState_1140_);
lean_inc(v_messages_1139_);
lean_inc(v_recordedDeps_1138_);
lean_inc(v_cache_1137_);
lean_inc(v_traceState_1132_);
lean_inc(v_auxDeclNGen_1136_);
lean_inc(v_ngen_1135_);
lean_inc(v_nextMacroScope_1134_);
lean_inc(v_env_1133_);
lean_dec(v___x_1131_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1171_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
uint64_t v_tid_1145_; lean_object* v_traces_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1170_; 
v_tid_1145_ = lean_ctor_get_uint64(v_traceState_1132_, sizeof(void*)*1);
v_traces_1146_ = lean_ctor_get(v_traceState_1132_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_traceState_1132_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1148_ = v_traceState_1132_;
v_isShared_1149_ = v_isSharedCheck_1170_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_traces_1146_);
lean_dec(v_traceState_1132_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1170_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; double v___x_1152_; uint8_t v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1150_ = lean_box(0);
v___x_1151_ = lean_box(0);
v___x_1152_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0);
v___x_1153_ = 0;
v___x_1154_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1));
v___x_1155_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1155_, 0, v_cls_1118_);
lean_ctor_set(v___x_1155_, 1, v___x_1151_);
lean_ctor_set(v___x_1155_, 2, v___x_1154_);
lean_ctor_set_float(v___x_1155_, sizeof(void*)*3, v___x_1152_);
lean_ctor_set_float(v___x_1155_, sizeof(void*)*3 + 8, v___x_1152_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3 + 16, v___x_1153_);
v___x_1156_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__2));
v___x_1157_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v_a_1127_);
lean_ctor_set(v___x_1157_, 2, v___x_1156_);
lean_inc(v_ref_1125_);
v___x_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1158_, 0, v_ref_1125_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = l_Lean_PersistentArray_push___redArg(v_traces_1146_, v___x_1158_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1159_);
v___x_1161_ = v___x_1148_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1159_);
lean_ctor_set_uint64(v_reuseFailAlloc_1169_, sizeof(void*)*1, v_tid_1145_);
v___x_1161_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1163_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 4, v___x_1161_);
v___x_1163_ = v___x_1143_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_env_1133_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_nextMacroScope_1134_);
lean_ctor_set(v_reuseFailAlloc_1168_, 2, v_ngen_1135_);
lean_ctor_set(v_reuseFailAlloc_1168_, 3, v_auxDeclNGen_1136_);
lean_ctor_set(v_reuseFailAlloc_1168_, 4, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1168_, 5, v_cache_1137_);
lean_ctor_set(v_reuseFailAlloc_1168_, 6, v_recordedDeps_1138_);
lean_ctor_set(v_reuseFailAlloc_1168_, 7, v_messages_1139_);
lean_ctor_set(v_reuseFailAlloc_1168_, 8, v_infoState_1140_);
lean_ctor_set(v_reuseFailAlloc_1168_, 9, v_snapshotTasks_1141_);
v___x_1163_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1164_ = lean_st_ref_put(v___y_1123_, v___x_1163_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1150_);
v___x_1166_ = v___x_1129_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1150_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1118_ = stack[0].m_obj;
lean_object* v_msg_1119_ = stack[1].m_obj;
lean_object* v___y_1120_ = stack[2].m_obj;
lean_object* v___y_1121_ = stack[3].m_obj;
lean_object* v___y_1122_ = stack[4].m_obj;
lean_object* v___y_1123_ = stack[5].m_obj;
lean_object* v_res_1173_;
v_res_1173_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1118_, v_msg_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
stack->m_obj
 = v_res_1173_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___boxed(lean_object* v_cls_1174_, lean_object* v_msg_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1174_, v_msg_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
return v_res_1181_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1192_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_1193_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5));
v___x_1194_ = l_Lean_Name_append(v___x_1193_, v___x_1192_);
return v___x_1194_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__7));
v___x_1197_ = l_Lean_stringToMessageData(v___x_1196_);
return v___x_1197_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__9));
v___x_1200_ = l_Lean_stringToMessageData(v___x_1199_);
return v___x_1200_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(uint8_t v___x_1201_, lean_object* v_a_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___y_1215_; lean_object* v_snd_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1298_; 
v_snd_1235_ = lean_ctor_get(v_a_1202_, 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_a_1202_);
if (v_isSharedCheck_1298_ == 0)
{
lean_object* v_unused_1299_; 
v_unused_1299_ = lean_ctor_get(v_a_1202_, 0);
lean_dec(v_unused_1299_);
v___x_1237_ = v_a_1202_;
v_isShared_1238_ = v_isSharedCheck_1298_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_snd_1235_);
lean_dec(v_a_1202_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1298_;
goto v_resetjp_1236_;
}
v___jp_1214_:
{
if (lean_obj_tag(v___y_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1226_; 
v_a_1216_ = lean_ctor_get(v___y_1215_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___y_1215_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1218_ = v___y_1215_;
v_isShared_1219_ = v_isSharedCheck_1226_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___y_1215_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1226_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
if (lean_obj_tag(v_a_1216_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1222_; 
v_a_1220_ = lean_ctor_get(v_a_1216_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v_a_1216_, 1);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v_a_1220_);
v___x_1222_ = v___x_1218_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
else
{
lean_object* v_a_1224_; 
lean_del_object(v___x_1218_);
v_a_1224_ = lean_ctor_get(v_a_1216_, 0);
lean_inc(v_a_1224_);
lean_dec_ref_known(v_a_1216_, 1);
v_a_1202_ = v_a_1224_;
goto _start;
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
v_a_1227_ = lean_ctor_get(v___y_1215_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___y_1215_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___y_1215_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___y_1215_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; 
v___x_1239_ = lean_box(0);
if (lean_obj_tag(v_snd_1235_) == 7)
{
lean_object* v_binderType_1240_; lean_object* v_body_1241_; lean_object* v___x_1245_; 
v_binderType_1240_ = lean_ctor_get(v_snd_1235_, 1);
v_body_1241_ = lean_ctor_get(v_snd_1235_, 2);
lean_inc_ref(v_binderType_1240_);
v___x_1245_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_binderType_1240_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; uint8_t v___x_1247_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref_known(v___x_1245_, 1);
v___x_1247_ = lean_unbox(v_a_1246_);
lean_dec(v_a_1246_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1249_; 
lean_inc_ref(v_body_1241_);
lean_dec_ref_known(v_snd_1235_, 3);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 1, v_body_1241_);
lean_ctor_set(v___x_1237_, 0, v___x_1239_);
v___x_1249_ = v___x_1237_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_body_1241_);
v___x_1249_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
v_a_1202_ = v___x_1249_;
goto _start;
}
}
else
{
lean_object* v_toCold_1252_; lean_object* v_options_1253_; uint8_t v_hasTrace_1254_; 
lean_del_object(v___x_1237_);
v_toCold_1252_ = lean_ctor_get(v___y_1211_, 0);
v_options_1253_ = lean_ctor_get(v_toCold_1252_, 2);
v_hasTrace_1254_ = lean_ctor_get_uint8(v_options_1253_, sizeof(void*)*1);
if (v_hasTrace_1254_ == 0)
{
goto v___jp_1242_;
}
else
{
lean_object* v_inheritedTraceOptions_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v_inheritedTraceOptions_1255_ = lean_ctor_get(v_toCold_1252_, 11);
v___x_1256_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_1257_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_1258_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1255_, v_options_1253_, v___x_1257_);
if (v___x_1258_ == 0)
{
goto v___jp_1242_;
}
else
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_Meta_Grind_updateLastTag(v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_dec_ref_known(v___x_1259_, 1);
v___x_1260_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8);
lean_inc_ref(v_snd_1235_);
v___x_1261_ = l_Lean_indentExpr(v_snd_1235_);
v___x_1262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10);
v___x_1264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
lean_inc_ref(v_binderType_1240_);
v___x_1265_ = l_Lean_indentExpr(v_binderType_1240_);
v___x_1266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1264_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_1256_, v___x_1266_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1269_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1269_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_1201_, v_snd_1235_, v_a_1268_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
v___y_1215_ = v___x_1269_;
goto v___jp_1214_;
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec_ref_known(v_snd_1235_, 3);
v_a_1270_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1267_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1267_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec_ref_known(v_snd_1235_, 3);
v_a_1278_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1259_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1259_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec_ref_known(v_snd_1235_, 3);
lean_del_object(v___x_1237_);
v_a_1286_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1245_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1245_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
v___jp_1242_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_box(0);
v___x_1244_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_1201_, v_snd_1235_, v___x_1243_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
v___y_1215_ = v___x_1244_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1295_; 
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v___x_1239_);
v___x_1295_ = v___x_1237_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_snd_1235_);
v___x_1295_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
lean_object* v___x_1296_; 
v___x_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
return v___x_1296_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1201_ = stack[0].m_num;
lean_object* v_a_1202_ = stack[1].m_obj;
lean_object* v___y_1203_ = stack[2].m_obj;
lean_object* v___y_1204_ = stack[3].m_obj;
lean_object* v___y_1205_ = stack[4].m_obj;
lean_object* v___y_1206_ = stack[5].m_obj;
lean_object* v___y_1207_ = stack[6].m_obj;
lean_object* v___y_1208_ = stack[7].m_obj;
lean_object* v___y_1209_ = stack[8].m_obj;
lean_object* v___y_1210_ = stack[9].m_obj;
lean_object* v___y_1211_ = stack[10].m_obj;
lean_object* v___y_1212_ = stack[11].m_obj;
lean_object* v_res_1300_;
v_res_1300_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_1201_, v_a_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
stack->m_obj
 = v_res_1300_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___boxed(lean_object* v___x_1301_, lean_object* v_a_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
uint8_t v___x_23741__boxed_1314_; lean_object* v_res_1315_; 
v___x_23741__boxed_1314_ = lean_unbox(v___x_1301_);
v_res_1315_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_23741__boxed_1314_, v_a_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec(v___y_1303_);
return v_res_1315_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(lean_object* v_e_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1316_, v_a_1324_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
lean_dec_ref_known(v___x_1332_, 1);
v___x_1334_ = l_Lean_Expr_cleanupAnnotations(v_a_1333_);
v___x_1335_ = l_Lean_Expr_isApp(v___x_1334_);
if (v___x_1335_ == 0)
{
lean_dec_ref(v___x_1334_);
goto v___jp_1328_;
}
else
{
lean_object* v_arg_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v_arg_1336_ = lean_ctor_get(v___x_1334_, 1);
lean_inc_ref(v_arg_1336_);
v___x_1337_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1334_);
v___x_1338_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_1339_ = l_Lean_Expr_isConstOf(v___x_1337_, v___x_1338_);
lean_dec_ref(v___x_1337_);
if (v___x_1339_ == 0)
{
lean_dec_ref(v_arg_1336_);
goto v___jp_1328_;
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1340_ = lean_box(0);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
lean_ctor_set(v___x_1341_, 1, v_arg_1336_);
v___x_1342_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_1339_, v___x_1341_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1357_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1357_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1357_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v_fst_1347_; 
v_fst_1347_ = lean_ctor_get(v_a_1343_, 0);
lean_inc(v_fst_1347_);
lean_dec(v_a_1343_);
if (lean_obj_tag(v_fst_1347_) == 0)
{
uint8_t v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1348_ = 0;
v___x_1349_ = lean_box(v___x_1348_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1349_);
v___x_1351_ = v___x_1345_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
else
{
lean_object* v_val_1353_; lean_object* v___x_1355_; 
v_val_1353_ = lean_ctor_get(v_fst_1347_, 0);
lean_inc(v_val_1353_);
lean_dec_ref_known(v_fst_1347_, 1);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v_val_1353_);
v___x_1355_ = v___x_1345_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_val_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
v_a_1358_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1342_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1342_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
v_a_1366_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1332_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1332_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
v___jp_1328_:
{
uint8_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = 0;
v___x_1330_ = lean_box(v___x_1329_);
v___x_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
return v___x_1331_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1316_ = stack[0].m_obj;
lean_object* v_a_1317_ = stack[1].m_obj;
lean_object* v_a_1318_ = stack[2].m_obj;
lean_object* v_a_1319_ = stack[3].m_obj;
lean_object* v_a_1320_ = stack[4].m_obj;
lean_object* v_a_1321_ = stack[5].m_obj;
lean_object* v_a_1322_ = stack[6].m_obj;
lean_object* v_a_1323_ = stack[7].m_obj;
lean_object* v_a_1324_ = stack[8].m_obj;
lean_object* v_a_1325_ = stack[9].m_obj;
lean_object* v_a_1326_ = stack[10].m_obj;
lean_object* v_res_1374_;
v_res_1374_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
stack->m_obj
 = v_res_1374_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied___boxed(lean_object* v_e_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
lean_dec(v_a_1379_);
lean_dec_ref(v_a_1378_);
lean_dec(v_a_1377_);
lean_dec(v_a_1376_);
return v_res_1387_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(lean_object* v_cls_1388_, lean_object* v_msg_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1388_, v_msg_1389_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1401_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1388_ = stack[0].m_obj;
lean_object* v_msg_1389_ = stack[1].m_obj;
lean_object* v___y_1390_ = stack[2].m_obj;
lean_object* v___y_1391_ = stack[3].m_obj;
lean_object* v___y_1392_ = stack[4].m_obj;
lean_object* v___y_1393_ = stack[5].m_obj;
lean_object* v___y_1394_ = stack[6].m_obj;
lean_object* v___y_1395_ = stack[7].m_obj;
lean_object* v___y_1396_ = stack[8].m_obj;
lean_object* v___y_1397_ = stack[9].m_obj;
lean_object* v___y_1398_ = stack[10].m_obj;
lean_object* v___y_1399_ = stack[11].m_obj;
lean_object* v_res_1402_;
v_res_1402_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(v_cls_1388_, v_msg_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
stack->m_obj
 = v_res_1402_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___boxed(lean_object* v_cls_1403_, lean_object* v_msg_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(v_cls_1403_, v_msg_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec(v___y_1405_);
return v_res_1416_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(uint8_t v___x_1417_, lean_object* v_inst_1418_, lean_object* v_a_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_1417_, v_a_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
return v___x_1431_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1417_ = stack[0].m_num;
lean_object* v_a_1419_ = stack[2].m_obj;
lean_object* v___y_1420_ = stack[3].m_obj;
lean_object* v___y_1421_ = stack[4].m_obj;
lean_object* v___y_1422_ = stack[5].m_obj;
lean_object* v___y_1423_ = stack[6].m_obj;
lean_object* v___y_1424_ = stack[7].m_obj;
lean_object* v___y_1425_ = stack[8].m_obj;
lean_object* v___y_1426_ = stack[9].m_obj;
lean_object* v___y_1427_ = stack[10].m_obj;
lean_object* v___y_1428_ = stack[11].m_obj;
lean_object* v___y_1429_ = stack[12].m_obj;
lean_object* v_res_1432_;
v_res_1432_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(v___x_1417_, lean_box(0), v_a_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
stack->m_obj
 = v_res_1432_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___boxed(lean_object* v___x_1433_, lean_object* v_inst_1434_, lean_object* v_a_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
uint8_t v___x_24294__boxed_1447_; lean_object* v_res_1448_; 
v___x_24294__boxed_1447_ = lean_unbox(v___x_1433_);
v_res_1448_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(v___x_24294__boxed_1447_, v_inst_1434_, v_a_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec(v___y_1436_);
return v_res_1448_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(lean_object* v_k_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v_b_1456_, lean_object* v_c_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1463_; 
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1460_);
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1458_);
lean_inc(v___y_1455_);
lean_inc_ref(v___y_1454_);
lean_inc(v___y_1453_);
lean_inc_ref(v___y_1452_);
lean_inc(v___y_1451_);
lean_inc(v___y_1450_);
v___x_1463_ = lean_apply_13(v_k_1449_, v_b_1456_, v_c_1457_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, lean_box(0));
return v___x_1463_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1449_ = stack[0].m_obj;
lean_object* v___y_1450_ = stack[1].m_obj;
lean_object* v___y_1451_ = stack[2].m_obj;
lean_object* v___y_1452_ = stack[3].m_obj;
lean_object* v___y_1453_ = stack[4].m_obj;
lean_object* v___y_1454_ = stack[5].m_obj;
lean_object* v___y_1455_ = stack[6].m_obj;
lean_object* v_b_1456_ = stack[7].m_obj;
lean_object* v_c_1457_ = stack[8].m_obj;
lean_object* v___y_1458_ = stack[9].m_obj;
lean_object* v___y_1459_ = stack[10].m_obj;
lean_object* v___y_1460_ = stack[11].m_obj;
lean_object* v___y_1461_ = stack[12].m_obj;
lean_object* v_res_1464_;
v_res_1464_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(v_k_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v_b_1456_, v_c_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
stack->m_obj
 = v_res_1464_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed(lean_object* v_k_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v_b_1472_, lean_object* v_c_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(v_k_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v_b_1472_, v_c_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec(v___y_1466_);
return v_res_1479_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(lean_object* v_type_1480_, lean_object* v_k_1481_, uint8_t v_cleanupAnnotations_1482_, uint8_t v_whnfType_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v___f_1495_; lean_object* v___x_1496_; 
lean_inc(v___y_1489_);
lean_inc_ref(v___y_1488_);
lean_inc(v___y_1487_);
lean_inc_ref(v___y_1486_);
lean_inc(v___y_1485_);
lean_inc(v___y_1484_);
v___f_1495_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1495_, 0, v_k_1481_);
lean_closure_set(v___f_1495_, 1, v___y_1484_);
lean_closure_set(v___f_1495_, 2, v___y_1485_);
lean_closure_set(v___f_1495_, 3, v___y_1486_);
lean_closure_set(v___f_1495_, 4, v___y_1487_);
lean_closure_set(v___f_1495_, 5, v___y_1488_);
lean_closure_set(v___f_1495_, 6, v___y_1489_);
v___x_1496_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1480_, v___f_1495_, v_cleanupAnnotations_1482_, v_whnfType_1483_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
if (lean_obj_tag(v___x_1496_) == 0)
{
return v___x_1496_;
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1496_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1480_ = stack[0].m_obj;
lean_object* v_k_1481_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_1482_ = stack[2].m_num;
uint8_t v_whnfType_1483_ = stack[3].m_num;
lean_object* v___y_1484_ = stack[4].m_obj;
lean_object* v___y_1485_ = stack[5].m_obj;
lean_object* v___y_1486_ = stack[6].m_obj;
lean_object* v___y_1487_ = stack[7].m_obj;
lean_object* v___y_1488_ = stack[8].m_obj;
lean_object* v___y_1489_ = stack[9].m_obj;
lean_object* v___y_1490_ = stack[10].m_obj;
lean_object* v___y_1491_ = stack[11].m_obj;
lean_object* v___y_1492_ = stack[12].m_obj;
lean_object* v___y_1493_ = stack[13].m_obj;
lean_object* v_res_1505_;
v_res_1505_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_1480_, v_k_1481_, v_cleanupAnnotations_1482_, v_whnfType_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
stack->m_obj
 = v_res_1505_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___boxed(lean_object* v_type_1506_, lean_object* v_k_1507_, lean_object* v_cleanupAnnotations_1508_, lean_object* v_whnfType_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1521_; uint8_t v_whnfType_boxed_1522_; lean_object* v_res_1523_; 
v_cleanupAnnotations_boxed_1521_ = lean_unbox(v_cleanupAnnotations_1508_);
v_whnfType_boxed_1522_ = lean_unbox(v_whnfType_1509_);
v_res_1523_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_1506_, v_k_1507_, v_cleanupAnnotations_boxed_1521_, v_whnfType_boxed_1522_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec(v___y_1510_);
return v_res_1523_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(lean_object* v_00_u03b1_1524_, lean_object* v_type_1525_, lean_object* v_k_1526_, uint8_t v_cleanupAnnotations_1527_, uint8_t v_whnfType_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_1525_, v_k_1526_, v_cleanupAnnotations_1527_, v_whnfType_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
return v___x_1540_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1525_ = stack[1].m_obj;
lean_object* v_k_1526_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_1527_ = stack[3].m_num;
uint8_t v_whnfType_1528_ = stack[4].m_num;
lean_object* v___y_1529_ = stack[5].m_obj;
lean_object* v___y_1530_ = stack[6].m_obj;
lean_object* v___y_1531_ = stack[7].m_obj;
lean_object* v___y_1532_ = stack[8].m_obj;
lean_object* v___y_1533_ = stack[9].m_obj;
lean_object* v___y_1534_ = stack[10].m_obj;
lean_object* v___y_1535_ = stack[11].m_obj;
lean_object* v___y_1536_ = stack[12].m_obj;
lean_object* v___y_1537_ = stack[13].m_obj;
lean_object* v___y_1538_ = stack[14].m_obj;
lean_object* v_res_1541_;
v_res_1541_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(lean_box(0), v_type_1525_, v_k_1526_, v_cleanupAnnotations_1527_, v_whnfType_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
stack->m_obj
 = v_res_1541_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___boxed(lean_object* v_00_u03b1_1542_, lean_object* v_type_1543_, lean_object* v_k_1544_, lean_object* v_cleanupAnnotations_1545_, lean_object* v_whnfType_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1558_; uint8_t v_whnfType_boxed_1559_; lean_object* v_res_1560_; 
v_cleanupAnnotations_boxed_1558_ = lean_unbox(v_cleanupAnnotations_1545_);
v_whnfType_boxed_1559_ = lean_unbox(v_whnfType_1546_);
v_res_1560_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(v_00_u03b1_1542_, v_type_1543_, v_k_1544_, v_cleanupAnnotations_boxed_1558_, v_whnfType_boxed_1559_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec(v___y_1547_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed(lean_object** _args){
lean_object* v_e_1564_ = _args[0];
lean_object* v_name_1565_ = _args[1];
lean_object* v_name_1566_ = _args[2];
lean_object* v_a_1567_ = _args[3];
lean_object* v_a_1568_ = _args[4];
lean_object* v_xs_1569_ = _args[5];
lean_object* v_x_1570_ = _args[6];
lean_object* v___y_1571_ = _args[7];
lean_object* v___y_1572_ = _args[8];
lean_object* v___y_1573_ = _args[9];
lean_object* v___y_1574_ = _args[10];
lean_object* v___y_1575_ = _args[11];
lean_object* v___y_1576_ = _args[12];
lean_object* v___y_1577_ = _args[13];
lean_object* v___y_1578_ = _args[14];
lean_object* v___y_1579_ = _args[15];
lean_object* v___y_1580_ = _args[16];
lean_object* v___y_1581_ = _args[17];
_start:
{
uint8_t v_a_80142__boxed_1582_; lean_object* v_res_1583_; 
v_a_80142__boxed_1582_ = lean_unbox(v_a_1567_);
v_res_1583_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(v_e_1564_, v_name_1565_, v_name_1566_, v_a_80142__boxed_1582_, v_a_1568_, v_xs_1569_, v_x_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v_x_1570_);
lean_dec_ref(v_xs_1569_);
lean_dec(v_name_1566_);
lean_dec(v_name_1565_);
return v_res_1583_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__0));
v___x_1586_ = l_Lean_stringToMessageData(v___x_1585_);
return v___x_1586_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3(void){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__2));
v___x_1589_ = l_Lean_stringToMessageData(v___x_1588_);
return v___x_1589_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__4));
v___x_1592_ = l_Lean_stringToMessageData(v___x_1591_);
return v___x_1592_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(lean_object* v_e_1593_, lean_object* v_h_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
uint8_t v___y_1610_; uint8_t v___y_1611_; lean_object* v___y_1612_; uint8_t v___y_1613_; lean_object* v___y_1614_; lean_object* v_h_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; uint8_t v___y_1811_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v_toCold_1985_; lean_object* v_options_1986_; uint8_t v_hasTrace_1987_; 
v_toCold_1985_ = lean_ctor_get(v_a_1603_, 0);
v_options_1986_ = lean_ctor_get(v_toCold_1985_, 2);
v_hasTrace_1987_ = lean_ctor_get_uint8(v_options_1986_, sizeof(void*)*1);
if (v_hasTrace_1987_ == 0)
{
v___y_1888_ = v_a_1595_;
v___y_1889_ = v_a_1596_;
v___y_1890_ = v_a_1597_;
v___y_1891_ = v_a_1598_;
v___y_1892_ = v_a_1599_;
v___y_1893_ = v_a_1600_;
v___y_1894_ = v_a_1601_;
v___y_1895_ = v_a_1602_;
v___y_1896_ = v_a_1603_;
v___y_1897_ = v_a_1604_;
goto v___jp_1887_;
}
else
{
lean_object* v_inheritedTraceOptions_1988_; lean_object* v_cls_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v_inheritedTraceOptions_1988_ = lean_ctor_get(v_toCold_1985_, 11);
v_cls_1989_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_1990_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_1991_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1988_, v_options_1986_, v___x_1990_);
if (v___x_1991_ == 0)
{
v___y_1888_ = v_a_1595_;
v___y_1889_ = v_a_1596_;
v___y_1890_ = v_a_1597_;
v___y_1891_ = v_a_1598_;
v___y_1892_ = v_a_1599_;
v___y_1893_ = v_a_1600_;
v___y_1894_ = v_a_1601_;
v___y_1895_ = v_a_1602_;
v___y_1896_ = v_a_1603_;
v___y_1897_ = v_a_1604_;
goto v___jp_1887_;
}
else
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Lean_Meta_Grind_updateLastTag(v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v___x_1993_; 
lean_dec_ref_known(v___x_1992_, 1);
lean_inc(v_a_1604_);
lean_inc_ref(v_a_1603_);
lean_inc(v_a_1602_);
lean_inc_ref(v_a_1601_);
lean_inc_ref(v_h_1594_);
v___x_1993_ = lean_infer_type(v_h_1594_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1993_, 1);
v___x_1995_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5);
v___x_1996_ = l_Lean_MessageData_ofExpr(v_a_1994_);
v___x_1997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1995_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
v___x_1998_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1989_, v___x_1997_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_dec_ref_known(v___x_1998_, 1);
v___y_1888_ = v_a_1595_;
v___y_1889_ = v_a_1596_;
v___y_1890_ = v_a_1597_;
v___y_1891_ = v_a_1598_;
v___y_1892_ = v_a_1599_;
v___y_1893_ = v_a_1600_;
v___y_1894_ = v_a_1601_;
v___y_1895_ = v_a_1602_;
v___y_1896_ = v_a_1603_;
v___y_1897_ = v_a_1604_;
goto v___jp_1887_;
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec_ref(v_h_1594_);
lean_dec_ref(v_e_1593_);
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1998_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_dec_ref(v_h_1594_);
lean_dec_ref(v_e_1593_);
v_a_2007_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_1993_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_1993_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec_ref(v_h_1594_);
lean_dec_ref(v_e_1593_);
v_a_2015_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_1992_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_1992_);
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
}
v___jp_1606_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = lean_box(0);
v___x_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
return v___x_1608_;
}
v___jp_1609_:
{
if (v___y_1611_ == 0)
{
lean_dec_ref(v_e_1593_);
if (v___y_1613_ == 0)
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_dec_ref(v_h_1615_);
lean_dec_ref(v___y_1614_);
lean_dec_ref(v___y_1612_);
v___x_1626_ = lean_box(0);
v___x_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
return v___x_1627_;
}
else
{
lean_object* v___x_1628_; 
lean_inc_ref(v___y_1612_);
v___x_1628_ = l_Lean_Meta_normLitValue(v___y_1612_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1630_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___x_1628_, 1);
lean_inc_ref(v___y_1614_);
v___x_1630_ = l_Lean_Meta_normLitValue(v___y_1614_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1670_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1633_ = v___x_1630_;
v_isShared_1634_ = v_isSharedCheck_1670_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1670_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
uint8_t v___x_1635_; 
v___x_1635_ = lean_expr_eqv(v_a_1629_, v_a_1631_);
lean_dec(v_a_1631_);
lean_dec(v_a_1629_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; 
lean_del_object(v___x_1633_);
v___x_1636_ = l_Lean_Meta_mkEq(v___y_1612_, v___y_1614_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
v___x_1638_ = l_Lean_mkNot(v_a_1637_);
v___x_1639_ = l_Lean_Meta_mkDecideProof(v___x_1638_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1649_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1649_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1649_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1644_ = l_Lean_Expr_app___override(v_a_1640_, v_h_1615_);
v___x_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1645_);
v___x_1647_ = v___x_1642_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec_ref(v_h_1615_);
v_a_1650_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1639_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1639_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec_ref(v_h_1615_);
v_a_1658_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1636_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1636_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1668_; 
lean_dec_ref(v_h_1615_);
lean_dec_ref(v___y_1614_);
lean_dec_ref(v___y_1612_);
v___x_1666_ = lean_box(0);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v___x_1666_);
v___x_1668_ = v___x_1633_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec(v_a_1629_);
lean_dec_ref(v_h_1615_);
lean_dec_ref(v___y_1614_);
lean_dec_ref(v___y_1612_);
v_a_1671_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1630_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1630_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec_ref(v_h_1615_);
lean_dec_ref(v___y_1614_);
lean_dec_ref(v___y_1612_);
v_a_1679_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1628_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1628_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
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
}
else
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Lean_Meta_isConstructorApp_x3f(v___y_1612_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1788_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1788_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1788_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
if (lean_obj_tag(v_a_1688_) == 1)
{
lean_object* v_val_1692_; lean_object* v___x_1693_; 
lean_del_object(v___x_1690_);
v_val_1692_ = lean_ctor_get(v_a_1688_, 0);
lean_inc(v_val_1692_);
lean_dec_ref_known(v_a_1688_, 1);
v___x_1693_ = l_Lean_Meta_isConstructorApp_x3f(v___y_1614_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1775_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1696_ = v___x_1693_;
v_isShared_1697_ = v_isSharedCheck_1775_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1775_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
if (lean_obj_tag(v_a_1694_) == 1)
{
lean_object* v_val_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1770_; 
lean_del_object(v___x_1696_);
v_val_1698_ = lean_ctor_get(v_a_1694_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v_a_1694_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1700_ = v_a_1694_;
v_isShared_1701_ = v_isSharedCheck_1770_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_val_1698_);
lean_dec(v_a_1694_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1770_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_1620_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v___x_1704_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1702_, 1);
v___x_1704_ = l_Lean_Meta_mkNoConfusion(v_a_1703_, v_h_1615_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_toConstantVal_1705_; lean_object* v_toConstantVal_1706_; lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1753_; 
v_toConstantVal_1705_ = lean_ctor_get(v_val_1692_, 0);
lean_inc_ref(v_toConstantVal_1705_);
lean_dec(v_val_1692_);
v_toConstantVal_1706_ = lean_ctor_get(v_val_1698_, 0);
lean_inc_ref(v_toConstantVal_1706_);
lean_dec(v_val_1698_);
v_a_1707_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1709_ = v___x_1704_;
v_isShared_1710_ = v_isSharedCheck_1753_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1704_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1753_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v_name_1711_; lean_object* v_name_1712_; uint8_t v___x_1713_; 
v_name_1711_ = lean_ctor_get(v_toConstantVal_1705_, 0);
lean_inc(v_name_1711_);
lean_dec_ref(v_toConstantVal_1705_);
v_name_1712_ = lean_ctor_get(v_toConstantVal_1706_, 0);
lean_inc(v_name_1712_);
lean_dec_ref(v_toConstantVal_1706_);
v___x_1713_ = lean_name_eq(v_name_1711_, v_name_1712_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1715_; 
lean_dec(v_name_1712_);
lean_dec(v_name_1711_);
lean_dec_ref(v_e_1593_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v_a_1707_);
v___x_1715_ = v___x_1700_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1707_);
v___x_1715_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1717_; 
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v___x_1715_);
v___x_1717_ = v___x_1709_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
else
{
lean_object* v___x_1720_; lean_object* v___f_1721_; uint8_t v___x_1722_; lean_object* v___x_1723_; 
lean_del_object(v___x_1709_);
lean_del_object(v___x_1700_);
v___x_1720_ = lean_box(v___y_1610_);
lean_inc(v_a_1707_);
v___f_1721_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed), 18, 5);
lean_closure_set(v___f_1721_, 0, v_e_1593_);
lean_closure_set(v___f_1721_, 1, v_name_1711_);
lean_closure_set(v___f_1721_, 2, v_name_1712_);
lean_closure_set(v___f_1721_, 3, v___x_1720_);
lean_closure_set(v___f_1721_, 4, v_a_1707_);
v___x_1722_ = 0;
lean_inc(v___y_1625_);
lean_inc_ref(v___y_1624_);
lean_inc(v___y_1623_);
lean_inc_ref(v___y_1622_);
v___x_1723_ = lean_infer_type(v_a_1707_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1725_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1723_, 1);
v___x_1725_ = l_Lean_Meta_whnfD(v_a_1724_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1736_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1728_ = v___x_1725_;
v_isShared_1729_ = v_isSharedCheck_1736_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1725_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1736_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
if (lean_obj_tag(v_a_1726_) == 7)
{
lean_object* v_binderType_1730_; lean_object* v___x_1731_; 
lean_del_object(v___x_1728_);
v_binderType_1730_ = lean_ctor_get(v_a_1726_, 1);
lean_inc_ref(v_binderType_1730_);
lean_dec_ref_known(v_a_1726_, 3);
v___x_1731_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_binderType_1730_, v___f_1721_, v___x_1722_, v___x_1722_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
return v___x_1731_;
}
else
{
lean_object* v___x_1732_; lean_object* v___x_1734_; 
lean_dec(v_a_1726_);
lean_dec_ref(v___f_1721_);
v___x_1732_ = lean_box(0);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1732_);
v___x_1734_ = v___x_1728_;
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
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_dec_ref(v___f_1721_);
v_a_1737_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1725_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1725_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_dec_ref(v___f_1721_);
v_a_1745_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1723_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1723_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
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
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_del_object(v___x_1700_);
lean_dec(v_val_1698_);
lean_dec(v_val_1692_);
lean_dec_ref(v_e_1593_);
v_a_1754_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1704_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1704_);
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
lean_del_object(v___x_1700_);
lean_dec(v_val_1698_);
lean_dec(v_val_1692_);
lean_dec_ref(v_h_1615_);
lean_dec_ref(v_e_1593_);
v_a_1762_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1702_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1702_);
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
else
{
lean_object* v___x_1771_; lean_object* v___x_1773_; 
lean_dec(v_a_1694_);
lean_dec(v_val_1692_);
lean_dec_ref(v_h_1615_);
lean_dec_ref(v_e_1593_);
v___x_1771_ = lean_box(0);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1771_);
v___x_1773_ = v___x_1696_;
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
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_dec(v_val_1692_);
lean_dec_ref(v_h_1615_);
lean_dec_ref(v_e_1593_);
v_a_1776_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1693_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1693_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1786_; 
lean_dec(v_a_1688_);
lean_dec_ref(v_h_1615_);
lean_dec_ref(v___y_1614_);
lean_dec_ref(v_e_1593_);
v___x_1784_ = lean_box(0);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v___x_1784_);
v___x_1786_ = v___x_1690_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
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
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec_ref(v_h_1615_);
lean_dec_ref(v___y_1614_);
lean_dec_ref(v_e_1593_);
v_a_1789_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1687_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1687_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
v___jp_1797_:
{
lean_object* v_self_1812_; uint8_t v_interpreted_1813_; uint8_t v_ctor_1814_; lean_object* v___x_1815_; 
v_self_1812_ = lean_ctor_get(v___y_1803_, 0);
lean_inc_ref_n(v_self_1812_, 2);
v_interpreted_1813_ = lean_ctor_get_uint8(v___y_1803_, sizeof(void*)*12 + 1);
v_ctor_1814_ = lean_ctor_get_uint8(v___y_1803_, sizeof(void*)*12 + 2);
lean_dec_ref(v___y_1803_);
lean_inc_ref(v___y_1800_);
v___x_1815_ = l_Lean_Meta_Grind_hasSameType(v_self_1812_, v___y_1800_, v___y_1806_, v___y_1808_, v___y_1804_, v___y_1809_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1878_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1878_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1878_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
uint8_t v___x_1820_; 
v___x_1820_ = lean_unbox(v_a_1816_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; lean_object* v___x_1823_; 
lean_dec(v_a_1816_);
lean_dec_ref(v_self_1812_);
lean_dec_ref(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec_ref(v_h_1594_);
lean_dec_ref(v_e_1593_);
v___x_1821_ = lean_box(0);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1821_);
v___x_1823_ = v___x_1818_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
else
{
lean_del_object(v___x_1818_);
if (v___y_1811_ == 0)
{
lean_object* v___x_1825_; 
lean_inc(v___y_1809_);
lean_inc_ref(v___y_1804_);
lean_inc(v___y_1808_);
lean_inc_ref(v___y_1806_);
lean_inc(v___y_1798_);
lean_inc_ref(v___y_1807_);
lean_inc(v___y_1802_);
lean_inc_ref(v___y_1805_);
lean_inc(v___y_1801_);
lean_inc(v___y_1810_);
lean_inc_ref(v_self_1812_);
v___x_1825_ = lean_grind_mk_eq_proof(v_self_1812_, v___y_1799_, v___y_1810_, v___y_1801_, v___y_1805_, v___y_1802_, v___y_1807_, v___y_1798_, v___y_1806_, v___y_1808_, v___y_1804_, v___y_1809_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1827_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1826_);
lean_dec_ref_known(v___x_1825_, 1);
v___x_1827_ = l_Lean_Meta_mkEqTrans(v_a_1826_, v_h_1594_, v___y_1806_, v___y_1808_, v___y_1804_, v___y_1809_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; uint8_t v___x_1829_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_a_1828_);
lean_dec_ref_known(v___x_1827_, 1);
v___x_1829_ = lean_unbox(v_a_1816_);
lean_dec(v_a_1816_);
v___y_1610_ = v___x_1829_;
v___y_1611_ = v_ctor_1814_;
v___y_1612_ = v_self_1812_;
v___y_1613_ = v_interpreted_1813_;
v___y_1614_ = v___y_1800_;
v_h_1615_ = v_a_1828_;
v___y_1616_ = v___y_1810_;
v___y_1617_ = v___y_1801_;
v___y_1618_ = v___y_1805_;
v___y_1619_ = v___y_1802_;
v___y_1620_ = v___y_1807_;
v___y_1621_ = v___y_1798_;
v___y_1622_ = v___y_1806_;
v___y_1623_ = v___y_1808_;
v___y_1624_ = v___y_1804_;
v___y_1625_ = v___y_1809_;
goto v___jp_1609_;
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_dec(v_a_1816_);
lean_dec_ref(v_self_1812_);
lean_dec_ref(v___y_1800_);
lean_dec_ref(v_e_1593_);
v_a_1830_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1827_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1827_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec(v_a_1816_);
lean_dec_ref(v_self_1812_);
lean_dec_ref(v___y_1800_);
lean_dec_ref(v_h_1594_);
lean_dec_ref(v_e_1593_);
v_a_1838_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1825_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1825_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
else
{
lean_object* v___x_1846_; 
lean_inc(v___y_1809_);
lean_inc_ref(v___y_1804_);
lean_inc(v___y_1808_);
lean_inc_ref(v___y_1806_);
lean_inc(v___y_1798_);
lean_inc_ref(v___y_1807_);
lean_inc(v___y_1802_);
lean_inc_ref(v___y_1805_);
lean_inc(v___y_1801_);
lean_inc(v___y_1810_);
lean_inc_ref(v_self_1812_);
v___x_1846_ = lean_grind_mk_heq_proof(v_self_1812_, v___y_1799_, v___y_1810_, v___y_1801_, v___y_1805_, v___y_1802_, v___y_1807_, v___y_1798_, v___y_1806_, v___y_1808_, v___y_1804_, v___y_1809_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1848_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v___x_1846_, 1);
v___x_1848_ = l_Lean_Meta_mkHEqTrans(v_a_1847_, v_h_1594_, v___y_1806_, v___y_1808_, v___y_1804_, v___y_1809_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; uint8_t v___x_1850_; lean_object* v___x_1851_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref_known(v___x_1848_, 1);
v___x_1850_ = 0;
v___x_1851_ = l_Lean_Meta_mkEqOfHEq(v_a_1849_, v___x_1850_, v___y_1806_, v___y_1808_, v___y_1804_, v___y_1809_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; uint8_t v___x_1853_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_a_1852_);
lean_dec_ref_known(v___x_1851_, 1);
v___x_1853_ = lean_unbox(v_a_1816_);
lean_dec(v_a_1816_);
v___y_1610_ = v___x_1853_;
v___y_1611_ = v_ctor_1814_;
v___y_1612_ = v_self_1812_;
v___y_1613_ = v_interpreted_1813_;
v___y_1614_ = v___y_1800_;
v_h_1615_ = v_a_1852_;
v___y_1616_ = v___y_1810_;
v___y_1617_ = v___y_1801_;
v___y_1618_ = v___y_1805_;
v___y_1619_ = v___y_1802_;
v___y_1620_ = v___y_1807_;
v___y_1621_ = v___y_1798_;
v___y_1622_ = v___y_1806_;
v___y_1623_ = v___y_1808_;
v___y_1624_ = v___y_1804_;
v___y_1625_ = v___y_1809_;
goto v___jp_1609_;
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec(v_a_1816_);
lean_dec_ref(v_self_1812_);
lean_dec_ref(v___y_1800_);
lean_dec_ref(v_e_1593_);
v_a_1854_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1851_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1851_);
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
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec(v_a_1816_);
lean_dec_ref(v_self_1812_);
lean_dec_ref(v___y_1800_);
lean_dec_ref(v_e_1593_);
v_a_1862_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1848_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1848_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec(v_a_1816_);
lean_dec_ref(v_self_1812_);
lean_dec_ref(v___y_1800_);
lean_dec_ref(v_h_1594_);
lean_dec_ref(v_e_1593_);
v_a_1870_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1846_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1846_);
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
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec_ref(v_self_1812_);
lean_dec_ref(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec_ref(v_h_1594_);
lean_dec_ref(v_e_1593_);
v_a_1879_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1815_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1815_);
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
v___jp_1887_:
{
lean_object* v___x_1898_; 
lean_inc(v___y_1897_);
lean_inc_ref(v___y_1896_);
lean_inc(v___y_1895_);
lean_inc_ref(v___y_1894_);
lean_inc_ref(v_h_1594_);
v___x_1898_ = lean_infer_type(v_h_1594_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1976_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_1976_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1976_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1903_; 
v___x_1903_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_a_1899_);
if (lean_obj_tag(v___x_1903_) == 1)
{
lean_object* v_val_1904_; lean_object* v_snd_1905_; lean_object* v_fst_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1971_; 
lean_del_object(v___x_1901_);
v_val_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_val_1904_);
lean_dec_ref_known(v___x_1903_, 1);
v_snd_1905_ = lean_ctor_get(v_val_1904_, 1);
v_fst_1906_ = lean_ctor_get(v_val_1904_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_val_1904_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1908_ = v_val_1904_;
v_isShared_1909_ = v_isSharedCheck_1971_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_snd_1905_);
lean_inc(v_fst_1906_);
lean_dec(v_val_1904_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1971_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v_fst_1910_; lean_object* v_snd_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1970_; 
v_fst_1910_ = lean_ctor_get(v_snd_1905_, 0);
v_snd_1911_ = lean_ctor_get(v_snd_1905_, 1);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_snd_1905_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1913_ = v_snd_1905_;
v_isShared_1914_ = v_isSharedCheck_1970_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_snd_1911_);
lean_inc(v_fst_1910_);
lean_dec(v_snd_1905_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1970_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_Meta_Sym_shareCommon(v_fst_1910_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1917_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1915_, 1);
v___x_1917_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_a_1916_, v___y_1888_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
if (lean_obj_tag(v_a_1918_) == 1)
{
lean_del_object(v___x_1913_);
lean_del_object(v___x_1908_);
if (lean_obj_tag(v_fst_1906_) == 0)
{
lean_object* v_val_1919_; uint8_t v___x_1920_; 
v_val_1919_ = lean_ctor_get(v_a_1918_, 0);
lean_inc(v_val_1919_);
lean_dec_ref_known(v_a_1918_, 1);
v___x_1920_ = 0;
v___y_1798_ = v___y_1893_;
v___y_1799_ = v_a_1916_;
v___y_1800_ = v_snd_1911_;
v___y_1801_ = v___y_1889_;
v___y_1802_ = v___y_1891_;
v___y_1803_ = v_val_1919_;
v___y_1804_ = v___y_1896_;
v___y_1805_ = v___y_1890_;
v___y_1806_ = v___y_1894_;
v___y_1807_ = v___y_1892_;
v___y_1808_ = v___y_1895_;
v___y_1809_ = v___y_1897_;
v___y_1810_ = v___y_1888_;
v___y_1811_ = v___x_1920_;
goto v___jp_1797_;
}
else
{
lean_object* v_val_1921_; uint8_t v___x_1922_; 
lean_dec_ref_known(v_fst_1906_, 1);
v_val_1921_ = lean_ctor_get(v_a_1918_, 0);
lean_inc(v_val_1921_);
lean_dec_ref_known(v_a_1918_, 1);
v___x_1922_ = 1;
v___y_1798_ = v___y_1893_;
v___y_1799_ = v_a_1916_;
v___y_1800_ = v_snd_1911_;
v___y_1801_ = v___y_1889_;
v___y_1802_ = v___y_1891_;
v___y_1803_ = v_val_1921_;
v___y_1804_ = v___y_1896_;
v___y_1805_ = v___y_1890_;
v___y_1806_ = v___y_1894_;
v___y_1807_ = v___y_1892_;
v___y_1808_ = v___y_1895_;
v___y_1809_ = v___y_1897_;
v___y_1810_ = v___y_1888_;
v___y_1811_ = v___x_1922_;
goto v___jp_1797_;
}
}
else
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1926_; 
lean_dec(v_a_1918_);
lean_dec(v_snd_1911_);
lean_dec(v_fst_1906_);
lean_dec_ref(v_h_1594_);
v___x_1923_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1);
v___x_1924_ = l_Lean_indentExpr(v_a_1916_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set_tag(v___x_1913_, 7);
lean_ctor_set(v___x_1913_, 1, v___x_1924_);
lean_ctor_set(v___x_1913_, 0, v___x_1923_);
v___x_1926_ = v___x_1913_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1927_; lean_object* v___x_1929_; 
v___x_1927_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3);
if (v_isShared_1909_ == 0)
{
lean_ctor_set_tag(v___x_1908_, 7);
lean_ctor_set(v___x_1908_, 1, v___x_1927_);
lean_ctor_set(v___x_1908_, 0, v___x_1926_);
v___x_1929_ = v___x_1908_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = l_Lean_indentExpr(v_e_1593_);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1892_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; uint8_t v_verbose_1934_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
v_verbose_1934_ = lean_ctor_get_uint8(v_a_1933_, 0);
lean_dec(v_a_1933_);
if (v_verbose_1934_ == 0)
{
lean_dec_ref_known(v___x_1931_, 2);
goto v___jp_1606_;
}
else
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Lean_Meta_Sym_reportIssue(v___x_1931_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_dec_ref_known(v___x_1935_, 1);
goto v___jp_1606_;
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
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
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec_ref_known(v___x_1931_, 2);
v_a_1944_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1932_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1932_);
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
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v_a_1916_);
lean_del_object(v___x_1913_);
lean_dec(v_snd_1911_);
lean_del_object(v___x_1908_);
lean_dec(v_fst_1906_);
lean_dec_ref(v_h_1594_);
lean_dec_ref(v_e_1593_);
v_a_1954_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1917_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1917_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_del_object(v___x_1913_);
lean_dec(v_snd_1911_);
lean_del_object(v___x_1908_);
lean_dec(v_fst_1906_);
lean_dec_ref(v_h_1594_);
lean_dec_ref(v_e_1593_);
v_a_1962_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1915_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1915_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1974_; 
lean_dec(v___x_1903_);
lean_dec_ref(v_h_1594_);
lean_dec_ref(v_e_1593_);
v___x_1972_ = lean_box(0);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v___x_1972_);
v___x_1974_ = v___x_1901_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1972_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
else
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
lean_dec_ref(v_h_1594_);
lean_dec_ref(v_e_1593_);
v_a_1977_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1898_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1898_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1593_ = stack[0].m_obj;
lean_object* v_h_1594_ = stack[1].m_obj;
lean_object* v_a_1595_ = stack[2].m_obj;
lean_object* v_a_1596_ = stack[3].m_obj;
lean_object* v_a_1597_ = stack[4].m_obj;
lean_object* v_a_1598_ = stack[5].m_obj;
lean_object* v_a_1599_ = stack[6].m_obj;
lean_object* v_a_1600_ = stack[7].m_obj;
lean_object* v_a_1601_ = stack[8].m_obj;
lean_object* v_a_1602_ = stack[9].m_obj;
lean_object* v_a_1603_ = stack[10].m_obj;
lean_object* v_a_1604_ = stack[11].m_obj;
lean_object* v_res_2023_;
v_res_2023_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_1593_, v_h_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
stack->m_obj
 = v_res_2023_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(lean_object* v_e_2024_, lean_object* v_xs_2025_, lean_object* v___x_2026_, lean_object* v___x_2027_, uint8_t v_a_2028_, lean_object* v_a_2029_, lean_object* v_as_2030_, size_t v_sz_2031_, size_t v_i_2032_, lean_object* v_b_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
uint8_t v___y_2046_; uint8_t v___x_2094_; 
v___x_2094_ = lean_name_eq(v___x_2026_, v___x_2027_);
if (v___x_2094_ == 0)
{
uint8_t v___x_2095_; 
v___x_2095_ = 1;
v___y_2046_ = v___x_2095_;
goto v___jp_2045_;
}
else
{
uint8_t v___x_2096_; 
v___x_2096_ = 0;
v___y_2046_ = v___x_2096_;
goto v___jp_2045_;
}
v___jp_2045_:
{
uint8_t v___x_2047_; 
v___x_2047_ = lean_usize_dec_lt(v_i_2032_, v_sz_2031_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; 
lean_dec_ref(v_a_2029_);
lean_dec_ref(v_e_2024_);
v___x_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2048_, 0, v_b_2033_);
return v___x_2048_;
}
else
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v_a_2051_; lean_object* v___x_2052_; 
lean_dec_ref(v_b_2033_);
v___x_2049_ = lean_box(0);
v___x_2050_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_a_2051_ = lean_array_uget_borrowed(v_as_2030_, v_i_2032_);
lean_inc(v_a_2051_);
lean_inc_ref(v_e_2024_);
v___x_2052_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2024_, v_a_2051_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref_known(v___x_2052_, 1);
if (lean_obj_tag(v_a_2053_) == 1)
{
lean_object* v_val_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2082_; 
lean_dec_ref(v_e_2024_);
v_val_2054_ = lean_ctor_get(v_a_2053_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_a_2053_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2056_ = v_a_2053_;
v_isShared_2057_ = v_isSharedCheck_2082_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_val_2054_);
lean_dec(v_a_2053_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2082_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
uint8_t v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = 1;
v___x_2059_ = l_Lean_Meta_mkLambdaFVars(v_xs_2025_, v_val_2054_, v___y_2046_, v_a_2028_, v___y_2046_, v_a_2028_, v___x_2058_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2073_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2073_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2073_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2064_ = l_Lean_Expr_app___override(v_a_2029_, v_a_2060_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 0, v___x_2064_);
v___x_2066_ = v___x_2056_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2070_; 
v___x_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
v___x_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
lean_ctor_set(v___x_2068_, 1, v___x_2049_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v___x_2068_);
v___x_2070_ = v___x_2062_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2068_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_del_object(v___x_2056_);
lean_dec_ref(v_a_2029_);
v_a_2074_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2059_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2059_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
}
else
{
size_t v___x_2083_; size_t v___x_2084_; 
lean_dec(v_a_2053_);
v___x_2083_ = ((size_t)1ULL);
v___x_2084_ = lean_usize_add(v_i_2032_, v___x_2083_);
v_i_2032_ = v___x_2084_;
v_b_2033_ = v___x_2050_;
goto _start;
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec_ref(v_a_2029_);
lean_dec_ref(v_e_2024_);
v_a_2086_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2052_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2052_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2024_ = stack[0].m_obj;
lean_object* v_xs_2025_ = stack[1].m_obj;
lean_object* v___x_2026_ = stack[2].m_obj;
lean_object* v___x_2027_ = stack[3].m_obj;
uint8_t v_a_2028_ = stack[4].m_num;
lean_object* v_a_2029_ = stack[5].m_obj;
lean_object* v_as_2030_ = stack[6].m_obj;
size_t v_sz_2031_ = stack[7].m_num;
size_t v_i_2032_ = stack[8].m_num;
lean_object* v_b_2033_ = stack[9].m_obj;
lean_object* v___y_2034_ = stack[10].m_obj;
lean_object* v___y_2035_ = stack[11].m_obj;
lean_object* v___y_2036_ = stack[12].m_obj;
lean_object* v___y_2037_ = stack[13].m_obj;
lean_object* v___y_2038_ = stack[14].m_obj;
lean_object* v___y_2039_ = stack[15].m_obj;
lean_object* v___y_2040_ = stack[16].m_obj;
lean_object* v___y_2041_ = stack[17].m_obj;
lean_object* v___y_2042_ = stack[18].m_obj;
lean_object* v___y_2043_ = stack[19].m_obj;
lean_object* v_res_2097_;
v_res_2097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_2024_, v_xs_2025_, v___x_2026_, v___x_2027_, v_a_2028_, v_a_2029_, v_as_2030_, v_sz_2031_, v_i_2032_, v_b_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
stack->m_obj
 = v_res_2097_;
}
lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(lean_object* v_e_2098_, lean_object* v_name_2099_, lean_object* v_name_2100_, uint8_t v_a_2101_, lean_object* v_a_2102_, lean_object* v_xs_2103_, lean_object* v_x_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; size_t v_sz_2118_; size_t v___x_2119_; lean_object* v___x_2120_; 
v___x_2116_ = lean_box(0);
v___x_2117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_sz_2118_ = lean_array_size(v_xs_2103_);
v___x_2119_ = ((size_t)0ULL);
v___x_2120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_2098_, v_xs_2103_, v_name_2099_, v_name_2100_, v_a_2101_, v_a_2102_, v_xs_2103_, v_sz_2118_, v___x_2119_, v___x_2117_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2133_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2133_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2133_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v_fst_2125_; 
v_fst_2125_ = lean_ctor_get(v_a_2121_, 0);
lean_inc(v_fst_2125_);
lean_dec(v_a_2121_);
if (lean_obj_tag(v_fst_2125_) == 0)
{
lean_object* v___x_2127_; 
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2116_);
v___x_2127_ = v___x_2123_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2116_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
else
{
lean_object* v_val_2129_; lean_object* v___x_2131_; 
v_val_2129_ = lean_ctor_get(v_fst_2125_, 0);
lean_inc(v_val_2129_);
lean_dec_ref_known(v_fst_2125_, 1);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v_val_2129_);
v___x_2131_ = v___x_2123_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_val_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
v_a_2134_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2120_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2120_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2098_ = stack[0].m_obj;
lean_object* v_name_2099_ = stack[1].m_obj;
lean_object* v_name_2100_ = stack[2].m_obj;
uint8_t v_a_2101_ = stack[3].m_num;
lean_object* v_a_2102_ = stack[4].m_obj;
lean_object* v_xs_2103_ = stack[5].m_obj;
lean_object* v_x_2104_ = stack[6].m_obj;
lean_object* v___y_2105_ = stack[7].m_obj;
lean_object* v___y_2106_ = stack[8].m_obj;
lean_object* v___y_2107_ = stack[9].m_obj;
lean_object* v___y_2108_ = stack[10].m_obj;
lean_object* v___y_2109_ = stack[11].m_obj;
lean_object* v___y_2110_ = stack[12].m_obj;
lean_object* v___y_2111_ = stack[13].m_obj;
lean_object* v___y_2112_ = stack[14].m_obj;
lean_object* v___y_2113_ = stack[15].m_obj;
lean_object* v___y_2114_ = stack[16].m_obj;
lean_object* v_res_2142_;
v_res_2142_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(v_e_2098_, v_name_2099_, v_name_2100_, v_a_2101_, v_a_2102_, v_xs_2103_, v_x_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
stack->m_obj
 = v_res_2142_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_e_2143_ = _args[0];
lean_object* v_xs_2144_ = _args[1];
lean_object* v___x_2145_ = _args[2];
lean_object* v___x_2146_ = _args[3];
lean_object* v_a_2147_ = _args[4];
lean_object* v_a_2148_ = _args[5];
lean_object* v_as_2149_ = _args[6];
lean_object* v_sz_2150_ = _args[7];
lean_object* v_i_2151_ = _args[8];
lean_object* v_b_2152_ = _args[9];
lean_object* v___y_2153_ = _args[10];
lean_object* v___y_2154_ = _args[11];
lean_object* v___y_2155_ = _args[12];
lean_object* v___y_2156_ = _args[13];
lean_object* v___y_2157_ = _args[14];
lean_object* v___y_2158_ = _args[15];
lean_object* v___y_2159_ = _args[16];
lean_object* v___y_2160_ = _args[17];
lean_object* v___y_2161_ = _args[18];
lean_object* v___y_2162_ = _args[19];
lean_object* v___y_2163_ = _args[20];
_start:
{
uint8_t v_a_80168__boxed_2164_; size_t v_sz_boxed_2165_; size_t v_i_boxed_2166_; lean_object* v_res_2167_; 
v_a_80168__boxed_2164_ = lean_unbox(v_a_2147_);
v_sz_boxed_2165_ = lean_unbox_usize(v_sz_2150_);
lean_dec(v_sz_2150_);
v_i_boxed_2166_ = lean_unbox_usize(v_i_2151_);
lean_dec(v_i_2151_);
v_res_2167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_2143_, v_xs_2144_, v___x_2145_, v___x_2146_, v_a_80168__boxed_2164_, v_a_2148_, v_as_2149_, v_sz_boxed_2165_, v_i_boxed_2166_, v_b_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v_as_2149_);
lean_dec(v___x_2146_);
lean_dec(v___x_2145_);
lean_dec_ref(v_xs_2144_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___boxed(lean_object* v_e_2168_, lean_object* v_h_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2168_, v_h_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
lean_dec(v_a_2179_);
lean_dec_ref(v_a_2178_);
lean_dec(v_a_2177_);
lean_dec_ref(v_a_2176_);
lean_dec(v_a_2175_);
lean_dec_ref(v_a_2174_);
lean_dec(v_a_2173_);
lean_dec_ref(v_a_2172_);
lean_dec(v_a_2171_);
lean_dec(v_a_2170_);
return v_res_2181_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__0));
v___x_2184_ = l_Lean_stringToMessageData(v___x_2183_);
return v___x_2184_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(lean_object* v_e_2185_, lean_object* v_xs_2186_, uint8_t v___x_2187_, lean_object* v_as_2188_, size_t v_sz_2189_, size_t v_i_2190_, lean_object* v_b_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_a_2204_; uint8_t v___x_2208_; 
v___x_2208_ = lean_usize_dec_lt(v_i_2190_, v_sz_2189_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; 
lean_dec_ref(v_e_2185_);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v_b_2191_);
return v___x_2209_;
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v_a_2212_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___x_2263_; 
lean_dec_ref(v_b_2191_);
v___x_2210_ = lean_box(0);
v___x_2211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_a_2212_ = lean_array_uget_borrowed(v_as_2188_, v_i_2190_);
lean_inc(v___y_2201_);
lean_inc_ref(v___y_2200_);
lean_inc(v___y_2199_);
lean_inc_ref(v___y_2198_);
lean_inc(v_a_2212_);
v___x_2263_ = lean_infer_type(v_a_2212_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v___x_2265_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc_n(v_a_2264_, 2);
lean_dec_ref_known(v___x_2263_, 1);
v___x_2265_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_a_2264_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; uint8_t v___x_2267_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref_known(v___x_2265_, 1);
v___x_2267_ = lean_unbox(v_a_2266_);
lean_dec(v_a_2266_);
if (v___x_2267_ == 0)
{
lean_dec(v_a_2264_);
v_a_2204_ = v___x_2211_;
goto v___jp_2203_;
}
else
{
lean_object* v_toCold_2268_; lean_object* v_options_2269_; uint8_t v_hasTrace_2270_; 
v_toCold_2268_ = lean_ctor_get(v___y_2200_, 0);
v_options_2269_ = lean_ctor_get(v_toCold_2268_, 2);
v_hasTrace_2270_ = lean_ctor_get_uint8(v_options_2269_, sizeof(void*)*1);
if (v_hasTrace_2270_ == 0)
{
lean_dec(v_a_2264_);
v___y_2214_ = v___y_2192_;
v___y_2215_ = v___y_2193_;
v___y_2216_ = v___y_2194_;
v___y_2217_ = v___y_2195_;
v___y_2218_ = v___y_2196_;
v___y_2219_ = v___y_2197_;
v___y_2220_ = v___y_2198_;
v___y_2221_ = v___y_2199_;
v___y_2222_ = v___y_2200_;
v___y_2223_ = v___y_2201_;
goto v___jp_2213_;
}
else
{
lean_object* v_inheritedTraceOptions_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v_inheritedTraceOptions_2271_ = lean_ctor_get(v_toCold_2268_, 11);
v___x_2272_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
v___x_2273_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_2274_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2271_, v_options_2269_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_dec(v_a_2264_);
v___y_2214_ = v___y_2192_;
v___y_2215_ = v___y_2193_;
v___y_2216_ = v___y_2194_;
v___y_2217_ = v___y_2195_;
v___y_2218_ = v___y_2196_;
v___y_2219_ = v___y_2197_;
v___y_2220_ = v___y_2198_;
v___y_2221_ = v___y_2199_;
v___y_2222_ = v___y_2200_;
v___y_2223_ = v___y_2201_;
goto v___jp_2213_;
}
else
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_Meta_Grind_updateLastTag(v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_dec_ref_known(v___x_2275_, 1);
v___x_2276_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1);
v___x_2277_ = l_Lean_MessageData_ofExpr(v_a_2264_);
v___x_2278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2276_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_2272_, v___x_2278_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_dec_ref_known(v___x_2279_, 1);
v___y_2214_ = v___y_2192_;
v___y_2215_ = v___y_2193_;
v___y_2216_ = v___y_2194_;
v___y_2217_ = v___y_2195_;
v___y_2218_ = v___y_2196_;
v___y_2219_ = v___y_2197_;
v___y_2220_ = v___y_2198_;
v___y_2221_ = v___y_2199_;
v___y_2222_ = v___y_2200_;
v___y_2223_ = v___y_2201_;
goto v___jp_2213_;
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec_ref(v_e_2185_);
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2279_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2279_);
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
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_dec(v_a_2264_);
lean_dec_ref(v_e_2185_);
v_a_2288_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2275_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2275_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec(v_a_2264_);
lean_dec_ref(v_e_2185_);
v_a_2296_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2265_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2265_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec_ref(v_e_2185_);
v_a_2304_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2263_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2263_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
v___jp_2213_:
{
lean_object* v___x_2224_; 
lean_inc(v_a_2212_);
lean_inc_ref(v_e_2185_);
v___x_2224_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2185_, v_a_2212_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref_known(v___x_2224_, 1);
if (lean_obj_tag(v_a_2225_) == 1)
{
lean_object* v_val_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2254_; 
lean_dec_ref(v_e_2185_);
v_val_2226_ = lean_ctor_get(v_a_2225_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v_a_2225_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2228_ = v_a_2225_;
v_isShared_2229_ = v_isSharedCheck_2254_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_val_2226_);
lean_dec(v_a_2225_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2254_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
uint8_t v___x_2230_; uint8_t v___x_2231_; lean_object* v___x_2232_; 
v___x_2230_ = 0;
v___x_2231_ = 1;
v___x_2232_ = l_Lean_Meta_mkLambdaFVars(v_xs_2186_, v_val_2226_, v___x_2230_, v___x_2187_, v___x_2230_, v___x_2187_, v___x_2231_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2245_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2235_ = v___x_2232_;
v_isShared_2236_ = v_isSharedCheck_2245_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2232_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2245_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 0, v_a_2233_);
v___x_2238_ = v___x_2228_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
v___x_2240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
lean_ctor_set(v___x_2240_, 1, v___x_2210_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 0, v___x_2240_);
v___x_2242_ = v___x_2235_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_del_object(v___x_2228_);
v_a_2246_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2232_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2232_);
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
else
{
lean_dec(v_a_2225_);
v_a_2204_ = v___x_2211_;
goto v___jp_2203_;
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec_ref(v_e_2185_);
v_a_2255_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2224_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2224_);
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
v___jp_2203_:
{
size_t v___x_2205_; size_t v___x_2206_; 
v___x_2205_ = ((size_t)1ULL);
v___x_2206_ = lean_usize_add(v_i_2190_, v___x_2205_);
lean_inc_ref(v_a_2204_);
v_i_2190_ = v___x_2206_;
v_b_2191_ = v_a_2204_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2185_ = stack[0].m_obj;
lean_object* v_xs_2186_ = stack[1].m_obj;
uint8_t v___x_2187_ = stack[2].m_num;
lean_object* v_as_2188_ = stack[3].m_obj;
size_t v_sz_2189_ = stack[4].m_num;
size_t v_i_2190_ = stack[5].m_num;
lean_object* v_b_2191_ = stack[6].m_obj;
lean_object* v___y_2192_ = stack[7].m_obj;
lean_object* v___y_2193_ = stack[8].m_obj;
lean_object* v___y_2194_ = stack[9].m_obj;
lean_object* v___y_2195_ = stack[10].m_obj;
lean_object* v___y_2196_ = stack[11].m_obj;
lean_object* v___y_2197_ = stack[12].m_obj;
lean_object* v___y_2198_ = stack[13].m_obj;
lean_object* v___y_2199_ = stack[14].m_obj;
lean_object* v___y_2200_ = stack[15].m_obj;
lean_object* v___y_2201_ = stack[16].m_obj;
lean_object* v_res_2312_;
v_res_2312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2185_, v_xs_2186_, v___x_2187_, v_as_2188_, v_sz_2189_, v_i_2190_, v_b_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
stack->m_obj
 = v_res_2312_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_e_2313_ = _args[0];
lean_object* v_xs_2314_ = _args[1];
lean_object* v___x_2315_ = _args[2];
lean_object* v_as_2316_ = _args[3];
lean_object* v_sz_2317_ = _args[4];
lean_object* v_i_2318_ = _args[5];
lean_object* v_b_2319_ = _args[6];
lean_object* v___y_2320_ = _args[7];
lean_object* v___y_2321_ = _args[8];
lean_object* v___y_2322_ = _args[9];
lean_object* v___y_2323_ = _args[10];
lean_object* v___y_2324_ = _args[11];
lean_object* v___y_2325_ = _args[12];
lean_object* v___y_2326_ = _args[13];
lean_object* v___y_2327_ = _args[14];
lean_object* v___y_2328_ = _args[15];
lean_object* v___y_2329_ = _args[16];
lean_object* v___y_2330_ = _args[17];
_start:
{
uint8_t v___x_21099__boxed_2331_; size_t v_sz_boxed_2332_; size_t v_i_boxed_2333_; lean_object* v_res_2334_; 
v___x_21099__boxed_2331_ = lean_unbox(v___x_2315_);
v_sz_boxed_2332_ = lean_unbox_usize(v_sz_2317_);
lean_dec(v_sz_2317_);
v_i_boxed_2333_ = lean_unbox_usize(v_i_2318_);
lean_dec(v_i_2318_);
v_res_2334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2313_, v_xs_2314_, v___x_21099__boxed_2331_, v_as_2316_, v_sz_boxed_2332_, v_i_boxed_2333_, v_b_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v_as_2316_);
lean_dec_ref(v_xs_2314_);
return v_res_2334_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(lean_object* v_e_2335_, uint8_t v___x_2336_, lean_object* v_xs_2337_, lean_object* v_x_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; size_t v_sz_2352_; size_t v___x_2353_; lean_object* v___x_2354_; 
v___x_2350_ = lean_box(0);
v___x_2351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_sz_2352_ = lean_array_size(v_xs_2337_);
v___x_2353_ = ((size_t)0ULL);
v___x_2354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2335_, v_xs_2337_, v___x_2336_, v_xs_2337_, v_sz_2352_, v___x_2353_, v___x_2351_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2367_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2357_ = v___x_2354_;
v_isShared_2358_ = v_isSharedCheck_2367_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2354_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2367_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v_fst_2359_; 
v_fst_2359_ = lean_ctor_get(v_a_2355_, 0);
lean_inc(v_fst_2359_);
lean_dec(v_a_2355_);
if (lean_obj_tag(v_fst_2359_) == 0)
{
lean_object* v___x_2361_; 
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v___x_2350_);
v___x_2361_ = v___x_2357_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2350_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
else
{
lean_object* v_val_2363_; lean_object* v___x_2365_; 
v_val_2363_ = lean_ctor_get(v_fst_2359_, 0);
lean_inc(v_val_2363_);
lean_dec_ref_known(v_fst_2359_, 1);
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v_val_2363_);
v___x_2365_ = v___x_2357_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_val_2363_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
v_a_2368_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2354_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2354_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2335_ = stack[0].m_obj;
uint8_t v___x_2336_ = stack[1].m_num;
lean_object* v_xs_2337_ = stack[2].m_obj;
lean_object* v_x_2338_ = stack[3].m_obj;
lean_object* v___y_2339_ = stack[4].m_obj;
lean_object* v___y_2340_ = stack[5].m_obj;
lean_object* v___y_2341_ = stack[6].m_obj;
lean_object* v___y_2342_ = stack[7].m_obj;
lean_object* v___y_2343_ = stack[8].m_obj;
lean_object* v___y_2344_ = stack[9].m_obj;
lean_object* v___y_2345_ = stack[10].m_obj;
lean_object* v___y_2346_ = stack[11].m_obj;
lean_object* v___y_2347_ = stack[12].m_obj;
lean_object* v___y_2348_ = stack[13].m_obj;
lean_object* v_res_2376_;
v_res_2376_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(v_e_2335_, v___x_2336_, v_xs_2337_, v_x_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
stack->m_obj
 = v_res_2376_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed(lean_object* v_e_2377_, lean_object* v___x_2378_, lean_object* v_xs_2379_, lean_object* v_x_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
uint8_t v___x_21482__boxed_2392_; lean_object* v_res_2393_; 
v___x_21482__boxed_2392_ = lean_unbox(v___x_2378_);
v_res_2393_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(v_e_2377_, v___x_21482__boxed_2392_, v_xs_2379_, v_x_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v_x_2380_);
lean_dec_ref(v_xs_2379_);
return v_res_2393_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(lean_object* v_e_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v___x_2409_; 
lean_inc_ref(v_e_2394_);
v___x_2409_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2394_, v_a_2402_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref_known(v___x_2409_, 1);
v___x_2411_ = l_Lean_Expr_cleanupAnnotations(v_a_2410_);
v___x_2412_ = l_Lean_Expr_isApp(v___x_2411_);
if (v___x_2412_ == 0)
{
lean_dec_ref(v___x_2411_);
lean_dec_ref(v_e_2394_);
goto v___jp_2406_;
}
else
{
lean_object* v_arg_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; uint8_t v___x_2416_; 
v_arg_2413_ = lean_ctor_get(v___x_2411_, 1);
lean_inc_ref(v_arg_2413_);
v___x_2414_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2411_);
v___x_2415_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_2416_ = l_Lean_Expr_isConstOf(v___x_2414_, v___x_2415_);
lean_dec_ref(v___x_2414_);
if (v___x_2416_ == 0)
{
lean_dec_ref(v_arg_2413_);
lean_dec_ref(v_e_2394_);
goto v___jp_2406_;
}
else
{
lean_object* v___x_2417_; lean_object* v___f_2418_; uint8_t v___x_2419_; lean_object* v___x_2420_; 
v___x_2417_ = lean_box(v___x_2416_);
v___f_2418_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed), 15, 2);
lean_closure_set(v___f_2418_, 0, v_e_2394_);
lean_closure_set(v___f_2418_, 1, v___x_2417_);
v___x_2419_ = 0;
v___x_2420_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_arg_2413_, v___f_2418_, v___x_2419_, v___x_2419_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
return v___x_2420_;
}
}
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
lean_dec_ref(v_e_2394_);
v_a_2421_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2409_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2409_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
v___jp_2406_:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = lean_box(0);
v___x_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
return v___x_2408_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2394_ = stack[0].m_obj;
lean_object* v_a_2395_ = stack[1].m_obj;
lean_object* v_a_2396_ = stack[2].m_obj;
lean_object* v_a_2397_ = stack[3].m_obj;
lean_object* v_a_2398_ = stack[4].m_obj;
lean_object* v_a_2399_ = stack[5].m_obj;
lean_object* v_a_2400_ = stack[6].m_obj;
lean_object* v_a_2401_ = stack[7].m_obj;
lean_object* v_a_2402_ = stack[8].m_obj;
lean_object* v_a_2403_ = stack[9].m_obj;
lean_object* v_a_2404_ = stack[10].m_obj;
lean_object* v_res_2429_;
v_res_2429_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
stack->m_obj
 = v_res_2429_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___boxed(lean_object* v_e_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec(v_a_2432_);
lean_dec(v_a_2431_);
return v_res_2442_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(lean_object* v_e_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v___x_2449_; uint8_t v___x_2450_; uint8_t v___x_2451_; 
v___x_2449_ = l_Lean_Expr_getAppFn(v_e_2443_);
v___x_2450_ = l_Lean_Expr_isMVar(v___x_2449_);
lean_dec_ref(v___x_2449_);
v___x_2451_ = 1;
if (v___x_2450_ == 0)
{
lean_object* v___x_2452_; 
lean_inc_ref(v_e_2443_);
v___x_2452_ = l_Lean_Meta_isConstructorApp_x3f(v_e_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2466_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2466_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2466_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
if (lean_obj_tag(v_a_2453_) == 0)
{
if (v___x_2450_ == 0)
{
lean_object* v___x_2457_; 
lean_del_object(v___x_2455_);
v___x_2457_ = l_Lean_Meta_isLitValue(v_e_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
return v___x_2457_;
}
else
{
lean_object* v___x_2458_; lean_object* v___x_2460_; 
lean_dec_ref(v_e_2443_);
v___x_2458_ = lean_box(v___x_2451_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___x_2458_);
v___x_2460_ = v___x_2455_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2458_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
else
{
lean_object* v___x_2462_; lean_object* v___x_2464_; 
lean_dec_ref_known(v_a_2453_, 1);
lean_dec_ref(v_e_2443_);
v___x_2462_ = lean_box(v___x_2451_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___x_2462_);
v___x_2464_ = v___x_2455_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec_ref(v_e_2443_);
v_a_2467_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2452_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2452_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
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
lean_object* v___x_2475_; lean_object* v___x_2476_; 
lean_dec_ref(v_e_2443_);
v___x_2475_ = lean_box(v___x_2451_);
v___x_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
return v___x_2476_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2443_ = stack[0].m_obj;
lean_object* v_a_2444_ = stack[1].m_obj;
lean_object* v_a_2445_ = stack[2].m_obj;
lean_object* v_a_2446_ = stack[3].m_obj;
lean_object* v_a_2447_ = stack[4].m_obj;
lean_object* v_res_2477_;
v_res_2477_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(v_e_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
stack->m_obj
 = v_res_2477_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg___boxed(lean_object* v_e_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(v_e_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
lean_dec(v_a_2480_);
lean_dec_ref(v_a_2479_);
return v_res_2484_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike(lean_object* v_e_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(v_e_2485_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
return v___x_2497_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2485_ = stack[0].m_obj;
lean_object* v_a_2486_ = stack[1].m_obj;
lean_object* v_a_2487_ = stack[2].m_obj;
lean_object* v_a_2488_ = stack[3].m_obj;
lean_object* v_a_2489_ = stack[4].m_obj;
lean_object* v_a_2490_ = stack[5].m_obj;
lean_object* v_a_2491_ = stack[6].m_obj;
lean_object* v_a_2492_ = stack[7].m_obj;
lean_object* v_a_2493_ = stack[8].m_obj;
lean_object* v_a_2494_ = stack[9].m_obj;
lean_object* v_a_2495_ = stack[10].m_obj;
lean_object* v_res_2498_;
v_res_2498_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike(v_e_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
stack->m_obj
 = v_res_2498_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___boxed(lean_object* v_e_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike(v_e_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
lean_dec(v_a_2509_);
lean_dec_ref(v_a_2508_);
lean_dec(v_a_2507_);
lean_dec_ref(v_a_2506_);
lean_dec(v_a_2505_);
lean_dec_ref(v_a_2504_);
lean_dec(v_a_2503_);
lean_dec_ref(v_a_2502_);
lean_dec(v_a_2501_);
lean_dec(v_a_2500_);
return v_res_2511_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(lean_object* v_e_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_){
_start:
{
lean_object* v___x_2524_; 
lean_inc_ref(v_e_2512_);
v___x_2524_ = l_Lean_Meta_Grind_getRootENode___redArg(v_e_2512_, v_a_2513_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2592_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2527_ = v___x_2524_;
v_isShared_2528_ = v_isSharedCheck_2592_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2524_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2592_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
uint8_t v_ctor_2529_; 
v_ctor_2529_ = lean_ctor_get_uint8(v_a_2525_, sizeof(void*)*12 + 2);
if (v_ctor_2529_ == 0)
{
uint8_t v_interpreted_2530_; 
v_interpreted_2530_ = lean_ctor_get_uint8(v_a_2525_, sizeof(void*)*12 + 1);
if (v_interpreted_2530_ == 0)
{
lean_object* v___x_2532_; 
lean_dec(v_a_2525_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v_e_2512_);
v___x_2532_ = v___x_2527_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_e_2512_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
else
{
lean_object* v_self_2534_; lean_object* v___x_2536_; 
lean_dec_ref(v_e_2512_);
v_self_2534_ = lean_ctor_get(v_a_2525_, 0);
lean_inc_ref(v_self_2534_);
lean_dec(v_a_2525_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v_self_2534_);
v___x_2536_ = v___x_2527_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_self_2534_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
else
{
lean_object* v_self_2538_; lean_object* v___x_2539_; 
lean_del_object(v___x_2527_);
lean_dec_ref(v_e_2512_);
v_self_2538_ = lean_ctor_get(v_a_2525_, 0);
lean_inc_ref_n(v_self_2538_, 2);
lean_dec(v_a_2525_);
v___x_2539_ = l_Lean_Meta_isConstructorApp_x3f(v_self_2538_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2583_; 
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2542_ = v___x_2539_;
v_isShared_2543_ = v_isSharedCheck_2583_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2539_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2583_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
if (lean_obj_tag(v_a_2540_) == 1)
{
lean_object* v_val_2544_; lean_object* v_numParams_2545_; lean_object* v_numFields_2546_; lean_object* v_nargs_2547_; lean_object* v___x_2548_; lean_object* v_dummy_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
lean_del_object(v___x_2542_);
v_val_2544_ = lean_ctor_get(v_a_2540_, 0);
lean_inc(v_val_2544_);
lean_dec_ref_known(v_a_2540_, 1);
v_numParams_2545_ = lean_ctor_get(v_val_2544_, 3);
lean_inc(v_numParams_2545_);
v_numFields_2546_ = lean_ctor_get(v_val_2544_, 4);
lean_inc(v_numFields_2546_);
lean_dec(v_val_2544_);
v_nargs_2547_ = l_Lean_Expr_getAppNumArgs(v_self_2538_);
v___x_2548_ = lean_nat_add(v_numParams_2545_, v_numFields_2546_);
lean_dec(v_numFields_2546_);
v_dummy_2549_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0);
lean_inc(v_nargs_2547_);
v___x_2550_ = lean_mk_array(v_nargs_2547_, v_dummy_2549_);
v___x_2551_ = lean_unsigned_to_nat(1u);
v___x_2552_ = lean_nat_sub(v_nargs_2547_, v___x_2551_);
lean_dec(v_nargs_2547_);
lean_inc_ref(v_self_2538_);
v___x_2553_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_2538_, v___x_2550_, v___x_2552_);
v___x_2554_ = 0;
v___x_2555_ = lean_box(v___x_2554_);
v___x_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2553_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v___x_2548_, v_ctor_2529_, v_numParams_2545_, v___x_2556_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_);
lean_dec(v___x_2548_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2571_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2560_ = v___x_2557_;
v_isShared_2561_ = v_isSharedCheck_2571_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2557_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2571_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v_snd_2562_; uint8_t v___x_2563_; 
v_snd_2562_ = lean_ctor_get(v_a_2558_, 1);
v___x_2563_ = lean_unbox(v_snd_2562_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2565_; 
lean_dec(v_a_2558_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v_self_2538_);
v___x_2565_ = v___x_2560_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_self_2538_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
else
{
lean_object* v_fst_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
lean_del_object(v___x_2560_);
v_fst_2567_ = lean_ctor_get(v_a_2558_, 0);
lean_inc(v_fst_2567_);
lean_dec(v_a_2558_);
v___x_2568_ = l_Lean_Expr_getAppFn(v_self_2538_);
lean_dec_ref(v_self_2538_);
v___x_2569_ = l_Lean_mkAppN(v___x_2568_, v_fst_2567_);
lean_dec(v_fst_2567_);
v___x_2570_ = l_Lean_Meta_Sym_shareCommon(v___x_2569_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_);
return v___x_2570_;
}
}
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec_ref(v_self_2538_);
v_a_2572_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2557_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2557_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
else
{
lean_object* v___x_2581_; 
lean_dec(v_a_2540_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 0, v_self_2538_);
v___x_2581_ = v___x_2542_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_self_2538_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
else
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
lean_dec_ref(v_self_2538_);
v_a_2584_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v___x_2539_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2539_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
}
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec_ref(v_e_2512_);
v_a_2593_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2524_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2524_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2512_ = stack[0].m_obj;
lean_object* v_a_2513_ = stack[1].m_obj;
lean_object* v_a_2514_ = stack[2].m_obj;
lean_object* v_a_2515_ = stack[3].m_obj;
lean_object* v_a_2516_ = stack[4].m_obj;
lean_object* v_a_2517_ = stack[5].m_obj;
lean_object* v_a_2518_ = stack[6].m_obj;
lean_object* v_a_2519_ = stack[7].m_obj;
lean_object* v_a_2520_ = stack[8].m_obj;
lean_object* v_a_2521_ = stack[9].m_obj;
lean_object* v_a_2522_ = stack[10].m_obj;
lean_object* v_res_2601_;
v_res_2601_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_e_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_);
stack->m_obj
 = v_res_2601_;
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(lean_object* v_upperBound_2602_, uint8_t v___x_2603_, lean_object* v_a_2604_, lean_object* v_b_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v_a_2618_; uint8_t v___x_2622_; 
v___x_2622_ = lean_nat_dec_lt(v_a_2604_, v_upperBound_2602_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; 
lean_dec(v_a_2604_);
v___x_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2623_, 0, v_b_2605_);
return v___x_2623_;
}
else
{
lean_object* v_fst_2624_; lean_object* v_snd_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2652_; 
v_fst_2624_ = lean_ctor_get(v_b_2605_, 0);
v_snd_2625_ = lean_ctor_get(v_b_2605_, 1);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_b_2605_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2627_ = v_b_2605_;
v_isShared_2628_ = v_isSharedCheck_2652_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_snd_2625_);
lean_inc(v_fst_2624_);
lean_dec(v_b_2605_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2652_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = l_Lean_instInhabitedExpr;
v___x_2630_ = lean_array_get_borrowed(v___x_2629_, v_fst_2624_, v_a_2604_);
lean_inc(v___x_2630_);
v___x_2631_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v___x_2630_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; size_t v___x_2633_; size_t v___x_2634_; uint8_t v___x_2635_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_a_2632_);
lean_dec_ref_known(v___x_2631_, 1);
v___x_2633_ = lean_ptr_addr(v___x_2630_);
v___x_2634_ = lean_ptr_addr(v_a_2632_);
v___x_2635_ = lean_usize_dec_eq(v___x_2633_, v___x_2634_);
if (v___x_2635_ == 0)
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2639_; 
lean_dec(v_snd_2625_);
v___x_2636_ = lean_array_set(v_fst_2624_, v_a_2604_, v_a_2632_);
v___x_2637_ = lean_box(v___x_2603_);
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 1, v___x_2637_);
lean_ctor_set(v___x_2627_, 0, v___x_2636_);
v___x_2639_ = v___x_2627_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2636_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v___x_2637_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
v_a_2618_ = v___x_2639_;
goto v___jp_2617_;
}
}
else
{
lean_object* v___x_2642_; 
lean_dec(v_a_2632_);
if (v_isShared_2628_ == 0)
{
v___x_2642_ = v___x_2627_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_fst_2624_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v_snd_2625_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
v_a_2618_ = v___x_2642_;
goto v___jp_2617_;
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_del_object(v___x_2627_);
lean_dec(v_snd_2625_);
lean_dec(v_fst_2624_);
lean_dec(v_a_2604_);
v_a_2644_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2631_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2631_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
v___jp_2617_:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2619_ = lean_unsigned_to_nat(1u);
v___x_2620_ = lean_nat_add(v_a_2604_, v___x_2619_);
lean_dec(v_a_2604_);
v_a_2604_ = v___x_2620_;
v_b_2605_ = v_a_2618_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2602_ = stack[0].m_obj;
uint8_t v___x_2603_ = stack[1].m_num;
lean_object* v_a_2604_ = stack[2].m_obj;
lean_object* v_b_2605_ = stack[3].m_obj;
lean_object* v___y_2606_ = stack[4].m_obj;
lean_object* v___y_2607_ = stack[5].m_obj;
lean_object* v___y_2608_ = stack[6].m_obj;
lean_object* v___y_2609_ = stack[7].m_obj;
lean_object* v___y_2610_ = stack[8].m_obj;
lean_object* v___y_2611_ = stack[9].m_obj;
lean_object* v___y_2612_ = stack[10].m_obj;
lean_object* v___y_2613_ = stack[11].m_obj;
lean_object* v___y_2614_ = stack[12].m_obj;
lean_object* v___y_2615_ = stack[13].m_obj;
lean_object* v_res_2653_;
v_res_2653_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2602_, v___x_2603_, v_a_2604_, v_b_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
stack->m_obj
 = v_res_2653_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg___boxed(lean_object* v_upperBound_2654_, lean_object* v___x_2655_, lean_object* v_a_2656_, lean_object* v_b_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
uint8_t v___x_13705__boxed_2669_; lean_object* v_res_2670_; 
v___x_13705__boxed_2669_ = lean_unbox(v___x_2655_);
v_res_2670_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2654_, v___x_13705__boxed_2669_, v_a_2656_, v_b_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec(v_upperBound_2654_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go___boxed(lean_object* v_e_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_e_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
lean_dec(v_a_2673_);
lean_dec(v_a_2672_);
return v_res_2683_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(lean_object* v_upperBound_2684_, uint8_t v___x_2685_, lean_object* v_inst_2686_, lean_object* v_R_2687_, lean_object* v_a_2688_, lean_object* v_b_2689_, lean_object* v_c_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2684_, v___x_2685_, v_a_2688_, v_b_2689_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
return v___x_2702_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2684_ = stack[0].m_obj;
uint8_t v___x_2685_ = stack[1].m_num;
lean_object* v_a_2688_ = stack[4].m_obj;
lean_object* v_b_2689_ = stack[5].m_obj;
lean_object* v___y_2691_ = stack[7].m_obj;
lean_object* v___y_2692_ = stack[8].m_obj;
lean_object* v___y_2693_ = stack[9].m_obj;
lean_object* v___y_2694_ = stack[10].m_obj;
lean_object* v___y_2695_ = stack[11].m_obj;
lean_object* v___y_2696_ = stack[12].m_obj;
lean_object* v___y_2697_ = stack[13].m_obj;
lean_object* v___y_2698_ = stack[14].m_obj;
lean_object* v___y_2699_ = stack[15].m_obj;
lean_object* v___y_2700_ = stack[16].m_obj;
lean_object* v_res_2703_;
v_res_2703_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(v_upperBound_2684_, v___x_2685_, lean_box(0), lean_box(0), v_a_2688_, v_b_2689_, lean_box(0), v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
stack->m_obj
 = v_res_2703_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_2704_ = _args[0];
lean_object* v___x_2705_ = _args[1];
lean_object* v_inst_2706_ = _args[2];
lean_object* v_R_2707_ = _args[3];
lean_object* v_a_2708_ = _args[4];
lean_object* v_b_2709_ = _args[5];
lean_object* v_c_2710_ = _args[6];
lean_object* v___y_2711_ = _args[7];
lean_object* v___y_2712_ = _args[8];
lean_object* v___y_2713_ = _args[9];
lean_object* v___y_2714_ = _args[10];
lean_object* v___y_2715_ = _args[11];
lean_object* v___y_2716_ = _args[12];
lean_object* v___y_2717_ = _args[13];
lean_object* v___y_2718_ = _args[14];
lean_object* v___y_2719_ = _args[15];
lean_object* v___y_2720_ = _args[16];
lean_object* v___y_2721_ = _args[17];
_start:
{
uint8_t v___x_14079__boxed_2722_; lean_object* v_res_2723_; 
v___x_14079__boxed_2722_ = lean_unbox(v___x_2705_);
v_res_2723_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(v_upperBound_2704_, v___x_14079__boxed_2722_, v_inst_2706_, v_R_2707_, v_a_2708_, v_b_2709_, v_c_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec(v_upperBound_2704_);
return v_res_2723_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(lean_object* v_e_2724_, lean_object* v___y_2725_){
_start:
{
uint8_t v___x_2727_; 
v___x_2727_ = l_Lean_Expr_hasMVar(v_e_2724_);
if (v___x_2727_ == 0)
{
lean_object* v___x_2728_; 
v___x_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2728_, 0, v_e_2724_);
return v___x_2728_;
}
else
{
lean_object* v___x_2729_; lean_object* v_mctx_2730_; lean_object* v___x_2731_; lean_object* v_fst_2732_; lean_object* v_snd_2733_; lean_object* v___x_2734_; lean_object* v_cache_2735_; lean_object* v_zetaDeltaFVarIds_2736_; lean_object* v_postponed_2737_; lean_object* v_diag_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2747_; 
v___x_2729_ = lean_st_ref_get(v___y_2725_);
v_mctx_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc_ref(v_mctx_2730_);
lean_dec(v___x_2729_);
v___x_2731_ = l_Lean_instantiateMVarsCore(v_mctx_2730_, v_e_2724_);
v_fst_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_fst_2732_);
v_snd_2733_ = lean_ctor_get(v___x_2731_, 1);
lean_inc(v_snd_2733_);
lean_dec_ref(v___x_2731_);
v___x_2734_ = lean_st_ref_take(v___y_2725_);
v_cache_2735_ = lean_ctor_get(v___x_2734_, 1);
v_zetaDeltaFVarIds_2736_ = lean_ctor_get(v___x_2734_, 2);
v_postponed_2737_ = lean_ctor_get(v___x_2734_, 3);
v_diag_2738_ = lean_ctor_get(v___x_2734_, 4);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2747_ == 0)
{
lean_object* v_unused_2748_; 
v_unused_2748_ = lean_ctor_get(v___x_2734_, 0);
lean_dec(v_unused_2748_);
v___x_2740_ = v___x_2734_;
v_isShared_2741_ = v_isSharedCheck_2747_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_diag_2738_);
lean_inc(v_postponed_2737_);
lean_inc(v_zetaDeltaFVarIds_2736_);
lean_inc(v_cache_2735_);
lean_dec(v___x_2734_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2747_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 0, v_snd_2733_);
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_snd_2733_);
lean_ctor_set(v_reuseFailAlloc_2746_, 1, v_cache_2735_);
lean_ctor_set(v_reuseFailAlloc_2746_, 2, v_zetaDeltaFVarIds_2736_);
lean_ctor_set(v_reuseFailAlloc_2746_, 3, v_postponed_2737_);
lean_ctor_set(v_reuseFailAlloc_2746_, 4, v_diag_2738_);
v___x_2743_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2744_ = lean_st_ref_put(v___y_2725_, v___x_2743_);
v___x_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2745_, 0, v_fst_2732_);
return v___x_2745_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2724_ = stack[0].m_obj;
lean_object* v___y_2725_ = stack[1].m_obj;
lean_object* v_res_2749_;
v_res_2749_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v_e_2724_, v___y_2725_);
stack->m_obj
 = v_res_2749_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg___boxed(lean_object* v_e_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v_e_2750_, v___y_2751_);
lean_dec(v___y_2751_);
return v_res_2753_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(lean_object* v_e_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v_e_2754_, v___y_2762_);
return v___x_2766_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2754_ = stack[0].m_obj;
lean_object* v___y_2755_ = stack[1].m_obj;
lean_object* v___y_2756_ = stack[2].m_obj;
lean_object* v___y_2757_ = stack[3].m_obj;
lean_object* v___y_2758_ = stack[4].m_obj;
lean_object* v___y_2759_ = stack[5].m_obj;
lean_object* v___y_2760_ = stack[6].m_obj;
lean_object* v___y_2761_ = stack[7].m_obj;
lean_object* v___y_2762_ = stack[8].m_obj;
lean_object* v___y_2763_ = stack[9].m_obj;
lean_object* v___y_2764_ = stack[10].m_obj;
lean_object* v_res_2767_;
v_res_2767_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(v_e_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
stack->m_obj
 = v_res_2767_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___boxed(lean_object* v_e_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(v_e_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec(v___y_2769_);
return v_res_2780_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0(lean_object* v_k_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v___x_2793_; 
lean_inc(v___y_2787_);
lean_inc_ref(v___y_2786_);
lean_inc(v___y_2785_);
lean_inc_ref(v___y_2784_);
lean_inc(v___y_2783_);
lean_inc(v___y_2782_);
v___x_2793_ = lean_apply_11(v_k_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, lean_box(0));
return v___x_2793_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2781_ = stack[0].m_obj;
lean_object* v___y_2782_ = stack[1].m_obj;
lean_object* v___y_2783_ = stack[2].m_obj;
lean_object* v___y_2784_ = stack[3].m_obj;
lean_object* v___y_2785_ = stack[4].m_obj;
lean_object* v___y_2786_ = stack[5].m_obj;
lean_object* v___y_2787_ = stack[6].m_obj;
lean_object* v___y_2788_ = stack[7].m_obj;
lean_object* v___y_2789_ = stack[8].m_obj;
lean_object* v___y_2790_ = stack[9].m_obj;
lean_object* v___y_2791_ = stack[10].m_obj;
lean_object* v_res_2794_;
v_res_2794_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0(v_k_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
stack->m_obj
 = v_res_2794_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0___boxed(lean_object* v_k_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0(v_k_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec(v___y_2796_);
return v_res_2807_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(lean_object* v_k_2808_, uint8_t v_allowLevelAssignments_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v___f_2821_; lean_object* v___x_2822_; 
lean_inc(v___y_2815_);
lean_inc_ref(v___y_2814_);
lean_inc(v___y_2813_);
lean_inc_ref(v___y_2812_);
lean_inc(v___y_2811_);
lean_inc(v___y_2810_);
v___f_2821_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_2821_, 0, v_k_2808_);
lean_closure_set(v___f_2821_, 1, v___y_2810_);
lean_closure_set(v___f_2821_, 2, v___y_2811_);
lean_closure_set(v___f_2821_, 3, v___y_2812_);
lean_closure_set(v___f_2821_, 4, v___y_2813_);
lean_closure_set(v___f_2821_, 5, v___y_2814_);
lean_closure_set(v___f_2821_, 6, v___y_2815_);
v___x_2822_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2809_, v___f_2821_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2822_) == 0)
{
return v___x_2822_;
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2822_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2822_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2808_ = stack[0].m_obj;
uint8_t v_allowLevelAssignments_2809_ = stack[1].m_num;
lean_object* v___y_2810_ = stack[2].m_obj;
lean_object* v___y_2811_ = stack[3].m_obj;
lean_object* v___y_2812_ = stack[4].m_obj;
lean_object* v___y_2813_ = stack[5].m_obj;
lean_object* v___y_2814_ = stack[6].m_obj;
lean_object* v___y_2815_ = stack[7].m_obj;
lean_object* v___y_2816_ = stack[8].m_obj;
lean_object* v___y_2817_ = stack[9].m_obj;
lean_object* v___y_2818_ = stack[10].m_obj;
lean_object* v___y_2819_ = stack[11].m_obj;
lean_object* v_res_2831_;
v_res_2831_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(v_k_2808_, v_allowLevelAssignments_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
stack->m_obj
 = v_res_2831_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___boxed(lean_object* v_k_2832_, lean_object* v_allowLevelAssignments_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2845_; lean_object* v_res_2846_; 
v_allowLevelAssignments_boxed_2845_ = lean_unbox(v_allowLevelAssignments_2833_);
v_res_2846_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(v_k_2832_, v_allowLevelAssignments_boxed_2845_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
return v_res_2846_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(lean_object* v_00_u03b1_2847_, lean_object* v_k_2848_, uint8_t v_allowLevelAssignments_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(v_k_2848_, v_allowLevelAssignments_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
return v___x_2861_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2848_ = stack[1].m_obj;
uint8_t v_allowLevelAssignments_2849_ = stack[2].m_num;
lean_object* v___y_2850_ = stack[3].m_obj;
lean_object* v___y_2851_ = stack[4].m_obj;
lean_object* v___y_2852_ = stack[5].m_obj;
lean_object* v___y_2853_ = stack[6].m_obj;
lean_object* v___y_2854_ = stack[7].m_obj;
lean_object* v___y_2855_ = stack[8].m_obj;
lean_object* v___y_2856_ = stack[9].m_obj;
lean_object* v___y_2857_ = stack[10].m_obj;
lean_object* v___y_2858_ = stack[11].m_obj;
lean_object* v___y_2859_ = stack[12].m_obj;
lean_object* v_res_2862_;
v_res_2862_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(lean_box(0), v_k_2848_, v_allowLevelAssignments_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
stack->m_obj
 = v_res_2862_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___boxed(lean_object* v_00_u03b1_2863_, lean_object* v_k_2864_, lean_object* v_allowLevelAssignments_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2877_; lean_object* v_res_2878_; 
v_allowLevelAssignments_boxed_2877_ = lean_unbox(v_allowLevelAssignments_2865_);
v_res_2878_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_00_u03b1_2863_, v_k_2864_, v_allowLevelAssignments_boxed_2877_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec(v___y_2866_);
return v_res_2878_;
}
}
lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0(lean_object* v_cls_2879_, lean_object* v_____do__lift_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v_toCold_2892_; lean_object* v_options_2893_; uint8_t v_hasTrace_2894_; 
v_toCold_2892_ = lean_ctor_get(v___y_2889_, 0);
v_options_2893_ = lean_ctor_get(v_toCold_2892_, 2);
v_hasTrace_2894_ = lean_ctor_get_uint8(v_options_2893_, sizeof(void*)*1);
if (v_hasTrace_2894_ == 0)
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
lean_dec(v_cls_2879_);
v___x_2895_ = lean_box(v_hasTrace_2894_);
v___x_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
return v___x_2896_;
}
else
{
lean_object* v___x_2897_; lean_object* v___x_2898_; uint8_t v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2897_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5));
v___x_2898_ = l_Lean_Name_append(v___x_2897_, v_cls_2879_);
v___x_2899_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2880_, v_options_2893_, v___x_2898_);
lean_dec(v___x_2898_);
v___x_2900_ = lean_box(v___x_2899_);
v___x_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
return v___x_2901_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_tryToProveFalse___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2879_ = stack[0].m_obj;
lean_object* v_____do__lift_2880_ = stack[1].m_obj;
lean_object* v___y_2881_ = stack[2].m_obj;
lean_object* v___y_2882_ = stack[3].m_obj;
lean_object* v___y_2883_ = stack[4].m_obj;
lean_object* v___y_2884_ = stack[5].m_obj;
lean_object* v___y_2885_ = stack[6].m_obj;
lean_object* v___y_2886_ = stack[7].m_obj;
lean_object* v___y_2887_ = stack[8].m_obj;
lean_object* v___y_2888_ = stack[9].m_obj;
lean_object* v___y_2889_ = stack[10].m_obj;
lean_object* v___y_2890_ = stack[11].m_obj;
lean_object* v_res_2902_;
v_res_2902_ = l_Lean_Meta_Grind_tryToProveFalse___lam__0(v_cls_2879_, v_____do__lift_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
stack->m_obj
 = v_res_2902_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed(lean_object* v_cls_2903_, lean_object* v_____do__lift_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Lean_Meta_Grind_tryToProveFalse___lam__0(v_cls_2903_, v_____do__lift_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v_____do__lift_2904_);
return v_res_2916_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3(void){
_start:
{
lean_object* v_cls_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v_cls_2925_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1));
v___x_2926_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5));
v___x_2927_ = l_Lean_Name_append(v___x_2926_, v_cls_2925_);
return v___x_2927_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5(void){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__4));
v___x_2930_ = l_Lean_stringToMessageData(v___x_2929_);
return v___x_2930_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(lean_object* v_as_2931_, size_t v_sz_2932_, size_t v_i_2933_, lean_object* v_b_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v_a_2947_; uint8_t v___x_2951_; 
v___x_2951_ = lean_usize_dec_lt(v_i_2933_, v_sz_2932_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; 
v___x_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2952_, 0, v_b_2934_);
return v___x_2952_;
}
else
{
lean_object* v_snd_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_3209_; 
v_snd_2953_ = lean_ctor_get(v_b_2934_, 1);
v_isSharedCheck_3209_ = !lean_is_exclusive(v_b_2934_);
if (v_isSharedCheck_3209_ == 0)
{
lean_object* v_unused_3210_; 
v_unused_3210_ = lean_ctor_get(v_b_2934_, 0);
lean_dec(v_unused_3210_);
v___x_2955_ = v_b_2934_;
v_isShared_2956_ = v_isSharedCheck_3209_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_snd_2953_);
lean_dec(v_b_2934_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_3209_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v_array_2957_; lean_object* v_start_2958_; lean_object* v_stop_2959_; lean_object* v___x_2960_; uint8_t v___x_2961_; 
v_array_2957_ = lean_ctor_get(v_snd_2953_, 0);
v_start_2958_ = lean_ctor_get(v_snd_2953_, 1);
v_stop_2959_ = lean_ctor_get(v_snd_2953_, 2);
v___x_2960_ = lean_box(0);
v___x_2961_ = lean_nat_dec_lt(v_start_2958_, v_stop_2959_);
if (v___x_2961_ == 0)
{
lean_object* v___x_2963_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 0, v___x_2960_);
v___x_2963_ = v___x_2955_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2960_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_snd_2953_);
v___x_2963_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2964_; 
v___x_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
return v___x_2964_;
}
}
else
{
lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_3205_; 
lean_inc(v_stop_2959_);
lean_inc(v_start_2958_);
lean_inc_ref(v_array_2957_);
v_isSharedCheck_3205_ = !lean_is_exclusive(v_snd_2953_);
if (v_isSharedCheck_3205_ == 0)
{
lean_object* v_unused_3206_; lean_object* v_unused_3207_; lean_object* v_unused_3208_; 
v_unused_3206_ = lean_ctor_get(v_snd_2953_, 2);
lean_dec(v_unused_3206_);
v_unused_3207_ = lean_ctor_get(v_snd_2953_, 1);
lean_dec(v_unused_3207_);
v_unused_3208_ = lean_ctor_get(v_snd_2953_, 0);
lean_dec(v_unused_3208_);
v___x_2967_ = v_snd_2953_;
v_isShared_2968_ = v_isSharedCheck_3205_;
goto v_resetjp_2966_;
}
else
{
lean_dec(v_snd_2953_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_3205_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2969_ = lean_array_fget(v_array_2957_, v_start_2958_);
v___x_2970_ = lean_unsigned_to_nat(1u);
v___x_2971_ = lean_nat_add(v_start_2958_, v___x_2970_);
lean_dec(v_start_2958_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 1, v___x_2971_);
v___x_2973_ = v___x_2967_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_array_2957_);
lean_ctor_set(v_reuseFailAlloc_3204_, 1, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_3204_, 2, v_stop_2959_);
v___x_2973_ = v_reuseFailAlloc_3204_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
uint8_t v___x_2974_; 
v___x_2974_ = lean_unbox(v___x_2969_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2976_; 
lean_dec(v___x_2969_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v___x_2973_);
lean_ctor_set(v___x_2955_, 0, v___x_2960_);
v___x_2976_ = v___x_2955_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2960_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v___x_2973_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
v_a_2947_ = v___x_2976_;
goto v___jp_2946_;
}
}
else
{
lean_object* v_cls_2978_; lean_object* v_a_2979_; lean_object* v_____x_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___x_3017_; 
v_cls_2978_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1));
v_a_2979_ = lean_array_uget_borrowed(v_as_2931_, v_i_2933_);
lean_inc(v___y_2944_);
lean_inc_ref(v___y_2943_);
lean_inc(v___y_2942_);
lean_inc_ref(v___y_2941_);
lean_inc(v_a_2979_);
v___x_3017_ = lean_infer_type(v_a_2979_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3195_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3020_ = v___x_3017_;
v_isShared_3021_ = v_isSharedCheck_3195_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3017_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3195_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3022_; 
v___x_3022_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_a_3018_);
if (lean_obj_tag(v___x_3022_) == 1)
{
lean_object* v_val_3023_; lean_object* v_snd_3024_; lean_object* v_fst_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3189_; 
lean_del_object(v___x_3020_);
v_val_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_val_3023_);
lean_dec_ref_known(v___x_3022_, 1);
v_snd_3024_ = lean_ctor_get(v_val_3023_, 1);
v_fst_3025_ = lean_ctor_get(v_val_3023_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v_val_3023_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3027_ = v_val_3023_;
v_isShared_3028_ = v_isSharedCheck_3189_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_snd_3024_);
lean_inc(v_fst_3025_);
lean_dec(v_val_3023_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3189_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v_fst_3029_; lean_object* v_snd_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3188_; 
v_fst_3029_ = lean_ctor_get(v_snd_3024_, 0);
v_snd_3030_ = lean_ctor_get(v_snd_3024_, 1);
v_isSharedCheck_3188_ = !lean_is_exclusive(v_snd_3024_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3032_ = v_snd_3024_;
v_isShared_3033_ = v_isSharedCheck_3188_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_snd_3030_);
lean_inc(v_fst_3029_);
lean_dec(v_snd_3024_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3188_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
uint8_t v___y_3035_; lean_object* v_lhs_x27_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3068_; uint8_t v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3126_; uint8_t v___y_3127_; uint8_t v___y_3162_; 
if (lean_obj_tag(v_fst_3025_) == 0)
{
uint8_t v___x_3186_; 
v___x_3186_ = 0;
v___y_3162_ = v___x_3186_;
goto v___jp_3161_;
}
else
{
uint8_t v___x_3187_; 
lean_dec_ref_known(v_fst_3025_, 1);
v___x_3187_ = lean_unbox(v___x_2969_);
v___y_3162_ = v___x_3187_;
goto v___jp_3161_;
}
v___jp_3034_:
{
if (v___y_3035_ == 0)
{
lean_object* v___x_3047_; 
v___x_3047_ = l_Lean_Meta_Grind_proveEq_x3f(v_fst_3029_, v_lhs_x27_3036_, v___y_3035_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref_known(v___x_3047_, 1);
v_____x_2981_ = v_a_3048_;
v___y_2982_ = v___y_3043_;
v___y_2983_ = v___y_3044_;
v___y_2984_ = v___y_3045_;
v___y_2985_ = v___y_3046_;
goto v___jp_2980_;
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_dec_ref(v___x_2973_);
lean_del_object(v___x_2955_);
v_a_3049_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_3047_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3047_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
else
{
lean_object* v___x_3057_; 
v___x_3057_ = l_Lean_Meta_Grind_proveHEq_x3f(v_fst_3029_, v_lhs_x27_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
lean_inc(v_a_3058_);
lean_dec_ref_known(v___x_3057_, 1);
v_____x_2981_ = v_a_3058_;
v___y_2982_ = v___y_3043_;
v___y_2983_ = v___y_3044_;
v___y_2984_ = v___y_3045_;
v___y_2985_ = v___y_3046_;
goto v___jp_2980_;
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
lean_dec_ref(v___x_2973_);
lean_del_object(v___x_2955_);
v_a_3059_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_3057_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3057_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
}
v___jp_3067_:
{
lean_object* v___x_3081_; 
lean_inc_ref(v___y_3068_);
v___x_3081_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isPatternLike___redArg(v___y_3068_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3116_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3084_ = v___x_3081_;
v_isShared_3085_ = v_isSharedCheck_3116_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3081_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3116_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
uint8_t v___x_3086_; 
v___x_3086_ = lean_unbox(v_a_3082_);
lean_dec(v_a_3082_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; lean_object* v___x_3089_; 
lean_dec_ref(v___y_3070_);
lean_dec_ref(v___y_3068_);
lean_dec(v_fst_3029_);
lean_del_object(v___x_2955_);
v___x_3087_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 1, v___x_2973_);
lean_ctor_set(v___x_3032_, 0, v___x_3087_);
v___x_3089_ = v___x_3032_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3087_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v___x_2973_);
v___x_3089_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
lean_object* v___x_3091_; 
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 0, v___x_3089_);
v___x_3091_ = v___x_3084_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3089_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
else
{
lean_object* v___x_3094_; 
lean_del_object(v___x_3084_);
lean_inc_ref(v___y_3070_);
v___x_3094_ = l_Lean_Meta_isDefEqD(v___y_3070_, v___y_3068_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3107_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3097_ = v___x_3094_;
v_isShared_3098_ = v_isSharedCheck_3107_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3094_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3107_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
uint8_t v___x_3099_; 
v___x_3099_ = lean_unbox(v_a_3095_);
lean_dec(v_a_3095_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; lean_object* v___x_3102_; 
lean_dec_ref(v___y_3070_);
lean_dec(v_fst_3029_);
lean_del_object(v___x_2955_);
v___x_3100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 1, v___x_2973_);
lean_ctor_set(v___x_3032_, 0, v___x_3100_);
v___x_3102_ = v___x_3032_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v___x_3100_);
lean_ctor_set(v_reuseFailAlloc_3106_, 1, v___x_2973_);
v___x_3102_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
lean_object* v___x_3104_; 
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 0, v___x_3102_);
v___x_3104_ = v___x_3097_;
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
else
{
lean_del_object(v___x_3097_);
lean_del_object(v___x_3032_);
v___y_3035_ = v___y_3069_;
v_lhs_x27_3036_ = v___y_3070_;
v___y_3037_ = v___y_3071_;
v___y_3038_ = v___y_3072_;
v___y_3039_ = v___y_3073_;
v___y_3040_ = v___y_3074_;
v___y_3041_ = v___y_3075_;
v___y_3042_ = v___y_3076_;
v___y_3043_ = v___y_3077_;
v___y_3044_ = v___y_3078_;
v___y_3045_ = v___y_3079_;
v___y_3046_ = v___y_3080_;
goto v___jp_3034_;
}
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_dec_ref(v___y_3070_);
lean_del_object(v___x_3032_);
lean_dec(v_fst_3029_);
lean_dec_ref(v___x_2973_);
lean_del_object(v___x_2955_);
v_a_3108_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_3094_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3094_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
}
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec_ref(v___y_3070_);
lean_dec_ref(v___y_3068_);
lean_del_object(v___x_3032_);
lean_dec(v_fst_3029_);
lean_dec_ref(v___x_2973_);
lean_del_object(v___x_2955_);
v_a_3117_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3081_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3081_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
v___jp_3125_:
{
lean_object* v___x_3128_; 
lean_inc(v_fst_3029_);
v___x_3128_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_fst_3029_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_toCold_3129_; lean_object* v_options_3130_; uint8_t v_hasTrace_3131_; 
v_toCold_3129_ = lean_ctor_get(v___y_2943_, 0);
v_options_3130_ = lean_ctor_get(v_toCold_3129_, 2);
v_hasTrace_3131_ = lean_ctor_get_uint8(v_options_3130_, sizeof(void*)*1);
if (v_hasTrace_3131_ == 0)
{
lean_object* v_a_3132_; 
lean_del_object(v___x_3027_);
v_a_3132_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_a_3132_);
lean_dec_ref_known(v___x_3128_, 1);
v___y_3068_ = v___y_3126_;
v___y_3069_ = v___y_3127_;
v___y_3070_ = v_a_3132_;
v___y_3071_ = v___y_2935_;
v___y_3072_ = v___y_2936_;
v___y_3073_ = v___y_2937_;
v___y_3074_ = v___y_2938_;
v___y_3075_ = v___y_2939_;
v___y_3076_ = v___y_2940_;
v___y_3077_ = v___y_2941_;
v___y_3078_ = v___y_2942_;
v___y_3079_ = v___y_2943_;
v___y_3080_ = v___y_2944_;
goto v___jp_3067_;
}
else
{
lean_object* v_a_3133_; lean_object* v_inheritedTraceOptions_3134_; lean_object* v___x_3135_; uint8_t v___x_3136_; 
v_a_3133_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_a_3133_);
lean_dec_ref_known(v___x_3128_, 1);
v_inheritedTraceOptions_3134_ = lean_ctor_get(v_toCold_3129_, 11);
v___x_3135_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__3);
v___x_3136_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3134_, v_options_3130_, v___x_3135_);
if (v___x_3136_ == 0)
{
lean_del_object(v___x_3027_);
v___y_3068_ = v___y_3126_;
v___y_3069_ = v___y_3127_;
v___y_3070_ = v_a_3133_;
v___y_3071_ = v___y_2935_;
v___y_3072_ = v___y_2936_;
v___y_3073_ = v___y_2937_;
v___y_3074_ = v___y_2938_;
v___y_3075_ = v___y_2939_;
v___y_3076_ = v___y_2940_;
v___y_3077_ = v___y_2941_;
v___y_3078_ = v___y_2942_;
v___y_3079_ = v___y_2943_;
v___y_3080_ = v___y_2944_;
goto v___jp_3067_;
}
else
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3140_; 
lean_inc(v_a_3133_);
v___x_3137_ = l_Lean_MessageData_ofExpr(v_a_3133_);
v___x_3138_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__5);
if (v_isShared_3028_ == 0)
{
lean_ctor_set_tag(v___x_3027_, 7);
lean_ctor_set(v___x_3027_, 1, v___x_3138_);
lean_ctor_set(v___x_3027_, 0, v___x_3137_);
v___x_3140_ = v___x_3027_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3137_);
lean_ctor_set(v_reuseFailAlloc_3152_, 1, v___x_3138_);
v___x_3140_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
lean_inc_ref(v___y_3126_);
v___x_3141_ = l_Lean_MessageData_ofExpr(v___y_3126_);
v___x_3142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_2978_, v___x_3142_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_dec_ref_known(v___x_3143_, 1);
v___y_3068_ = v___y_3126_;
v___y_3069_ = v___y_3127_;
v___y_3070_ = v_a_3133_;
v___y_3071_ = v___y_2935_;
v___y_3072_ = v___y_2936_;
v___y_3073_ = v___y_2937_;
v___y_3074_ = v___y_2938_;
v___y_3075_ = v___y_2939_;
v___y_3076_ = v___y_2940_;
v___y_3077_ = v___y_2941_;
v___y_3078_ = v___y_2942_;
v___y_3079_ = v___y_2943_;
v___y_3080_ = v___y_2944_;
goto v___jp_3067_;
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec(v_a_3133_);
lean_dec_ref(v___y_3126_);
lean_del_object(v___x_3032_);
lean_dec(v_fst_3029_);
lean_dec_ref(v___x_2973_);
lean_del_object(v___x_2955_);
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3143_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3143_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
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
}
}
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec_ref(v___y_3126_);
lean_del_object(v___x_3032_);
lean_dec(v_fst_3029_);
lean_del_object(v___x_3027_);
lean_dec_ref(v___x_2973_);
lean_del_object(v___x_2955_);
v_a_3153_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3128_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3128_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
v___jp_3161_:
{
lean_object* v___x_3163_; 
v___x_3163_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v_snd_3030_, v___y_2942_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; uint8_t v___x_3165_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3164_);
lean_dec_ref_known(v___x_3163_, 1);
v___x_3165_ = l_Lean_Expr_hasExprMVar(v_a_3164_);
if (v___x_3165_ == 0)
{
uint8_t v___x_3166_; 
v___x_3166_ = lean_unbox(v___x_2969_);
lean_dec(v___x_2969_);
if (v___x_3166_ == 0)
{
v___y_3126_ = v_a_3164_;
v___y_3127_ = v___y_3162_;
goto v___jp_3125_;
}
else
{
lean_object* v___x_3167_; 
v___x_3167_ = l_Lean_Meta_Grind_isEqv___redArg(v_fst_3029_, v_a_3164_, v___y_2935_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; uint8_t v___x_3169_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
lean_inc(v_a_3168_);
lean_dec_ref_known(v___x_3167_, 1);
v___x_3169_ = lean_unbox(v_a_3168_);
lean_dec(v_a_3168_);
if (v___x_3169_ == 0)
{
v___y_3126_ = v_a_3164_;
v___y_3127_ = v___y_3162_;
goto v___jp_3125_;
}
else
{
lean_del_object(v___x_3032_);
lean_del_object(v___x_3027_);
v___y_3035_ = v___y_3162_;
v_lhs_x27_3036_ = v_a_3164_;
v___y_3037_ = v___y_2935_;
v___y_3038_ = v___y_2936_;
v___y_3039_ = v___y_2937_;
v___y_3040_ = v___y_2938_;
v___y_3041_ = v___y_2939_;
v___y_3042_ = v___y_2940_;
v___y_3043_ = v___y_2941_;
v___y_3044_ = v___y_2942_;
v___y_3045_ = v___y_2943_;
v___y_3046_ = v___y_2944_;
goto v___jp_3034_;
}
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_dec(v_a_3164_);
lean_del_object(v___x_3032_);
lean_dec(v_fst_3029_);
lean_del_object(v___x_3027_);
lean_dec_ref(v___x_2973_);
lean_del_object(v___x_2955_);
v_a_3170_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3167_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3167_);
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
}
else
{
lean_dec(v___x_2969_);
v___y_3126_ = v_a_3164_;
v___y_3127_ = v___y_3162_;
goto v___jp_3125_;
}
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_del_object(v___x_3032_);
lean_dec(v_fst_3029_);
lean_del_object(v___x_3027_);
lean_dec_ref(v___x_2973_);
lean_dec(v___x_2969_);
lean_del_object(v___x_2955_);
v_a_3178_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3163_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3163_);
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
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3193_; 
lean_dec(v___x_3022_);
lean_dec(v___x_2969_);
lean_del_object(v___x_2955_);
v___x_3190_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
v___x_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
lean_ctor_set(v___x_3191_, 1, v___x_2973_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 0, v___x_3191_);
v___x_3193_ = v___x_3020_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3191_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
lean_dec_ref(v___x_2973_);
lean_dec(v___x_2969_);
lean_del_object(v___x_2955_);
v_a_3196_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3017_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3017_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
v___jp_2980_:
{
if (lean_obj_tag(v_____x_2981_) == 1)
{
lean_object* v_val_2986_; lean_object* v___x_2987_; 
v_val_2986_ = lean_ctor_get(v_____x_2981_, 0);
lean_inc(v_val_2986_);
lean_dec_ref_known(v_____x_2981_, 1);
lean_inc(v_a_2979_);
v___x_2987_ = l_Lean_Meta_isExprDefEq(v_a_2979_, v_val_2986_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3003_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2990_ = v___x_2987_;
v_isShared_2991_ = v_isSharedCheck_3003_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2987_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3003_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
uint8_t v___x_2992_; 
v___x_2992_ = lean_unbox(v_a_2988_);
lean_dec(v_a_2988_);
if (v___x_2992_ == 0)
{
lean_object* v___x_2993_; lean_object* v___x_2995_; 
v___x_2993_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v___x_2973_);
lean_ctor_set(v___x_2955_, 0, v___x_2993_);
v___x_2995_ = v___x_2955_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2993_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v___x_2973_);
v___x_2995_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2997_; 
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 0, v___x_2995_);
v___x_2997_ = v___x_2990_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2995_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
else
{
lean_object* v___x_3001_; 
lean_del_object(v___x_2990_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v___x_2973_);
lean_ctor_set(v___x_2955_, 0, v___x_2960_);
v___x_3001_ = v___x_2955_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2960_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v___x_2973_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
v_a_2947_ = v___x_3001_;
goto v___jp_2946_;
}
}
}
}
else
{
lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3011_; 
lean_dec_ref(v___x_2973_);
lean_del_object(v___x_2955_);
v_a_3004_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3006_ = v___x_2987_;
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v___x_2987_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
if (v_isShared_3007_ == 0)
{
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_a_3004_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
}
else
{
lean_object* v___x_3012_; lean_object* v___x_3014_; 
lean_dec(v_____x_2981_);
v___x_3012_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__2));
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v___x_2973_);
lean_ctor_set(v___x_2955_, 0, v___x_3012_);
v___x_3014_ = v___x_2955_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3012_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v___x_2973_);
v___x_3014_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
lean_object* v___x_3015_; 
v___x_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
return v___x_3015_;
}
}
}
}
}
}
}
}
}
v___jp_2946_:
{
size_t v___x_2948_; size_t v___x_2949_; 
v___x_2948_ = ((size_t)1ULL);
v___x_2949_ = lean_usize_add(v_i_2933_, v___x_2948_);
v_i_2933_ = v___x_2949_;
v_b_2934_ = v_a_2947_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2931_ = stack[0].m_obj;
size_t v_sz_2932_ = stack[1].m_num;
size_t v_i_2933_ = stack[2].m_num;
lean_object* v_b_2934_ = stack[3].m_obj;
lean_object* v___y_2935_ = stack[4].m_obj;
lean_object* v___y_2936_ = stack[5].m_obj;
lean_object* v___y_2937_ = stack[6].m_obj;
lean_object* v___y_2938_ = stack[7].m_obj;
lean_object* v___y_2939_ = stack[8].m_obj;
lean_object* v___y_2940_ = stack[9].m_obj;
lean_object* v___y_2941_ = stack[10].m_obj;
lean_object* v___y_2942_ = stack[11].m_obj;
lean_object* v___y_2943_ = stack[12].m_obj;
lean_object* v___y_2944_ = stack[13].m_obj;
lean_object* v_res_3211_;
v_res_3211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(v_as_2931_, v_sz_2932_, v_i_2933_, v_b_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
stack->m_obj
 = v_res_3211_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___boxed(lean_object* v_as_3212_, lean_object* v_sz_3213_, lean_object* v_i_3214_, lean_object* v_b_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
size_t v_sz_boxed_3227_; size_t v_i_boxed_3228_; lean_object* v_res_3229_; 
v_sz_boxed_3227_ = lean_unbox_usize(v_sz_3213_);
lean_dec(v_sz_3213_);
v_i_boxed_3228_ = lean_unbox_usize(v_i_3214_);
lean_dec(v_i_3214_);
v_res_3229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(v_as_3212_, v_sz_boxed_3227_, v_i_boxed_3228_, v_b_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec(v___y_3217_);
lean_dec(v___y_3216_);
lean_dec_ref(v_as_3212_);
return v_res_3229_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = ((lean_object*)(l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__0));
v___x_3232_ = l_Lean_stringToMessageData(v___x_3231_);
return v___x_3232_;
}
}
lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1(lean_object* v_arg_3233_, uint8_t v___x_3234_, lean_object* v_e_3235_, lean_object* v___f_3236_, lean_object* v_cls_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v___x_3249_; 
lean_inc_ref(v_arg_3233_);
v___x_3249_ = l_Lean_Meta_forallMetaTelescope(v_arg_3233_, v___x_3234_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3250_; lean_object* v_fst_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3369_; 
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_a_3250_);
lean_dec_ref_known(v___x_3249_, 1);
v_fst_3251_ = lean_ctor_get(v_a_3250_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v_a_3250_);
if (v_isSharedCheck_3369_ == 0)
{
lean_object* v_unused_3370_; 
v_unused_3370_ = lean_ctor_get(v_a_3250_, 1);
lean_dec(v_unused_3370_);
v___x_3253_ = v_a_3250_;
v_isShared_3254_ = v_isSharedCheck_3369_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_fst_3251_);
lean_dec(v_a_3250_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3369_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3261_; 
v___x_3255_ = l_Lean_Meta_mkGenDiseqMask(v_arg_3233_);
lean_dec_ref(v_arg_3233_);
v___x_3256_ = lean_unsigned_to_nat(0u);
v___x_3257_ = lean_array_get_size(v___x_3255_);
v___x_3258_ = l_Array_toSubarray___redArg(v___x_3255_, v___x_3256_, v___x_3257_);
v___x_3259_ = lean_box(0);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 1, v___x_3258_);
lean_ctor_set(v___x_3253_, 0, v___x_3259_);
v___x_3261_ = v___x_3253_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3259_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v___x_3258_);
v___x_3261_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
size_t v_sz_3262_; size_t v___x_3263_; lean_object* v___x_3264_; 
v_sz_3262_ = lean_array_size(v_fst_3251_);
v___x_3263_ = ((size_t)0ULL);
v___x_3264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(v_fst_3251_, v_sz_3262_, v___x_3263_, v___x_3261_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3359_; 
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3267_ = v___x_3264_;
v_isShared_3268_ = v_isSharedCheck_3359_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3264_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3359_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v_fst_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3357_; 
v_fst_3269_ = lean_ctor_get(v_a_3265_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v_a_3265_);
if (v_isSharedCheck_3357_ == 0)
{
lean_object* v_unused_3358_; 
v_unused_3358_ = lean_ctor_get(v_a_3265_, 1);
lean_dec(v_unused_3358_);
v___x_3271_ = v_a_3265_;
v_isShared_3272_ = v_isSharedCheck_3357_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_fst_3269_);
lean_dec(v_a_3265_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3357_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
if (lean_obj_tag(v_fst_3269_) == 0)
{
lean_object* v___x_3273_; 
lean_del_object(v___x_3267_);
lean_inc_ref(v_e_3235_);
v___x_3273_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_3235_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3344_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_a_3274_);
lean_dec_ref_known(v___x_3273_, 1);
v___x_3275_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3235_, v_a_3274_);
v___x_3276_ = l_Lean_mkAppN(v___x_3275_, v_fst_3251_);
lean_dec(v_fst_3251_);
v___x_3277_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(v___x_3276_, v___y_3245_);
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3280_ = v___x_3277_;
v_isShared_3281_ = v_isSharedCheck_3344_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3277_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3344_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3287_; 
lean_inc(v_a_3278_);
v___x_3287_ = l_Lean_Meta_hasAssignableMVar(v_a_3278_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3335_; 
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3290_ = v___x_3287_;
v_isShared_3291_ = v_isSharedCheck_3335_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3287_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3335_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
uint8_t v___x_3292_; 
v___x_3292_ = lean_unbox(v_a_3288_);
lean_dec(v_a_3288_);
if (v___x_3292_ == 0)
{
lean_object* v_toCold_3293_; lean_object* v_inheritedTraceOptions_3294_; lean_object* v___x_3295_; 
lean_del_object(v___x_3290_);
v_toCold_3293_ = lean_ctor_get(v___y_3246_, 0);
v_inheritedTraceOptions_3294_ = lean_ctor_get(v_toCold_3293_, 11);
lean_inc(v___y_3247_);
lean_inc_ref(v___y_3246_);
lean_inc(v___y_3245_);
lean_inc_ref(v___y_3244_);
lean_inc(v___y_3243_);
lean_inc_ref(v___y_3242_);
lean_inc(v___y_3241_);
lean_inc_ref(v___y_3240_);
lean_inc(v___y_3239_);
lean_inc(v___y_3238_);
lean_inc_ref(v_inheritedTraceOptions_3294_);
v___x_3295_ = lean_apply_12(v___f_3236_, v_inheritedTraceOptions_3294_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, lean_box(0));
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v_a_3296_; uint8_t v___x_3297_; 
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
lean_inc(v_a_3296_);
lean_dec_ref_known(v___x_3295_, 1);
v___x_3297_ = lean_unbox(v_a_3296_);
lean_dec(v_a_3296_);
if (v___x_3297_ == 0)
{
lean_del_object(v___x_3271_);
lean_dec(v_cls_3237_);
goto v___jp_3282_;
}
else
{
lean_object* v___x_3298_; 
lean_inc(v___y_3247_);
lean_inc_ref(v___y_3246_);
lean_inc(v___y_3245_);
lean_inc_ref(v___y_3244_);
lean_inc(v_a_3278_);
v___x_3298_ = lean_infer_type(v_a_3278_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3303_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_a_3299_);
lean_dec_ref_known(v___x_3298_, 1);
lean_inc(v_a_3278_);
v___x_3300_ = l_Lean_MessageData_ofExpr(v_a_3278_);
v___x_3301_ = lean_obj_once(&l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1, &l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1_once, _init_l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1);
if (v_isShared_3272_ == 0)
{
lean_ctor_set_tag(v___x_3271_, 7);
lean_ctor_set(v___x_3271_, 1, v___x_3301_);
lean_ctor_set(v___x_3271_, 0, v___x_3300_);
v___x_3303_ = v___x_3271_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3300_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v___x_3301_);
v___x_3303_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3304_ = l_Lean_MessageData_ofExpr(v_a_3299_);
v___x_3305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3303_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
v___x_3306_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3237_, v___x_3305_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_dec_ref_known(v___x_3306_, 1);
goto v___jp_3282_;
}
else
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
lean_del_object(v___x_3280_);
lean_dec(v_a_3278_);
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3306_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3306_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3312_; 
if (v_isShared_3310_ == 0)
{
v___x_3312_ = v___x_3309_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3307_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
}
else
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3323_; 
lean_del_object(v___x_3280_);
lean_dec(v_a_3278_);
lean_del_object(v___x_3271_);
lean_dec(v_cls_3237_);
v_a_3316_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3318_ = v___x_3298_;
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3298_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3321_; 
if (v_isShared_3319_ == 0)
{
v___x_3321_ = v___x_3318_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_a_3316_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
}
}
else
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3331_; 
lean_del_object(v___x_3280_);
lean_dec(v_a_3278_);
lean_del_object(v___x_3271_);
lean_dec(v_cls_3237_);
v_a_3324_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3326_ = v___x_3295_;
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3295_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3329_; 
if (v_isShared_3327_ == 0)
{
v___x_3329_ = v___x_3326_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
else
{
lean_object* v___x_3333_; 
lean_del_object(v___x_3280_);
lean_dec(v_a_3278_);
lean_del_object(v___x_3271_);
lean_dec(v_cls_3237_);
lean_dec_ref(v___f_3236_);
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 0, v___x_3259_);
v___x_3333_ = v___x_3290_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3259_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
else
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3343_; 
lean_del_object(v___x_3280_);
lean_dec(v_a_3278_);
lean_del_object(v___x_3271_);
lean_dec(v_cls_3237_);
lean_dec_ref(v___f_3236_);
v_a_3336_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3338_ = v___x_3287_;
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3287_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3341_; 
if (v_isShared_3339_ == 0)
{
v___x_3341_ = v___x_3338_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_a_3336_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
v___jp_3282_:
{
lean_object* v___x_3283_; lean_object* v___x_3285_; 
v___x_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3283_, 0, v_a_3278_);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 0, v___x_3283_);
v___x_3285_ = v___x_3280_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v___x_3283_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_del_object(v___x_3271_);
lean_dec(v_fst_3251_);
lean_dec(v_cls_3237_);
lean_dec_ref(v___f_3236_);
lean_dec_ref(v_e_3235_);
v_a_3345_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3273_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3273_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
else
{
lean_object* v_val_3353_; lean_object* v___x_3355_; 
lean_del_object(v___x_3271_);
lean_dec(v_fst_3251_);
lean_dec(v_cls_3237_);
lean_dec_ref(v___f_3236_);
lean_dec_ref(v_e_3235_);
v_val_3353_ = lean_ctor_get(v_fst_3269_, 0);
lean_inc(v_val_3353_);
lean_dec_ref_known(v_fst_3269_, 1);
if (v_isShared_3268_ == 0)
{
lean_ctor_set(v___x_3267_, 0, v_val_3353_);
v___x_3355_ = v___x_3267_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_val_3353_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
}
else
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3367_; 
lean_dec(v_fst_3251_);
lean_dec(v_cls_3237_);
lean_dec_ref(v___f_3236_);
lean_dec_ref(v_e_3235_);
v_a_3360_ = lean_ctor_get(v___x_3264_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3362_ = v___x_3264_;
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3264_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3365_; 
if (v_isShared_3363_ == 0)
{
v___x_3365_ = v___x_3362_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_a_3360_);
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
}
}
else
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
lean_dec(v_cls_3237_);
lean_dec_ref(v___f_3236_);
lean_dec_ref(v_e_3235_);
lean_dec_ref(v_arg_3233_);
v_a_3371_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v___x_3249_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3249_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3374_ == 0)
{
v___x_3376_ = v___x_3373_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_tryToProveFalse___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_3233_ = stack[0].m_obj;
uint8_t v___x_3234_ = stack[1].m_num;
lean_object* v_e_3235_ = stack[2].m_obj;
lean_object* v___f_3236_ = stack[3].m_obj;
lean_object* v_cls_3237_ = stack[4].m_obj;
lean_object* v___y_3238_ = stack[5].m_obj;
lean_object* v___y_3239_ = stack[6].m_obj;
lean_object* v___y_3240_ = stack[7].m_obj;
lean_object* v___y_3241_ = stack[8].m_obj;
lean_object* v___y_3242_ = stack[9].m_obj;
lean_object* v___y_3243_ = stack[10].m_obj;
lean_object* v___y_3244_ = stack[11].m_obj;
lean_object* v___y_3245_ = stack[12].m_obj;
lean_object* v___y_3246_ = stack[13].m_obj;
lean_object* v___y_3247_ = stack[14].m_obj;
lean_object* v_res_3379_;
v_res_3379_ = l_Lean_Meta_Grind_tryToProveFalse___lam__1(v_arg_3233_, v___x_3234_, v_e_3235_, v___f_3236_, v_cls_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
stack->m_obj
 = v_res_3379_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__1___boxed(lean_object* v_arg_3380_, lean_object* v___x_3381_, lean_object* v_e_3382_, lean_object* v___f_3383_, lean_object* v_cls_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_){
_start:
{
uint8_t v___x_77804__boxed_3396_; lean_object* v_res_3397_; 
v___x_77804__boxed_3396_ = lean_unbox(v___x_3381_);
v_res_3397_ = l_Lean_Meta_Grind_tryToProveFalse___lam__1(v_arg_3380_, v___x_77804__boxed_3396_, v_e_3382_, v___f_3383_, v_cls_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec(v___y_3385_);
return v_res_3397_;
}
}
lean_object* l_Lean_Meta_Grind_tryToProveFalse(lean_object* v_e_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_){
_start:
{
lean_object* v_toCold_3415_; lean_object* v_inheritedTraceOptions_3416_; lean_object* v_cls_3417_; lean_object* v___f_3418_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___x_3470_; lean_object* v_a_3471_; uint8_t v___x_3472_; 
v_toCold_3415_ = lean_ctor_get(v_a_3409_, 0);
v_inheritedTraceOptions_3416_ = lean_ctor_get(v_toCold_3415_, 11);
v_cls_3417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___closed__1));
v___f_3418_ = ((lean_object*)(l_Lean_Meta_Grind_tryToProveFalse___closed__0));
v___x_3470_ = l_Lean_Meta_Grind_tryToProveFalse___lam__0(v_cls_3417_, v_inheritedTraceOptions_3416_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3471_);
lean_dec_ref(v___x_3470_);
v___x_3472_ = lean_unbox(v_a_3471_);
lean_dec(v_a_3471_);
if (v___x_3472_ == 0)
{
v___y_3420_ = v_a_3401_;
v___y_3421_ = v_a_3402_;
v___y_3422_ = v_a_3403_;
v___y_3423_ = v_a_3404_;
v___y_3424_ = v_a_3405_;
v___y_3425_ = v_a_3406_;
v___y_3426_ = v_a_3407_;
v___y_3427_ = v_a_3408_;
v___y_3428_ = v_a_3409_;
v___y_3429_ = v_a_3410_;
goto v___jp_3419_;
}
else
{
lean_object* v___x_3473_; 
v___x_3473_ = l_Lean_Meta_Grind_updateLastTag(v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
lean_dec_ref_known(v___x_3473_, 1);
lean_inc_ref(v_e_3400_);
v___x_3474_ = l_Lean_MessageData_ofExpr(v_e_3400_);
v___x_3475_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3417_, v___x_3474_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_dec_ref_known(v___x_3475_, 1);
v___y_3420_ = v_a_3401_;
v___y_3421_ = v_a_3402_;
v___y_3422_ = v_a_3403_;
v___y_3423_ = v_a_3404_;
v___y_3424_ = v_a_3405_;
v___y_3425_ = v_a_3406_;
v___y_3426_ = v_a_3407_;
v___y_3427_ = v_a_3408_;
v___y_3428_ = v_a_3409_;
v___y_3429_ = v_a_3410_;
goto v___jp_3419_;
}
else
{
lean_dec_ref(v_e_3400_);
return v___x_3475_;
}
}
else
{
lean_dec_ref(v_e_3400_);
return v___x_3473_;
}
}
v___jp_3412_:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = lean_box(0);
v___x_3414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
return v___x_3414_;
}
v___jp_3419_:
{
lean_object* v___x_3430_; 
lean_inc_ref(v_e_3400_);
v___x_3430_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3400_, v___y_3427_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v___x_3432_; uint8_t v___x_3433_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3431_);
lean_dec_ref_known(v___x_3430_, 1);
v___x_3432_ = l_Lean_Expr_cleanupAnnotations(v_a_3431_);
v___x_3433_ = l_Lean_Expr_isApp(v___x_3432_);
if (v___x_3433_ == 0)
{
lean_dec_ref(v___x_3432_);
lean_dec_ref(v_e_3400_);
goto v___jp_3412_;
}
else
{
lean_object* v_arg_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; uint8_t v___x_3437_; 
v_arg_3434_ = lean_ctor_get(v___x_3432_, 1);
lean_inc_ref(v_arg_3434_);
v___x_3435_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3432_);
v___x_3436_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3437_ = l_Lean_Expr_isConstOf(v___x_3435_, v___x_3436_);
lean_dec_ref(v___x_3435_);
if (v___x_3437_ == 0)
{
lean_dec_ref(v_arg_3434_);
lean_dec_ref(v_e_3400_);
goto v___jp_3412_;
}
else
{
uint8_t v___x_3438_; lean_object* v___x_3439_; lean_object* v___f_3440_; uint8_t v___x_3441_; lean_object* v___x_3442_; 
v___x_3438_ = 0;
v___x_3439_ = lean_box(v___x_3438_);
v___f_3440_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_tryToProveFalse___lam__1___boxed), 16, 5);
lean_closure_set(v___f_3440_, 0, v_arg_3434_);
lean_closure_set(v___f_3440_, 1, v___x_3439_);
lean_closure_set(v___f_3440_, 2, v_e_3400_);
lean_closure_set(v___f_3440_, 3, v___f_3418_);
lean_closure_set(v___f_3440_, 4, v_cls_3417_);
v___x_3441_ = 0;
v___x_3442_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(v___f_3440_, v___x_3441_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3453_; 
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3445_ = v___x_3442_;
v_isShared_3446_ = v_isSharedCheck_3453_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3442_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3453_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
if (lean_obj_tag(v_a_3443_) == 1)
{
lean_object* v_val_3447_; lean_object* v___x_3448_; 
lean_del_object(v___x_3445_);
v_val_3447_ = lean_ctor_get(v_a_3443_, 0);
lean_inc(v_val_3447_);
lean_dec_ref_known(v_a_3443_, 1);
v___x_3448_ = l_Lean_Meta_Grind_closeGoal(v_val_3447_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
return v___x_3448_;
}
else
{
lean_object* v___x_3449_; lean_object* v___x_3451_; 
lean_dec(v_a_3443_);
v___x_3449_ = lean_box(0);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 0, v___x_3449_);
v___x_3451_ = v___x_3445_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3449_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
else
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3461_; 
v_a_3454_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3456_ = v___x_3442_;
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3442_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3457_ == 0)
{
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_a_3454_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
}
}
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
lean_dec_ref(v_e_3400_);
v_a_3462_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3430_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3430_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3462_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_tryToProveFalse_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3400_ = stack[0].m_obj;
lean_object* v_a_3401_ = stack[1].m_obj;
lean_object* v_a_3402_ = stack[2].m_obj;
lean_object* v_a_3403_ = stack[3].m_obj;
lean_object* v_a_3404_ = stack[4].m_obj;
lean_object* v_a_3405_ = stack[5].m_obj;
lean_object* v_a_3406_ = stack[6].m_obj;
lean_object* v_a_3407_ = stack[7].m_obj;
lean_object* v_a_3408_ = stack[8].m_obj;
lean_object* v_a_3409_ = stack[9].m_obj;
lean_object* v_a_3410_ = stack[10].m_obj;
lean_object* v_res_3476_;
v_res_3476_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
stack->m_obj
 = v_res_3476_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___boxed(lean_object* v_e_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
lean_dec(v_a_3487_);
lean_dec_ref(v_a_3486_);
lean_dec(v_a_3485_);
lean_dec_ref(v_a_3484_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
lean_dec(v_a_3479_);
lean_dec(v_a_3478_);
return v_res_3489_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1(void){
_start:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3491_ = ((lean_object*)(l_Lean_Meta_Grind_propagateMatchCondUp___closed__0));
v___x_3492_ = l_Lean_stringToMessageData(v___x_3491_);
return v___x_3492_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3(void){
_start:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3494_ = ((lean_object*)(l_Lean_Meta_Grind_propagateMatchCondUp___closed__2));
v___x_3495_ = l_Lean_stringToMessageData(v___x_3494_);
return v___x_3495_;
}
}
lean_object* l_Lean_Meta_Grind_propagateMatchCondUp(lean_object* v_e_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_){
_start:
{
lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v_toCold_3522_; lean_object* v_options_3523_; lean_object* v_inheritedTraceOptions_3524_; uint8_t v_hasTrace_3525_; lean_object* v_cls_3526_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; 
v_toCold_3522_ = lean_ctor_get(v_a_3505_, 0);
v_options_3523_ = lean_ctor_get(v_toCold_3522_, 2);
v_inheritedTraceOptions_3524_ = lean_ctor_get(v_toCold_3522_, 11);
v_hasTrace_3525_ = lean_ctor_get_uint8(v_options_3523_, sizeof(void*)*1);
v_cls_3526_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3));
if (v_hasTrace_3525_ == 0)
{
v___y_3528_ = v_a_3497_;
v___y_3529_ = v_a_3498_;
v___y_3530_ = v_a_3499_;
v___y_3531_ = v_a_3500_;
v___y_3532_ = v_a_3501_;
v___y_3533_ = v_a_3502_;
v___y_3534_ = v_a_3503_;
v___y_3535_ = v_a_3504_;
v___y_3536_ = v_a_3505_;
v___y_3537_ = v_a_3506_;
goto v___jp_3527_;
}
else
{
lean_object* v___x_3634_; uint8_t v___x_3635_; 
v___x_3634_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_3635_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3524_, v_options_3523_, v___x_3634_);
if (v___x_3635_ == 0)
{
v___y_3528_ = v_a_3497_;
v___y_3529_ = v_a_3498_;
v___y_3530_ = v_a_3499_;
v___y_3531_ = v_a_3500_;
v___y_3532_ = v_a_3501_;
v___y_3533_ = v_a_3502_;
v___y_3534_ = v_a_3503_;
v___y_3535_ = v_a_3504_;
v___y_3536_ = v_a_3505_;
v___y_3537_ = v_a_3506_;
goto v___jp_3527_;
}
else
{
lean_object* v___x_3636_; 
v___x_3636_ = l_Lean_Meta_Grind_updateLastTag(v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; 
lean_dec_ref_known(v___x_3636_, 1);
v___x_3637_ = lean_obj_once(&l_Lean_Meta_Grind_propagateMatchCondUp___closed__3, &l_Lean_Meta_Grind_propagateMatchCondUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3);
lean_inc_ref(v_e_3496_);
v___x_3638_ = l_Lean_indentExpr(v_e_3496_);
v___x_3639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3637_);
lean_ctor_set(v___x_3639_, 1, v___x_3638_);
v___x_3640_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3526_, v___x_3639_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_dec_ref_known(v___x_3640_, 1);
v___y_3528_ = v_a_3497_;
v___y_3529_ = v_a_3498_;
v___y_3530_ = v_a_3499_;
v___y_3531_ = v_a_3500_;
v___y_3532_ = v_a_3501_;
v___y_3533_ = v_a_3502_;
v___y_3534_ = v_a_3503_;
v___y_3535_ = v_a_3504_;
v___y_3536_ = v_a_3505_;
v___y_3537_ = v_a_3506_;
goto v___jp_3527_;
}
else
{
lean_dec_ref(v_e_3496_);
return v___x_3640_;
}
}
else
{
lean_dec_ref(v_e_3496_);
return v___x_3636_;
}
}
}
v___jp_3508_:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3509_ = lean_box(0);
v___x_3510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3509_);
return v___x_3510_;
}
v___jp_3511_:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
lean_inc_ref(v_e_3496_);
v___x_3520_ = l_Lean_Meta_mkEqTrueCore(v_e_3496_, v___y_3512_);
v___x_3521_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_3496_, v___x_3520_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
return v___x_3521_;
}
v___jp_3527_:
{
lean_object* v___x_3538_; 
lean_inc_ref(v_e_3496_);
v___x_3538_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3496_, v___y_3528_, v___y_3532_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3539_; uint8_t v___x_3540_; 
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_a_3539_);
lean_dec_ref_known(v___x_3538_, 1);
v___x_3540_ = lean_unbox(v_a_3539_);
lean_dec(v_a_3539_);
if (v___x_3540_ == 0)
{
lean_object* v___x_3541_; 
lean_inc_ref(v_e_3496_);
v___x_3541_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3496_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3597_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3544_ = v___x_3541_;
v_isShared_3545_ = v_isSharedCheck_3597_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3541_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3597_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
uint8_t v___x_3546_; 
v___x_3546_ = lean_unbox(v_a_3542_);
lean_dec(v_a_3542_);
if (v___x_3546_ == 0)
{
lean_object* v___x_3547_; lean_object* v___x_3549_; 
lean_dec_ref(v_e_3496_);
v___x_3547_ = lean_box(0);
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 0, v___x_3547_);
v___x_3549_ = v___x_3544_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3547_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
else
{
lean_object* v___x_3551_; 
lean_del_object(v___x_3544_);
lean_inc_ref(v_e_3496_);
v___x_3551_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_3496_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3552_);
lean_dec_ref_known(v___x_3551_, 1);
if (lean_obj_tag(v_a_3552_) == 1)
{
lean_object* v_toCold_3553_; lean_object* v_options_3554_; uint8_t v_hasTrace_3555_; 
v_toCold_3553_ = lean_ctor_get(v___y_3536_, 0);
v_options_3554_ = lean_ctor_get(v_toCold_3553_, 2);
v_hasTrace_3555_ = lean_ctor_get_uint8(v_options_3554_, sizeof(void*)*1);
if (v_hasTrace_3555_ == 0)
{
lean_object* v_val_3556_; 
v_val_3556_ = lean_ctor_get(v_a_3552_, 0);
lean_inc(v_val_3556_);
lean_dec_ref_known(v_a_3552_, 1);
v___y_3512_ = v_val_3556_;
v___y_3513_ = v___y_3528_;
v___y_3514_ = v___y_3530_;
v___y_3515_ = v___y_3532_;
v___y_3516_ = v___y_3534_;
v___y_3517_ = v___y_3535_;
v___y_3518_ = v___y_3536_;
v___y_3519_ = v___y_3537_;
goto v___jp_3511_;
}
else
{
lean_object* v_val_3557_; lean_object* v_inheritedTraceOptions_3558_; lean_object* v___x_3559_; uint8_t v___x_3560_; 
v_val_3557_ = lean_ctor_get(v_a_3552_, 0);
lean_inc(v_val_3557_);
lean_dec_ref_known(v_a_3552_, 1);
v_inheritedTraceOptions_3558_ = lean_ctor_get(v_toCold_3553_, 11);
v___x_3559_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
v___x_3560_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3558_, v_options_3554_, v___x_3559_);
if (v___x_3560_ == 0)
{
v___y_3512_ = v_val_3557_;
v___y_3513_ = v___y_3528_;
v___y_3514_ = v___y_3530_;
v___y_3515_ = v___y_3532_;
v___y_3516_ = v___y_3534_;
v___y_3517_ = v___y_3535_;
v___y_3518_ = v___y_3536_;
v___y_3519_ = v___y_3537_;
goto v___jp_3511_;
}
else
{
lean_object* v___x_3561_; 
v___x_3561_ = l_Lean_Meta_Grind_updateLastTag(v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v___x_3562_; 
lean_dec_ref_known(v___x_3561_, 1);
lean_inc(v___y_3537_);
lean_inc_ref(v___y_3536_);
lean_inc(v___y_3535_);
lean_inc_ref(v___y_3534_);
lean_inc(v_val_3557_);
v___x_3562_ = lean_infer_type(v_val_3557_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
lean_inc(v_a_3563_);
lean_dec_ref_known(v___x_3562_, 1);
v___x_3564_ = l_Lean_MessageData_ofExpr(v_a_3563_);
v___x_3565_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3526_, v___x_3564_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_dec_ref_known(v___x_3565_, 1);
v___y_3512_ = v_val_3557_;
v___y_3513_ = v___y_3528_;
v___y_3514_ = v___y_3530_;
v___y_3515_ = v___y_3532_;
v___y_3516_ = v___y_3534_;
v___y_3517_ = v___y_3535_;
v___y_3518_ = v___y_3536_;
v___y_3519_ = v___y_3537_;
goto v___jp_3511_;
}
else
{
lean_dec(v_val_3557_);
lean_dec_ref(v_e_3496_);
return v___x_3565_;
}
}
else
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
lean_dec(v_val_3557_);
lean_dec_ref(v_e_3496_);
v_a_3566_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3568_ = v___x_3562_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3562_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
if (v_isShared_3569_ == 0)
{
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3566_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
else
{
lean_dec(v_val_3557_);
lean_dec_ref(v_e_3496_);
return v___x_3561_;
}
}
}
}
else
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
lean_dec(v_a_3552_);
v___x_3574_ = lean_obj_once(&l_Lean_Meta_Grind_propagateMatchCondUp___closed__1, &l_Lean_Meta_Grind_propagateMatchCondUp___closed__1_once, _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1);
v___x_3575_ = l_Lean_indentExpr(v_e_3496_);
v___x_3576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3574_);
lean_ctor_set(v___x_3576_, 1, v___x_3575_);
v___x_3577_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_3532_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v_a_3578_; uint8_t v_verbose_3579_; 
v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
lean_inc(v_a_3578_);
lean_dec_ref_known(v___x_3577_, 1);
v_verbose_3579_ = lean_ctor_get_uint8(v_a_3578_, 0);
lean_dec(v_a_3578_);
if (v_verbose_3579_ == 0)
{
lean_dec_ref_known(v___x_3576_, 2);
goto v___jp_3508_;
}
else
{
lean_object* v___x_3580_; 
v___x_3580_ = l_Lean_Meta_Sym_reportIssue(v___x_3576_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_dec_ref_known(v___x_3580_, 1);
goto v___jp_3508_;
}
else
{
return v___x_3580_;
}
}
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec_ref_known(v___x_3576_, 2);
v_a_3581_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3577_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3577_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
}
else
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3596_; 
lean_dec_ref(v_e_3496_);
v_a_3589_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3591_ = v___x_3551_;
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3551_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3594_; 
if (v_isShared_3592_ == 0)
{
v___x_3594_ = v___x_3591_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_a_3589_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
}
}
else
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3605_; 
lean_dec_ref(v_e_3496_);
v_a_3598_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3600_ = v___x_3541_;
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3541_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3603_; 
if (v_isShared_3601_ == 0)
{
v___x_3603_ = v___x_3600_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_a_3598_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
}
}
else
{
lean_object* v___x_3606_; 
lean_inc_ref(v_e_3496_);
v___x_3606_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3496_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3617_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3609_ = v___x_3606_;
v_isShared_3610_ = v_isSharedCheck_3617_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3606_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3617_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
uint8_t v___x_3611_; 
v___x_3611_ = lean_unbox(v_a_3607_);
lean_dec(v_a_3607_);
if (v___x_3611_ == 0)
{
lean_object* v___x_3612_; 
lean_del_object(v___x_3609_);
v___x_3612_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3496_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
return v___x_3612_;
}
else
{
lean_object* v___x_3613_; lean_object* v___x_3615_; 
lean_dec_ref(v_e_3496_);
v___x_3613_ = lean_box(0);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 0, v___x_3613_);
v___x_3615_ = v___x_3609_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3613_);
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
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_dec_ref(v_e_3496_);
v_a_3618_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3606_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3606_);
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
else
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3633_; 
lean_dec_ref(v_e_3496_);
v_a_3626_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3628_ = v___x_3538_;
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3538_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3631_; 
if (v_isShared_3629_ == 0)
{
v___x_3631_ = v___x_3628_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3626_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateMatchCondUp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3496_ = stack[0].m_obj;
lean_object* v_a_3497_ = stack[1].m_obj;
lean_object* v_a_3498_ = stack[2].m_obj;
lean_object* v_a_3499_ = stack[3].m_obj;
lean_object* v_a_3500_ = stack[4].m_obj;
lean_object* v_a_3501_ = stack[5].m_obj;
lean_object* v_a_3502_ = stack[6].m_obj;
lean_object* v_a_3503_ = stack[7].m_obj;
lean_object* v_a_3504_ = stack[8].m_obj;
lean_object* v_a_3505_ = stack[9].m_obj;
lean_object* v_a_3506_ = stack[10].m_obj;
lean_object* v_res_3641_;
v_res_3641_ = l_Lean_Meta_Grind_propagateMatchCondUp(v_e_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_);
stack->m_obj
 = v_res_3641_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___boxed(lean_object* v_e_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Lean_Meta_Grind_propagateMatchCondUp(v_e_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_);
lean_dec(v_a_3652_);
lean_dec_ref(v_a_3651_);
lean_dec(v_a_3650_);
lean_dec_ref(v_a_3649_);
lean_dec(v_a_3648_);
lean_dec_ref(v_a_3647_);
lean_dec(v_a_3646_);
lean_dec_ref(v_a_3645_);
lean_dec(v_a_3644_);
lean_dec(v_a_3643_);
return v_res_3654_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3656_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3657_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondUp___boxed), 12, 0);
v___x_3658_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3656_, v___x_3657_);
return v___x_3658_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3659_;
v_res_3659_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_9_();
stack->m_obj
 = v_res_3659_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_9____boxed(lean_object* v_a_3660_){
_start:
{
lean_object* v_res_3661_; 
v_res_3661_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_9_();
return v_res_3661_;
}
}
lean_object* l_Lean_Meta_Grind_propagateMatchCondDown(lean_object* v_e_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_){
_start:
{
lean_object* v___x_3674_; 
lean_inc_ref(v_e_3662_);
v___x_3674_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3662_, v_a_3663_, v_a_3667_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3704_; 
v_a_3675_ = lean_ctor_get(v___x_3674_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3674_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3677_ = v___x_3674_;
v_isShared_3678_ = v_isSharedCheck_3704_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3674_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3704_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
uint8_t v___x_3679_; 
v___x_3679_ = lean_unbox(v_a_3675_);
lean_dec(v_a_3675_);
if (v___x_3679_ == 0)
{
lean_object* v___x_3680_; lean_object* v___x_3682_; 
lean_dec_ref(v_e_3662_);
v___x_3680_ = lean_box(0);
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 0, v___x_3680_);
v___x_3682_ = v___x_3677_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3680_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
else
{
lean_object* v___x_3684_; 
lean_del_object(v___x_3677_);
lean_inc_ref(v_e_3662_);
v___x_3684_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3695_; 
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3687_ = v___x_3684_;
v_isShared_3688_ = v_isSharedCheck_3695_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3684_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3695_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
uint8_t v___x_3689_; 
v___x_3689_ = lean_unbox(v_a_3685_);
lean_dec(v_a_3685_);
if (v___x_3689_ == 0)
{
lean_object* v___x_3690_; 
lean_del_object(v___x_3687_);
v___x_3690_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
return v___x_3690_;
}
else
{
lean_object* v___x_3691_; lean_object* v___x_3693_; 
lean_dec_ref(v_e_3662_);
v___x_3691_ = lean_box(0);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 0, v___x_3691_);
v___x_3693_ = v___x_3687_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_dec_ref(v_e_3662_);
v_a_3696_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3684_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3684_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
}
}
else
{
lean_object* v_a_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3712_; 
lean_dec_ref(v_e_3662_);
v_a_3705_ = lean_ctor_get(v___x_3674_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v___x_3674_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3707_ = v___x_3674_;
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
else
{
lean_inc(v_a_3705_);
lean_dec(v___x_3674_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
lean_object* v___x_3710_; 
if (v_isShared_3708_ == 0)
{
v___x_3710_ = v___x_3707_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_a_3705_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateMatchCondDown_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3662_ = stack[0].m_obj;
lean_object* v_a_3663_ = stack[1].m_obj;
lean_object* v_a_3664_ = stack[2].m_obj;
lean_object* v_a_3665_ = stack[3].m_obj;
lean_object* v_a_3666_ = stack[4].m_obj;
lean_object* v_a_3667_ = stack[5].m_obj;
lean_object* v_a_3668_ = stack[6].m_obj;
lean_object* v_a_3669_ = stack[7].m_obj;
lean_object* v_a_3670_ = stack[8].m_obj;
lean_object* v_a_3671_ = stack[9].m_obj;
lean_object* v_a_3672_ = stack[10].m_obj;
lean_object* v_res_3713_;
v_res_3713_ = l_Lean_Meta_Grind_propagateMatchCondDown(v_e_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
stack->m_obj
 = v_res_3713_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___boxed(lean_object* v_e_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l_Lean_Meta_Grind_propagateMatchCondDown(v_e_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_);
lean_dec(v_a_3724_);
lean_dec_ref(v_a_3723_);
lean_dec(v_a_3722_);
lean_dec_ref(v_a_3721_);
lean_dec(v_a_3720_);
lean_dec_ref(v_a_3719_);
lean_dec(v_a_3718_);
lean_dec_ref(v_a_3717_);
lean_dec(v_a_3716_);
lean_dec(v_a_3715_);
return v_res_3726_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3728_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3729_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondDown___boxed), 12, 0);
v___x_3730_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3728_, v___x_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3731_;
v_res_3731_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_9_();
stack->m_obj
 = v_res_3731_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_9____boxed(lean_object* v_a_3732_){
_start:
{
lean_object* v_res_3733_; 
v_res_3733_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_9_();
return v_res_3733_;
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
