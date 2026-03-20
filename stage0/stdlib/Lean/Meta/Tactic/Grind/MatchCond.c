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
lean_object* lean_st_ref_get(lean_object*);
uint64_t l_Lean_instHashableLevelMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLevelMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_normLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_heq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_proveEq_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_proveHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0(lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss(lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__0_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__1_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchCond"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__2_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__3_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__3_value_aux_1),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(181, 170, 56, 23, 185, 62, 169, 45)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__3 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__3_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "satifised"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__4 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__4_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__5;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "\nthe following equality is false"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__6 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__6_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__7;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__0;
static const lean_closure_object l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__1 = (const lean_object*)&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__2 = (const lean_object*)&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__3 = (const lean_object*)&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__4 = (const lean_object*)&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.MetavarContext"};
static const lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___closed__0 = (const lean_object*)&l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___closed__0_value;
static const lean_string_object l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.isLevelMVarAssignable"};
static const lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___closed__1 = (const lean_object*)&l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___closed__1_value;
static const lean_string_object l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "unknown universe metavariable "};
static const lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___closed__2 = (const lean_object*)&l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "proveFalse"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_1),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(181, 170, 56, 23, 185, 62, 169, 45)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(234, 57, 131, 114, 246, 81, 253, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " =\?= "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0(lean_object* v_b_38_){
_start:
{
lean_object* v_snd_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_90_; 
v_snd_39_ = lean_ctor_get(v_b_38_, 1);
v_isSharedCheck_90_ = !lean_is_exclusive(v_b_38_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; 
v_unused_91_ = lean_ctor_get(v_b_38_, 0);
lean_dec(v_unused_91_);
v___x_41_ = v_b_38_;
v_isShared_42_ = v_isSharedCheck_90_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_snd_39_);
lean_dec(v_b_38_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_90_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v_snd_43_; 
v_snd_43_ = lean_ctor_get(v_snd_39_, 1);
lean_inc(v_snd_43_);
if (lean_obj_tag(v_snd_43_) == 7)
{
lean_object* v_fst_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_75_; 
v_fst_44_ = lean_ctor_get(v_snd_39_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v_snd_39_);
if (v_isSharedCheck_75_ == 0)
{
lean_object* v_unused_76_; 
v_unused_76_ = lean_ctor_get(v_snd_39_, 1);
lean_dec(v_unused_76_);
v___x_46_ = v_snd_39_;
v_isShared_47_ = v_isSharedCheck_75_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_fst_44_);
lean_dec(v_snd_39_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_75_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v_binderType_48_; lean_object* v_body_49_; lean_object* v___x_50_; lean_object* v_r_52_; lean_object* v___x_60_; 
v_binderType_48_ = lean_ctor_get(v_snd_43_, 1);
lean_inc_ref(v_binderType_48_);
v_body_49_ = lean_ctor_get(v_snd_43_, 2);
lean_inc_ref(v_body_49_);
lean_dec_ref(v_snd_43_);
v___x_50_ = lean_box(0);
v___x_60_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_binderType_48_);
if (lean_obj_tag(v___x_60_) == 1)
{
lean_object* v_val_61_; lean_object* v_snd_62_; lean_object* v_fst_63_; lean_object* v_fst_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_73_; 
v_val_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_val_61_);
lean_dec_ref(v___x_60_);
v_snd_62_ = lean_ctor_get(v_val_61_, 1);
lean_inc(v_snd_62_);
v_fst_63_ = lean_ctor_get(v_val_61_, 0);
lean_inc(v_fst_63_);
lean_dec(v_val_61_);
v_fst_64_ = lean_ctor_get(v_snd_62_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v_snd_62_);
if (v_isSharedCheck_73_ == 0)
{
lean_object* v_unused_74_; 
v_unused_74_ = lean_ctor_get(v_snd_62_, 1);
lean_dec(v_unused_74_);
v___x_66_ = v_snd_62_;
v_isShared_67_ = v_isSharedCheck_73_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_fst_64_);
lean_dec(v_snd_62_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_73_;
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
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v_fst_64_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v_fst_63_);
v___x_70_ = v_reuseFailAlloc_72_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v_r_71_; 
v_r_71_ = lean_array_push(v_fst_44_, v___x_70_);
v_r_52_ = v_r_71_;
goto v___jp_51_;
}
}
else
{
lean_del_object(v___x_66_);
lean_dec(v_fst_64_);
lean_dec(v_fst_63_);
v_r_52_ = v_fst_44_;
goto v___jp_51_;
}
}
}
else
{
lean_dec(v___x_60_);
v_r_52_ = v_fst_44_;
goto v___jp_51_;
}
v___jp_51_:
{
lean_object* v___x_54_; 
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 1, v_body_49_);
lean_ctor_set(v___x_46_, 0, v_r_52_);
v___x_54_ = v___x_46_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_r_52_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v_body_49_);
v___x_54_ = v_reuseFailAlloc_59_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
lean_object* v___x_56_; 
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 1, v___x_54_);
lean_ctor_set(v___x_41_, 0, v___x_50_);
v___x_56_ = v___x_41_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___x_50_);
lean_ctor_set(v_reuseFailAlloc_58_, 1, v___x_54_);
v___x_56_ = v_reuseFailAlloc_58_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
v_b_38_ = v___x_56_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_fst_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_88_; 
v_fst_77_ = lean_ctor_get(v_snd_39_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v_snd_39_);
if (v_isSharedCheck_88_ == 0)
{
lean_object* v_unused_89_; 
v_unused_89_ = lean_ctor_get(v_snd_39_, 1);
lean_dec(v_unused_89_);
v___x_79_ = v_snd_39_;
v_isShared_80_ = v_isSharedCheck_88_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_fst_77_);
lean_dec(v_snd_39_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_88_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; lean_object* v___x_83_; 
lean_inc(v_fst_77_);
v___x_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_81_, 0, v_fst_77_);
if (v_isShared_80_ == 0)
{
v___x_83_ = v___x_79_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_fst_77_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v_snd_43_);
v___x_83_ = v_reuseFailAlloc_87_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
lean_object* v___x_85_; 
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 1, v___x_83_);
lean_ctor_set(v___x_41_, 0, v___x_81_);
v___x_85_ = v___x_41_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_81_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v___x_83_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss(lean_object* v_e_94_){
_start:
{
lean_object* v_r_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v_fst_100_; 
v_r_95_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss___closed__0));
v___x_96_ = lean_box(0);
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v_r_95_);
lean_ctor_set(v___x_97_, 1, v_e_94_);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_96_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0(v___x_98_);
v_fst_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_fst_100_);
if (lean_obj_tag(v_fst_100_) == 0)
{
lean_object* v_snd_101_; lean_object* v_fst_102_; 
v_snd_101_ = lean_ctor_get(v___x_99_, 1);
lean_inc(v_snd_101_);
lean_dec_ref(v___x_99_);
v_fst_102_ = lean_ctor_get(v_snd_101_, 0);
lean_inc(v_fst_102_);
lean_dec(v_snd_101_);
return v_fst_102_;
}
else
{
lean_object* v_val_103_; 
lean_dec_ref(v___x_99_);
v_val_103_ = lean_ctor_get(v_fst_100_, 0);
lean_inc(v_val_103_);
lean_dec_ref(v_fst_100_);
return v_val_103_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f_spec__0(lean_object* v_msg_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = l_Lean_instInhabitedExpr;
v___x_106_ = lean_panic_fn(v___x_105_, v_msg_104_);
return v___x_106_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__2));
v___x_111_ = lean_unsigned_to_nat(14u);
v___x_112_ = lean_unsigned_to_nat(22u);
v___x_113_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__1));
v___x_114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__0));
v___x_115_ = l_mkPanicMessageWithDecl(v___x_114_, v___x_113_, v___x_112_, v___x_111_, v___x_110_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f(lean_object* v_e_116_, lean_object* v_lhsNew_117_, lean_object* v_ty_x3f_118_){
_start:
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = l_Lean_Expr_cleanupAnnotations(v_e_116_);
v___x_120_ = l_Lean_Expr_isApp(v___x_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; 
lean_dec_ref(v___x_119_);
lean_dec(v_ty_x3f_118_);
lean_dec_ref(v_lhsNew_117_);
v___x_121_ = lean_box(0);
return v___x_121_;
}
else
{
lean_object* v_arg_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v_arg_122_ = lean_ctor_get(v___x_119_, 1);
lean_inc_ref(v_arg_122_);
v___x_123_ = l_Lean_Expr_appFnCleanup___redArg(v___x_119_);
v___x_124_ = l_Lean_Expr_isApp(v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
lean_dec_ref(v___x_123_);
lean_dec_ref(v_arg_122_);
lean_dec(v_ty_x3f_118_);
lean_dec_ref(v_lhsNew_117_);
v___x_125_ = lean_box(0);
return v___x_125_;
}
else
{
lean_object* v_arg_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v_arg_126_ = lean_ctor_get(v___x_123_, 1);
lean_inc_ref(v_arg_126_);
v___x_127_ = l_Lean_Expr_appFnCleanup___redArg(v___x_123_);
v___x_128_ = l_Lean_Expr_isApp(v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
lean_dec_ref(v___x_127_);
lean_dec_ref(v_arg_126_);
lean_dec_ref(v_arg_122_);
lean_dec(v_ty_x3f_118_);
lean_dec_ref(v_lhsNew_117_);
v___x_129_ = lean_box(0);
return v___x_129_;
}
else
{
lean_object* v_arg_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v_arg_130_ = lean_ctor_get(v___x_127_, 1);
lean_inc_ref(v_arg_130_);
v___x_131_ = l_Lean_Expr_appFnCleanup___redArg(v___x_127_);
v___x_132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1));
v___x_133_ = l_Lean_Expr_isConstOf(v___x_131_, v___x_132_);
if (v___x_133_ == 0)
{
uint8_t v___x_134_; 
v___x_134_ = l_Lean_Expr_isApp(v___x_131_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; 
lean_dec_ref(v___x_131_);
lean_dec_ref(v_arg_130_);
lean_dec_ref(v_arg_126_);
lean_dec_ref(v_arg_122_);
lean_dec(v_ty_x3f_118_);
lean_dec_ref(v_lhsNew_117_);
v___x_135_ = lean_box(0);
return v___x_135_;
}
else
{
lean_object* v___x_136_; lean_object* v___y_138_; lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_136_ = l_Lean_Expr_appFnCleanup___redArg(v___x_131_);
v___x_141_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3));
v___x_142_ = l_Lean_Expr_isConstOf(v___x_136_, v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
lean_dec_ref(v___x_136_);
lean_dec_ref(v_arg_130_);
lean_dec_ref(v_arg_126_);
lean_dec_ref(v_arg_122_);
lean_dec(v_ty_x3f_118_);
lean_dec_ref(v_lhsNew_117_);
v___x_143_ = lean_box(0);
return v___x_143_;
}
else
{
uint8_t v___x_144_; 
v___x_144_ = l_Lean_Expr_hasLooseBVars(v_arg_130_);
lean_dec_ref(v_arg_130_);
if (v___x_144_ == 0)
{
if (lean_obj_tag(v_ty_x3f_118_) == 0)
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3);
v___x_146_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f_spec__0(v___x_145_);
v___y_138_ = v___x_146_;
goto v___jp_137_;
}
else
{
lean_object* v_val_147_; 
v_val_147_ = lean_ctor_get(v_ty_x3f_118_, 0);
lean_inc(v_val_147_);
lean_dec_ref(v_ty_x3f_118_);
v___y_138_ = v_val_147_;
goto v___jp_137_;
}
}
else
{
lean_object* v___x_148_; 
lean_dec_ref(v___x_136_);
lean_dec_ref(v_arg_126_);
lean_dec_ref(v_arg_122_);
lean_dec(v_ty_x3f_118_);
lean_dec_ref(v_lhsNew_117_);
v___x_148_ = lean_box(0);
return v___x_148_;
}
}
v___jp_137_:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = l_Lean_mkApp4(v___x_136_, v___y_138_, v_lhsNew_117_, v_arg_126_, v_arg_122_);
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
return v___x_140_;
}
}
}
else
{
uint8_t v___x_149_; 
lean_dec(v_ty_x3f_118_);
v___x_149_ = l_Lean_Expr_hasLooseBVars(v_arg_126_);
lean_dec_ref(v_arg_126_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = l_Lean_mkApp3(v___x_131_, v_arg_130_, v_lhsNew_117_, v_arg_122_);
v___x_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
else
{
lean_object* v___x_152_; 
lean_dec_ref(v___x_131_);
lean_dec_ref(v_arg_130_);
lean_dec_ref(v_arg_122_);
lean_dec_ref(v_lhsNew_117_);
v___x_152_ = lean_box(0);
return v___x_152_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(lean_object* v_xs_153_, lean_object* v_tys_154_, lean_object* v_e_155_, lean_object* v_i_156_){
_start:
{
if (lean_obj_tag(v_e_155_) == 7)
{
lean_object* v_binderName_157_; lean_object* v_binderType_158_; lean_object* v_body_159_; uint8_t v_binderInfo_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v_binderName_157_ = lean_ctor_get(v_e_155_, 0);
v_binderType_158_ = lean_ctor_get(v_e_155_, 1);
v_body_159_ = lean_ctor_get(v_e_155_, 2);
v_binderInfo_160_ = lean_ctor_get_uint8(v_e_155_, sizeof(void*)*3 + 8);
v___x_161_ = lean_array_get_size(v_xs_153_);
v___x_162_ = lean_nat_dec_lt(v_i_156_, v___x_161_);
if (v___x_162_ == 0)
{
return v_e_155_;
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_163_ = lean_array_fget_borrowed(v_xs_153_, v_i_156_);
v___x_164_ = lean_box(0);
v___x_165_ = lean_array_get_borrowed(v___x_164_, v_tys_154_, v_i_156_);
lean_inc(v___x_165_);
lean_inc(v___x_163_);
lean_inc_ref(v_binderType_158_);
v___x_166_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f(v_binderType_158_, v___x_163_, v___x_165_);
if (lean_obj_tag(v___x_166_) == 1)
{
lean_object* v_val_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___y_172_; size_t v___x_176_; size_t v___x_177_; uint8_t v___x_178_; 
v_val_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_val_167_);
lean_dec_ref(v___x_166_);
v___x_168_ = lean_unsigned_to_nat(1u);
v___x_169_ = lean_nat_add(v_i_156_, v___x_168_);
lean_inc_ref(v_body_159_);
v___x_170_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_153_, v_tys_154_, v_body_159_, v___x_169_);
lean_dec(v___x_169_);
v___x_176_ = lean_ptr_addr(v_binderType_158_);
v___x_177_ = lean_ptr_addr(v_val_167_);
v___x_178_ = lean_usize_dec_eq(v___x_176_, v___x_177_);
if (v___x_178_ == 0)
{
v___y_172_ = v___x_178_;
goto v___jp_171_;
}
else
{
size_t v___x_179_; size_t v___x_180_; uint8_t v___x_181_; 
v___x_179_ = lean_ptr_addr(v_body_159_);
v___x_180_ = lean_ptr_addr(v___x_170_);
v___x_181_ = lean_usize_dec_eq(v___x_179_, v___x_180_);
v___y_172_ = v___x_181_;
goto v___jp_171_;
}
v___jp_171_:
{
if (v___y_172_ == 0)
{
lean_object* v___x_173_; 
lean_inc(v_binderName_157_);
lean_dec_ref(v_e_155_);
v___x_173_ = l_Lean_Expr_forallE___override(v_binderName_157_, v_val_167_, v___x_170_, v_binderInfo_160_);
return v___x_173_;
}
else
{
uint8_t v___x_174_; 
v___x_174_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_160_, v_binderInfo_160_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
lean_inc(v_binderName_157_);
lean_dec_ref(v_e_155_);
v___x_175_ = l_Lean_Expr_forallE___override(v_binderName_157_, v_val_167_, v___x_170_, v_binderInfo_160_);
return v___x_175_;
}
else
{
lean_dec_ref(v___x_170_);
lean_dec(v_val_167_);
return v_e_155_;
}
}
}
}
else
{
lean_object* v___x_182_; uint8_t v___y_184_; size_t v___x_188_; uint8_t v___x_189_; 
lean_dec(v___x_166_);
lean_inc_ref(v_body_159_);
v___x_182_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_153_, v_tys_154_, v_body_159_, v_i_156_);
v___x_188_ = lean_ptr_addr(v_binderType_158_);
v___x_189_ = lean_usize_dec_eq(v___x_188_, v___x_188_);
if (v___x_189_ == 0)
{
v___y_184_ = v___x_189_;
goto v___jp_183_;
}
else
{
size_t v___x_190_; size_t v___x_191_; uint8_t v___x_192_; 
v___x_190_ = lean_ptr_addr(v_body_159_);
v___x_191_ = lean_ptr_addr(v___x_182_);
v___x_192_ = lean_usize_dec_eq(v___x_190_, v___x_191_);
v___y_184_ = v___x_192_;
goto v___jp_183_;
}
v___jp_183_:
{
if (v___y_184_ == 0)
{
lean_object* v___x_185_; 
lean_inc_ref(v_binderType_158_);
lean_inc(v_binderName_157_);
lean_dec_ref(v_e_155_);
v___x_185_ = l_Lean_Expr_forallE___override(v_binderName_157_, v_binderType_158_, v___x_182_, v_binderInfo_160_);
return v___x_185_;
}
else
{
uint8_t v___x_186_; 
v___x_186_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_160_, v_binderInfo_160_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
lean_inc_ref(v_binderType_158_);
lean_inc(v_binderName_157_);
lean_dec_ref(v_e_155_);
v___x_187_ = l_Lean_Expr_forallE___override(v_binderName_157_, v_binderType_158_, v___x_182_, v_binderInfo_160_);
return v___x_187_;
}
else
{
lean_dec_ref(v___x_182_);
return v_e_155_;
}
}
}
}
}
}
else
{
return v_e_155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss___boxed(lean_object* v_xs_193_, lean_object* v_tys_194_, lean_object* v_e_195_, lean_object* v_i_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_193_, v_tys_194_, v_e_195_, v_i_196_);
lean_dec(v_i_196_);
lean_dec_ref(v_tys_194_);
lean_dec_ref(v_xs_193_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0(lean_object* v_k_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v_b_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = lean_apply_12(v_k_198_, v_b_205_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, lean_box(0));
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v_b_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0(v_k_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v_b_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(lean_object* v_name_226_, uint8_t v_bi_227_, lean_object* v_type_228_, lean_object* v_k_229_, uint8_t v_kind_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v___f_242_; lean_object* v___x_243_; 
v___f_242_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_242_, 0, v_k_229_);
lean_closure_set(v___f_242_, 1, v___y_231_);
lean_closure_set(v___f_242_, 2, v___y_232_);
lean_closure_set(v___f_242_, 3, v___y_233_);
lean_closure_set(v___f_242_, 4, v___y_234_);
lean_closure_set(v___f_242_, 5, v___y_235_);
lean_closure_set(v___f_242_, 6, v___y_236_);
v___x_243_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_226_, v_bi_227_, v_type_228_, v___f_242_, v_kind_230_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
if (lean_obj_tag(v___x_243_) == 0)
{
return v___x_243_;
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___boxed(lean_object* v_name_252_, lean_object* v_bi_253_, lean_object* v_type_254_, lean_object* v_k_255_, lean_object* v_kind_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
uint8_t v_bi_boxed_268_; uint8_t v_kind_boxed_269_; lean_object* v_res_270_; 
v_bi_boxed_268_ = lean_unbox(v_bi_253_);
v_kind_boxed_269_ = lean_unbox(v_kind_256_);
v_res_270_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_252_, v_bi_boxed_268_, v_type_254_, v_k_255_, v_kind_boxed_269_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(lean_object* v_name_271_, lean_object* v_type_272_, lean_object* v_k_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
uint8_t v___x_285_; uint8_t v___x_286_; lean_object* v___x_287_; 
v___x_285_ = 0;
v___x_286_ = 0;
v___x_287_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_271_, v___x_285_, v_type_272_, v_k_273_, v___x_286_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg___boxed(lean_object* v_name_288_, lean_object* v_type_289_, lean_object* v_k_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v_name_288_, v_type_289_, v_k_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed(lean_object** _args){
lean_object* v_i_306_ = _args[0];
lean_object* v_xs_307_ = _args[1];
lean_object* v_tys_308_ = _args[2];
lean_object* v_tysxs_309_ = _args[3];
lean_object* v_args_310_ = _args[4];
lean_object* v_val_311_ = _args[5];
lean_object* v_fst_312_ = _args[6];
lean_object* v_e_313_ = _args[7];
lean_object* v_lhss_u03b1s_314_ = _args[8];
lean_object* v_ty_315_ = _args[9];
lean_object* v___y_316_ = _args[10];
lean_object* v___y_317_ = _args[11];
lean_object* v___y_318_ = _args[12];
lean_object* v___y_319_ = _args[13];
lean_object* v___y_320_ = _args[14];
lean_object* v___y_321_ = _args[15];
lean_object* v___y_322_ = _args[16];
lean_object* v___y_323_ = _args[17];
lean_object* v___y_324_ = _args[18];
lean_object* v___y_325_ = _args[19];
lean_object* v___y_326_ = _args[20];
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(v_i_306_, v_xs_307_, v_tys_308_, v_tysxs_309_, v_args_310_, v_val_311_, v_fst_312_, v_e_313_, v_lhss_u03b1s_314_, v_ty_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(lean_object* v_i_331_, lean_object* v_xs_332_, lean_object* v_tys_333_, lean_object* v_tysxs_334_, lean_object* v_args_335_, lean_object* v_fst_336_, lean_object* v_e_337_, lean_object* v_lhss_u03b1s_338_, lean_object* v_x_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_351_ = lean_unsigned_to_nat(1u);
v___x_352_ = lean_nat_add(v_i_331_, v___x_351_);
lean_inc_ref(v_x_339_);
v___x_353_ = lean_array_push(v_xs_332_, v_x_339_);
v___x_354_ = lean_box(0);
v___x_355_ = lean_array_push(v_tys_333_, v___x_354_);
v___x_356_ = lean_array_push(v_tysxs_334_, v_x_339_);
v___x_357_ = lean_array_push(v_args_335_, v_fst_336_);
v___x_358_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_337_, v_lhss_u03b1s_338_, v___x_352_, v___x_353_, v___x_355_, v___x_356_, v___x_357_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed(lean_object** _args){
lean_object* v_i_359_ = _args[0];
lean_object* v_xs_360_ = _args[1];
lean_object* v_tys_361_ = _args[2];
lean_object* v_tysxs_362_ = _args[3];
lean_object* v_args_363_ = _args[4];
lean_object* v_fst_364_ = _args[5];
lean_object* v_e_365_ = _args[6];
lean_object* v_lhss_u03b1s_366_ = _args[7];
lean_object* v_x_367_ = _args[8];
lean_object* v___y_368_ = _args[9];
lean_object* v___y_369_ = _args[10];
lean_object* v___y_370_ = _args[11];
lean_object* v___y_371_ = _args[12];
lean_object* v___y_372_ = _args[13];
lean_object* v___y_373_ = _args[14];
lean_object* v___y_374_ = _args[15];
lean_object* v___y_375_ = _args[16];
lean_object* v___y_376_ = _args[17];
lean_object* v___y_377_ = _args[18];
lean_object* v___y_378_ = _args[19];
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(v_i_359_, v_xs_360_, v_tys_361_, v_tysxs_362_, v_args_363_, v_fst_364_, v_e_365_, v_lhss_u03b1s_366_, v_x_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v_i_359_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(lean_object* v_e_380_, lean_object* v_lhss_u03b1s_381_, lean_object* v_i_382_, lean_object* v_xs_383_, lean_object* v_tys_384_, lean_object* v_tysxs_385_, lean_object* v_args_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_398_ = lean_array_get_size(v_lhss_u03b1s_381_);
v___x_399_ = lean_nat_dec_lt(v_i_382_, v___x_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v_eAbst_401_; uint8_t v___x_402_; uint8_t v___x_403_; lean_object* v___x_404_; 
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec(v_a_387_);
lean_dec(v_i_382_);
lean_dec_ref(v_lhss_u03b1s_381_);
v___x_400_ = lean_unsigned_to_nat(0u);
v_eAbst_401_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_383_, v_tys_384_, v_e_380_, v___x_400_);
lean_dec_ref(v_tys_384_);
lean_dec_ref(v_xs_383_);
v___x_402_ = 1;
v___x_403_ = 1;
v___x_404_ = l_Lean_Meta_mkLambdaFVars(v_tysxs_385_, v_eAbst_401_, v___x_399_, v___x_402_, v___x_399_, v___x_402_, v___x_403_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec_ref(v_tysxs_385_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
lean_dec_ref(v___x_404_);
v___x_406_ = l_Lean_mkAppN(v_a_405_, v_args_386_);
v___x_407_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_406_, v_a_392_);
lean_dec(v_a_392_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_416_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_416_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_416_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_416_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v_args_386_);
lean_ctor_set(v___x_412_, 1, v_a_408_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_412_);
v___x_414_ = v___x_410_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec_ref(v_args_386_);
v_a_417_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_407_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_407_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
else
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
lean_dec(v_a_392_);
lean_dec_ref(v_args_386_);
v_a_425_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_404_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_404_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
else
{
lean_object* v___x_433_; lean_object* v_snd_434_; 
v___x_433_ = lean_array_fget_borrowed(v_lhss_u03b1s_381_, v_i_382_);
v_snd_434_ = lean_ctor_get(v___x_433_, 1);
if (lean_obj_tag(v_snd_434_) == 1)
{
lean_object* v_fst_435_; lean_object* v_val_436_; lean_object* v___x_437_; 
v_fst_435_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_fst_435_);
v_val_436_ = lean_ctor_get(v_snd_434_, 0);
lean_inc(v_val_436_);
lean_inc(v_a_396_);
lean_inc_ref(v_a_395_);
lean_inc(v_a_394_);
lean_inc_ref(v_a_393_);
lean_inc(v_val_436_);
v___x_437_ = lean_infer_type(v_val_436_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___f_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref(v___x_437_);
lean_inc(v_i_382_);
v___f_439_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed), 21, 9);
lean_closure_set(v___f_439_, 0, v_i_382_);
lean_closure_set(v___f_439_, 1, v_xs_383_);
lean_closure_set(v___f_439_, 2, v_tys_384_);
lean_closure_set(v___f_439_, 3, v_tysxs_385_);
lean_closure_set(v___f_439_, 4, v_args_386_);
lean_closure_set(v___f_439_, 5, v_val_436_);
lean_closure_set(v___f_439_, 6, v_fst_435_);
lean_closure_set(v___f_439_, 7, v_e_380_);
lean_closure_set(v___f_439_, 8, v_lhss_u03b1s_381_);
v___x_440_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__1));
v___x_441_ = lean_name_append_index_after(v___x_440_, v_i_382_);
v___x_442_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v___x_441_, v_a_438_, v___f_439_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
return v___x_442_;
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec(v_val_436_);
lean_dec(v_fst_435_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_args_386_);
lean_dec_ref(v_tysxs_385_);
lean_dec_ref(v_tys_384_);
lean_dec_ref(v_xs_383_);
lean_dec(v_i_382_);
lean_dec_ref(v_lhss_u03b1s_381_);
lean_dec_ref(v_e_380_);
v_a_443_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_437_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_437_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
else
{
lean_object* v_fst_451_; lean_object* v___x_452_; 
v_fst_451_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_fst_451_);
lean_inc(v_a_396_);
lean_inc_ref(v_a_395_);
lean_inc(v_a_394_);
lean_inc_ref(v_a_393_);
lean_inc(v_fst_451_);
v___x_452_ = lean_infer_type(v_fst_451_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; lean_object* v___f_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_a_453_);
lean_dec_ref(v___x_452_);
lean_inc(v_i_382_);
v___f_454_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed), 20, 8);
lean_closure_set(v___f_454_, 0, v_i_382_);
lean_closure_set(v___f_454_, 1, v_xs_383_);
lean_closure_set(v___f_454_, 2, v_tys_384_);
lean_closure_set(v___f_454_, 3, v_tysxs_385_);
lean_closure_set(v___f_454_, 4, v_args_386_);
lean_closure_set(v___f_454_, 5, v_fst_451_);
lean_closure_set(v___f_454_, 6, v_e_380_);
lean_closure_set(v___f_454_, 7, v_lhss_u03b1s_381_);
v___x_455_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1));
v___x_456_ = lean_name_append_index_after(v___x_455_, v_i_382_);
v___x_457_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v___x_456_, v_a_453_, v___f_454_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
return v___x_457_;
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
lean_dec(v_fst_451_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_args_386_);
lean_dec_ref(v_tysxs_385_);
lean_dec_ref(v_tys_384_);
lean_dec_ref(v_xs_383_);
lean_dec(v_i_382_);
lean_dec_ref(v_lhss_u03b1s_381_);
lean_dec_ref(v_e_380_);
v_a_458_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_452_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_452_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(lean_object* v_i_466_, lean_object* v_xs_467_, lean_object* v_ty_468_, lean_object* v_tys_469_, lean_object* v_tysxs_470_, lean_object* v_args_471_, lean_object* v_val_472_, lean_object* v_fst_473_, lean_object* v_e_474_, lean_object* v_lhss_u03b1s_475_, lean_object* v_x_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = lean_nat_add(v_i_466_, v___x_488_);
lean_inc_ref(v_x_476_);
v___x_490_ = lean_array_push(v_xs_467_, v_x_476_);
lean_inc_ref(v_ty_468_);
v___x_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_491_, 0, v_ty_468_);
v___x_492_ = lean_array_push(v_tys_469_, v___x_491_);
v___x_493_ = lean_array_push(v_tysxs_470_, v_ty_468_);
v___x_494_ = lean_array_push(v___x_493_, v_x_476_);
v___x_495_ = lean_array_push(v_args_471_, v_val_472_);
v___x_496_ = lean_array_push(v___x_495_, v_fst_473_);
v___x_497_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_474_, v_lhss_u03b1s_475_, v___x_489_, v___x_490_, v___x_492_, v___x_494_, v___x_496_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0___boxed(lean_object** _args){
lean_object* v_i_498_ = _args[0];
lean_object* v_xs_499_ = _args[1];
lean_object* v_ty_500_ = _args[2];
lean_object* v_tys_501_ = _args[3];
lean_object* v_tysxs_502_ = _args[4];
lean_object* v_args_503_ = _args[5];
lean_object* v_val_504_ = _args[6];
lean_object* v_fst_505_ = _args[7];
lean_object* v_e_506_ = _args[8];
lean_object* v_lhss_u03b1s_507_ = _args[9];
lean_object* v_x_508_ = _args[10];
lean_object* v___y_509_ = _args[11];
lean_object* v___y_510_ = _args[12];
lean_object* v___y_511_ = _args[13];
lean_object* v___y_512_ = _args[14];
lean_object* v___y_513_ = _args[15];
lean_object* v___y_514_ = _args[16];
lean_object* v___y_515_ = _args[17];
lean_object* v___y_516_ = _args[18];
lean_object* v___y_517_ = _args[19];
lean_object* v___y_518_ = _args[20];
lean_object* v___y_519_ = _args[21];
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(v_i_498_, v_xs_499_, v_ty_500_, v_tys_501_, v_tysxs_502_, v_args_503_, v_val_504_, v_fst_505_, v_e_506_, v_lhss_u03b1s_507_, v_x_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v_i_498_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(lean_object* v_i_521_, lean_object* v_xs_522_, lean_object* v_tys_523_, lean_object* v_tysxs_524_, lean_object* v_args_525_, lean_object* v_val_526_, lean_object* v_fst_527_, lean_object* v_e_528_, lean_object* v_lhss_u03b1s_529_, lean_object* v_ty_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v___f_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
lean_inc_ref(v_ty_530_);
lean_inc(v_i_521_);
v___f_542_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0___boxed), 22, 10);
lean_closure_set(v___f_542_, 0, v_i_521_);
lean_closure_set(v___f_542_, 1, v_xs_522_);
lean_closure_set(v___f_542_, 2, v_ty_530_);
lean_closure_set(v___f_542_, 3, v_tys_523_);
lean_closure_set(v___f_542_, 4, v_tysxs_524_);
lean_closure_set(v___f_542_, 5, v_args_525_);
lean_closure_set(v___f_542_, 6, v_val_526_);
lean_closure_set(v___f_542_, 7, v_fst_527_);
lean_closure_set(v___f_542_, 8, v_e_528_);
lean_closure_set(v___f_542_, 9, v_lhss_u03b1s_529_);
v___x_543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1));
v___x_544_ = lean_name_append_index_after(v___x_543_, v_i_521_);
v___x_545_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v___x_544_, v_ty_530_, v___f_542_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___boxed(lean_object** _args){
lean_object* v_e_546_ = _args[0];
lean_object* v_lhss_u03b1s_547_ = _args[1];
lean_object* v_i_548_ = _args[2];
lean_object* v_xs_549_ = _args[3];
lean_object* v_tys_550_ = _args[4];
lean_object* v_tysxs_551_ = _args[5];
lean_object* v_args_552_ = _args[6];
lean_object* v_a_553_ = _args[7];
lean_object* v_a_554_ = _args[8];
lean_object* v_a_555_ = _args[9];
lean_object* v_a_556_ = _args[10];
lean_object* v_a_557_ = _args[11];
lean_object* v_a_558_ = _args[12];
lean_object* v_a_559_ = _args[13];
lean_object* v_a_560_ = _args[14];
lean_object* v_a_561_ = _args[15];
lean_object* v_a_562_ = _args[16];
lean_object* v_a_563_ = _args[17];
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_546_, v_lhss_u03b1s_547_, v_i_548_, v_xs_549_, v_tys_550_, v_tysxs_551_, v_args_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0(lean_object* v_00_u03b1_565_, lean_object* v_name_566_, uint8_t v_bi_567_, lean_object* v_type_568_, lean_object* v_k_569_, uint8_t v_kind_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_566_, v_bi_567_, v_type_568_, v_k_569_, v_kind_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_583_ = _args[0];
lean_object* v_name_584_ = _args[1];
lean_object* v_bi_585_ = _args[2];
lean_object* v_type_586_ = _args[3];
lean_object* v_k_587_ = _args[4];
lean_object* v_kind_588_ = _args[5];
lean_object* v___y_589_ = _args[6];
lean_object* v___y_590_ = _args[7];
lean_object* v___y_591_ = _args[8];
lean_object* v___y_592_ = _args[9];
lean_object* v___y_593_ = _args[10];
lean_object* v___y_594_ = _args[11];
lean_object* v___y_595_ = _args[12];
lean_object* v___y_596_ = _args[13];
lean_object* v___y_597_ = _args[14];
lean_object* v___y_598_ = _args[15];
lean_object* v___y_599_ = _args[16];
_start:
{
uint8_t v_bi_boxed_600_; uint8_t v_kind_boxed_601_; lean_object* v_res_602_; 
v_bi_boxed_600_ = lean_unbox(v_bi_585_);
v_kind_boxed_601_ = lean_unbox(v_kind_588_);
v_res_602_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0(v_00_u03b1_583_, v_name_584_, v_bi_boxed_600_, v_type_586_, v_k_587_, v_kind_boxed_601_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0(lean_object* v_00_u03b1_603_, lean_object* v_name_604_, lean_object* v_type_605_, lean_object* v_k_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v_name_604_, v_type_605_, v_k_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___boxed(lean_object* v_00_u03b1_619_, lean_object* v_name_620_, lean_object* v_type_621_, lean_object* v_k_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0(v_00_u03b1_619_, v_name_620_, v_type_621_, v_k_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter___redArg(lean_object* v_x_635_, lean_object* v_h__1_636_){
_start:
{
lean_object* v_fst_637_; lean_object* v_snd_638_; lean_object* v___x_639_; 
v_fst_637_ = lean_ctor_get(v_x_635_, 0);
lean_inc(v_fst_637_);
v_snd_638_ = lean_ctor_get(v_x_635_, 1);
lean_inc(v_snd_638_);
lean_dec_ref(v_x_635_);
v___x_639_ = lean_apply_2(v_h__1_636_, v_fst_637_, v_snd_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter(lean_object* v_motive_640_, lean_object* v_x_641_, lean_object* v_h__1_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter___redArg(v_x_641_, v_h__1_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter___redArg(lean_object* v_00_u03b1_x3f_644_, lean_object* v_h__1_645_, lean_object* v_h__2_646_){
_start:
{
if (lean_obj_tag(v_00_u03b1_x3f_644_) == 1)
{
lean_object* v_val_647_; lean_object* v___x_648_; 
lean_dec(v_h__2_646_);
v_val_647_ = lean_ctor_get(v_00_u03b1_x3f_644_, 0);
lean_inc(v_val_647_);
lean_dec_ref(v_00_u03b1_x3f_644_);
v___x_648_ = lean_apply_1(v_h__1_645_, v_val_647_);
return v___x_648_;
}
else
{
lean_object* v___x_649_; 
lean_dec(v_h__1_645_);
v___x_649_ = lean_apply_2(v_h__2_646_, v_00_u03b1_x3f_644_, lean_box(0));
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter(lean_object* v_motive_650_, lean_object* v_00_u03b1_x3f_651_, lean_object* v_h__1_652_, lean_object* v_h__2_653_){
_start:
{
if (lean_obj_tag(v_00_u03b1_x3f_651_) == 1)
{
lean_object* v_val_654_; lean_object* v___x_655_; 
lean_dec(v_h__2_653_);
v_val_654_ = lean_ctor_get(v_00_u03b1_x3f_651_, 0);
lean_inc(v_val_654_);
lean_dec_ref(v_00_u03b1_x3f_651_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(lean_object* v_matchCond_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v___x_682_; uint8_t v___x_683_; 
lean_inc_ref(v_matchCond_666_);
v___x_682_ = l_Lean_Expr_cleanupAnnotations(v_matchCond_666_);
v___x_683_ = l_Lean_Expr_isApp(v___x_682_);
if (v___x_683_ == 0)
{
lean_dec_ref(v___x_682_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec(v_a_668_);
lean_dec(v_a_667_);
goto v___jp_678_;
}
else
{
lean_object* v_arg_684_; lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v_arg_684_ = lean_ctor_get(v___x_682_, 1);
lean_inc_ref(v_arg_684_);
v___x_685_ = l_Lean_Expr_appFnCleanup___redArg(v___x_682_);
v___x_686_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_687_ = l_Lean_Expr_isConstOf(v___x_685_, v___x_686_);
lean_dec_ref(v___x_685_);
if (v___x_687_ == 0)
{
lean_dec_ref(v_arg_684_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec(v_a_668_);
lean_dec(v_a_667_);
goto v___jp_678_;
}
else
{
lean_object* v_lhss_u03b1s_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
lean_dec_ref(v_matchCond_666_);
lean_inc_ref(v_arg_684_);
v_lhss_u03b1s_688_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss(v_arg_684_);
v___x_689_ = lean_unsigned_to_nat(0u);
v___x_690_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0));
v___x_691_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_arg_684_, v_lhss_u03b1s_688_, v___x_689_, v___x_690_, v___x_690_, v___x_690_, v___x_690_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
return v___x_691_;
}
}
v___jp_678_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_679_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0));
v___x_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
lean_ctor_set(v___x_680_, 1, v_matchCond_666_);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
return v___x_681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___boxed(lean_object* v_matchCond_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(v_matchCond_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_);
return v_res_704_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0(void){
_start:
{
lean_object* v___x_708_; lean_object* v_dummy_709_; 
v___x_708_ = lean_box(0);
v_dummy_709_ = l_Lean_Expr_sort___override(v___x_708_);
return v_dummy_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(lean_object* v_lhs_710_, lean_object* v_rhs_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
uint8_t v___x_723_; 
v___x_723_ = l_Lean_Expr_hasLooseBVars(v_lhs_710_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_Meta_Grind_getRootENode___redArg(v_lhs_710_, v_a_712_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_865_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_865_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_865_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_865_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
uint8_t v_ctor_729_; 
v_ctor_729_ = lean_ctor_get_uint8(v_a_725_, sizeof(void*)*11 + 2);
if (v_ctor_729_ == 0)
{
uint8_t v_interpreted_730_; 
v_interpreted_730_ = lean_ctor_get_uint8(v_a_725_, sizeof(void*)*11 + 1);
if (v_interpreted_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___x_733_; 
lean_dec(v_a_725_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec_ref(v_rhs_711_);
v___x_731_ = lean_box(v_interpreted_730_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_731_);
v___x_733_ = v___x_727_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
else
{
lean_object* v_self_735_; uint8_t v___x_736_; 
v_self_735_ = lean_ctor_get(v_a_725_, 0);
lean_inc_ref(v_self_735_);
lean_dec(v_a_725_);
v___x_736_ = l_Lean_Expr_hasLooseBVars(v_rhs_711_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
lean_del_object(v___x_727_);
lean_inc(v_a_721_);
lean_inc_ref(v_a_720_);
lean_inc(v_a_719_);
lean_inc_ref(v_a_718_);
lean_inc_ref(v_rhs_711_);
v___x_737_ = l_Lean_Meta_isLitValue(v_rhs_711_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; uint8_t v___x_739_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
v___x_739_ = lean_unbox(v_a_738_);
if (v___x_739_ == 0)
{
lean_dec(v_a_738_);
lean_dec_ref(v_self_735_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec_ref(v_rhs_711_);
return v___x_737_;
}
else
{
lean_object* v___x_740_; 
lean_dec_ref(v___x_737_);
lean_inc(v_a_721_);
lean_inc_ref(v_a_720_);
lean_inc(v_a_719_);
lean_inc_ref(v_a_718_);
v___x_740_ = l_Lean_Meta_normLitValue(v_self_735_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_742_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref(v___x_740_);
v___x_742_ = l_Lean_Meta_normLitValue(v_rhs_711_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_755_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_755_ == 0)
{
v___x_745_ = v___x_742_;
v_isShared_746_ = v_isSharedCheck_755_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_742_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_755_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
uint8_t v___x_747_; 
v___x_747_ = lean_expr_eqv(v_a_741_, v_a_743_);
lean_dec(v_a_743_);
lean_dec(v_a_741_);
if (v___x_747_ == 0)
{
lean_object* v___x_749_; 
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v_a_738_);
v___x_749_ = v___x_745_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_738_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
else
{
lean_object* v___x_751_; lean_object* v___x_753_; 
lean_dec(v_a_738_);
v___x_751_ = lean_box(v___x_736_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_751_);
v___x_753_ = v___x_745_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v_a_741_);
lean_dec(v_a_738_);
v_a_756_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_742_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_742_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
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
lean_dec(v_a_738_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec_ref(v_rhs_711_);
v_a_764_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_740_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_740_);
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
}
else
{
lean_dec_ref(v_self_735_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec_ref(v_rhs_711_);
return v___x_737_;
}
}
else
{
lean_object* v___x_772_; lean_object* v___x_774_; 
lean_dec_ref(v_self_735_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec_ref(v_rhs_711_);
v___x_772_ = lean_box(v_ctor_729_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_772_);
v___x_774_ = v___x_727_;
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
}
else
{
lean_object* v_self_776_; lean_object* v___x_777_; 
lean_del_object(v___x_727_);
v_self_776_ = lean_ctor_get(v_a_725_, 0);
lean_inc_ref(v_self_776_);
lean_dec(v_a_725_);
lean_inc(v_a_721_);
lean_inc_ref(v_a_720_);
lean_inc(v_a_719_);
lean_inc_ref(v_a_718_);
lean_inc_ref(v_self_776_);
v___x_777_ = l_Lean_Meta_isConstructorApp_x3f(v_self_776_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_856_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_856_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_856_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_856_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
if (lean_obj_tag(v_a_778_) == 1)
{
lean_object* v_val_782_; lean_object* v___x_783_; 
lean_del_object(v___x_780_);
v_val_782_ = lean_ctor_get(v_a_778_, 0);
lean_inc(v_val_782_);
lean_dec_ref(v_a_778_);
lean_inc(v_a_721_);
lean_inc_ref(v_a_720_);
lean_inc(v_a_719_);
lean_inc_ref(v_a_718_);
lean_inc_ref(v_rhs_711_);
v___x_783_ = l_Lean_Meta_isConstructorApp_x3f(v_rhs_711_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_843_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_843_ == 0)
{
v___x_786_ = v___x_783_;
v_isShared_787_ = v_isSharedCheck_843_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_783_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_843_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
if (lean_obj_tag(v_a_784_) == 1)
{
lean_object* v_toConstantVal_788_; lean_object* v_val_789_; lean_object* v_toConstantVal_790_; lean_object* v_numParams_791_; lean_object* v_numFields_792_; lean_object* v_name_793_; lean_object* v_name_794_; uint8_t v___x_795_; 
v_toConstantVal_788_ = lean_ctor_get(v_val_782_, 0);
lean_inc_ref(v_toConstantVal_788_);
v_val_789_ = lean_ctor_get(v_a_784_, 0);
lean_inc(v_val_789_);
lean_dec_ref(v_a_784_);
v_toConstantVal_790_ = lean_ctor_get(v_val_789_, 0);
lean_inc_ref(v_toConstantVal_790_);
lean_dec(v_val_789_);
v_numParams_791_ = lean_ctor_get(v_val_782_, 3);
lean_inc(v_numParams_791_);
v_numFields_792_ = lean_ctor_get(v_val_782_, 4);
lean_inc(v_numFields_792_);
lean_dec(v_val_782_);
v_name_793_ = lean_ctor_get(v_toConstantVal_788_, 0);
lean_inc(v_name_793_);
lean_dec_ref(v_toConstantVal_788_);
v_name_794_ = lean_ctor_get(v_toConstantVal_790_, 0);
lean_inc(v_name_794_);
lean_dec_ref(v_toConstantVal_790_);
v___x_795_ = lean_name_eq(v_name_793_, v_name_794_);
lean_dec(v_name_794_);
lean_dec(v_name_793_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_798_; 
lean_dec(v_numFields_792_);
lean_dec(v_numParams_791_);
lean_dec_ref(v_self_776_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec_ref(v_rhs_711_);
v___x_796_ = lean_box(v_ctor_729_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_796_);
v___x_798_ = v___x_786_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
else
{
if (v___x_723_ == 0)
{
lean_object* v_nargs_800_; lean_object* v_nargs_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v_dummy_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
lean_del_object(v___x_786_);
v_nargs_800_ = l_Lean_Expr_getAppNumArgs(v_self_776_);
v_nargs_801_ = l_Lean_Expr_getAppNumArgs(v_rhs_711_);
v___x_802_ = lean_nat_add(v_numParams_791_, v_numFields_792_);
lean_dec(v_numFields_792_);
v___x_803_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0));
v_dummy_804_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0);
lean_inc(v_nargs_800_);
v___x_805_ = lean_mk_array(v_nargs_800_, v_dummy_804_);
v___x_806_ = lean_unsigned_to_nat(1u);
v___x_807_ = lean_nat_sub(v_nargs_800_, v___x_806_);
lean_dec(v_nargs_800_);
v___x_808_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_776_, v___x_805_, v___x_807_);
lean_inc(v_nargs_801_);
v___x_809_ = lean_mk_array(v_nargs_801_, v_dummy_804_);
v___x_810_ = lean_nat_sub(v_nargs_801_, v___x_806_);
lean_dec(v_nargs_801_);
v___x_811_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_rhs_711_, v___x_809_, v___x_810_);
v___x_812_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v___x_802_, v___x_808_, v___x_811_, v_ctor_729_, v_numParams_791_, v___x_803_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
lean_dec_ref(v___x_811_);
lean_dec_ref(v___x_808_);
lean_dec(v___x_802_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_826_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_826_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_826_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_826_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v_fst_817_; 
v_fst_817_ = lean_ctor_get(v_a_813_, 0);
lean_inc(v_fst_817_);
lean_dec(v_a_813_);
if (lean_obj_tag(v_fst_817_) == 0)
{
lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_818_ = lean_box(v___x_723_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_818_);
v___x_820_ = v___x_815_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
else
{
lean_object* v_val_822_; lean_object* v___x_824_; 
v_val_822_ = lean_ctor_get(v_fst_817_, 0);
lean_inc(v_val_822_);
lean_dec_ref(v_fst_817_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v_val_822_);
v___x_824_ = v___x_815_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_val_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
v_a_827_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_812_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_812_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
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
lean_object* v___x_835_; lean_object* v___x_837_; 
lean_dec(v_numFields_792_);
lean_dec(v_numParams_791_);
lean_dec_ref(v_self_776_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec_ref(v_rhs_711_);
v___x_835_ = lean_box(v_ctor_729_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_835_);
v___x_837_ = v___x_786_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_object* v___x_839_; lean_object* v___x_841_; 
lean_dec(v_a_784_);
lean_dec(v_val_782_);
lean_dec_ref(v_self_776_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec_ref(v_rhs_711_);
v___x_839_ = lean_box(v___x_723_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_839_);
v___x_841_ = v___x_786_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
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
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec(v_val_782_);
lean_dec_ref(v_self_776_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec_ref(v_rhs_711_);
v_a_844_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_783_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_783_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
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
lean_object* v___x_852_; lean_object* v___x_854_; 
lean_dec(v_a_778_);
lean_dec_ref(v_self_776_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec_ref(v_rhs_711_);
v___x_852_ = lean_box(v___x_723_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_852_);
v___x_854_ = v___x_780_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_dec_ref(v_self_776_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec_ref(v_rhs_711_);
v_a_857_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_777_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_777_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
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
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec_ref(v_rhs_711_);
v_a_866_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_724_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_724_);
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
else
{
uint8_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec_ref(v_rhs_711_);
lean_dec_ref(v_lhs_710_);
v___x_874_ = 0;
v___x_875_ = lean_box(v___x_874_);
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
return v___x_876_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(lean_object* v_upperBound_877_, lean_object* v___x_878_, lean_object* v___x_879_, uint8_t v___x_880_, lean_object* v_a_881_, lean_object* v_b_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
uint8_t v___x_894_; 
v___x_894_ = lean_nat_dec_lt(v_a_881_, v_upperBound_877_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; 
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v_a_881_);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v_b_882_);
return v___x_895_;
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec_ref(v_b_882_);
v___x_896_ = l_Lean_instInhabitedExpr;
v___x_897_ = lean_array_get_borrowed(v___x_896_, v___x_878_, v_a_881_);
v___x_898_ = lean_array_get_borrowed(v___x_896_, v___x_879_, v_a_881_);
lean_inc(v___y_892_);
lean_inc_ref(v___y_891_);
lean_inc(v___y_890_);
lean_inc_ref(v___y_889_);
lean_inc(v___x_898_);
lean_inc(v___x_897_);
v___x_899_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v___x_897_, v___x_898_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_916_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_916_ == 0)
{
v___x_902_ = v___x_899_;
v_isShared_903_ = v_isSharedCheck_916_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_899_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_916_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = lean_box(0);
v___x_905_ = lean_unbox(v_a_900_);
lean_dec(v_a_900_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
lean_del_object(v___x_902_);
v___x_906_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0));
v___x_907_ = lean_unsigned_to_nat(1u);
v___x_908_ = lean_nat_add(v_a_881_, v___x_907_);
lean_dec(v_a_881_);
v_a_881_ = v___x_908_;
v_b_882_ = v___x_906_;
goto _start;
}
else
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v_a_881_);
v___x_910_ = lean_box(v___x_880_);
v___x_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v___x_904_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v___x_912_);
v___x_914_ = v___x_902_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v_a_881_);
v_a_917_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_899_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_899_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_925_ = _args[0];
lean_object* v___x_926_ = _args[1];
lean_object* v___x_927_ = _args[2];
lean_object* v___x_928_ = _args[3];
lean_object* v_a_929_ = _args[4];
lean_object* v_b_930_ = _args[5];
lean_object* v___y_931_ = _args[6];
lean_object* v___y_932_ = _args[7];
lean_object* v___y_933_ = _args[8];
lean_object* v___y_934_ = _args[9];
lean_object* v___y_935_ = _args[10];
lean_object* v___y_936_ = _args[11];
lean_object* v___y_937_ = _args[12];
lean_object* v___y_938_ = _args[13];
lean_object* v___y_939_ = _args[14];
lean_object* v___y_940_ = _args[15];
lean_object* v___y_941_ = _args[16];
_start:
{
uint8_t v___x_30307__boxed_942_; lean_object* v_res_943_; 
v___x_30307__boxed_942_ = lean_unbox(v___x_928_);
v_res_943_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v_upperBound_925_, v___x_926_, v___x_927_, v___x_30307__boxed_942_, v_a_929_, v_b_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___x_927_);
lean_dec_ref(v___x_926_);
lean_dec(v_upperBound_925_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___boxed(lean_object* v_lhs_944_, lean_object* v_rhs_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v_lhs_944_, v_rhs_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
lean_dec(v_a_946_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(lean_object* v_upperBound_958_, lean_object* v___x_959_, lean_object* v___x_960_, uint8_t v___x_961_, lean_object* v_inst_962_, lean_object* v_R_963_, lean_object* v_a_964_, lean_object* v_b_965_, lean_object* v_c_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v_upperBound_958_, v___x_959_, v___x_960_, v___x_961_, v_a_964_, v_b_965_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_979_ = _args[0];
lean_object* v___x_980_ = _args[1];
lean_object* v___x_981_ = _args[2];
lean_object* v___x_982_ = _args[3];
lean_object* v_inst_983_ = _args[4];
lean_object* v_R_984_ = _args[5];
lean_object* v_a_985_ = _args[6];
lean_object* v_b_986_ = _args[7];
lean_object* v_c_987_ = _args[8];
lean_object* v___y_988_ = _args[9];
lean_object* v___y_989_ = _args[10];
lean_object* v___y_990_ = _args[11];
lean_object* v___y_991_ = _args[12];
lean_object* v___y_992_ = _args[13];
lean_object* v___y_993_ = _args[14];
lean_object* v___y_994_ = _args[15];
lean_object* v___y_995_ = _args[16];
lean_object* v___y_996_ = _args[17];
lean_object* v___y_997_ = _args[18];
lean_object* v___y_998_ = _args[19];
_start:
{
uint8_t v___x_30733__boxed_999_; lean_object* v_res_1000_; 
v___x_30733__boxed_999_ = lean_unbox(v___x_982_);
v_res_1000_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(v_upperBound_979_, v___x_980_, v___x_981_, v___x_30733__boxed_999_, v_inst_983_, v_R_984_, v_a_985_, v_b_986_, v_c_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___x_981_);
lean_dec_ref(v___x_980_);
lean_dec(v_upperBound_979_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(lean_object* v_e_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_e_1001_);
if (lean_obj_tag(v___x_1013_) == 1)
{
lean_object* v_val_1014_; lean_object* v_snd_1015_; lean_object* v_fst_1016_; lean_object* v_snd_1017_; lean_object* v___x_1018_; 
v_val_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_val_1014_);
lean_dec_ref(v___x_1013_);
v_snd_1015_ = lean_ctor_get(v_val_1014_, 1);
lean_inc(v_snd_1015_);
lean_dec(v_val_1014_);
v_fst_1016_ = lean_ctor_get(v_snd_1015_, 0);
lean_inc(v_fst_1016_);
v_snd_1017_ = lean_ctor_get(v_snd_1015_, 1);
lean_inc(v_snd_1017_);
lean_dec(v_snd_1015_);
v___x_1018_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v_fst_1016_, v_snd_1017_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
return v___x_1018_;
}
else
{
uint8_t v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_dec(v___x_1013_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
v___x_1019_ = 0;
v___x_1020_ = lean_box(v___x_1019_);
v___x_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
return v___x_1021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp___boxed(lean_object* v_e_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_e_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec(v_a_1023_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(lean_object* v_cls_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_options_1041_; uint8_t v_hasTrace_1042_; 
v_options_1041_ = lean_ctor_get(v___y_1039_, 2);
v_hasTrace_1042_ = lean_ctor_get_uint8(v_options_1041_, sizeof(void*)*1);
if (v_hasTrace_1042_ == 0)
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec(v_cls_1038_);
v___x_1043_ = lean_box(v_hasTrace_1042_);
v___x_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
return v___x_1044_;
}
else
{
lean_object* v_inheritedTraceOptions_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v_inheritedTraceOptions_1045_ = lean_ctor_get(v___y_1039_, 13);
v___x_1046_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1));
v___x_1047_ = l_Lean_Name_append(v___x_1046_, v_cls_1038_);
v___x_1048_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1045_, v_options_1041_, v___x_1047_);
lean_dec(v___x_1047_);
v___x_1049_ = lean_box(v___x_1048_);
v___x_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___boxed(lean_object* v_cls_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1051_, v___y_1052_);
lean_dec_ref(v___y_1052_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(lean_object* v_cls_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1055_, v___y_1064_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___boxed(lean_object* v_cls_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(v_cls_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec(v___y_1069_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1_spec__1(lean_object* v_msgData_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1087_; lean_object* v_env_1088_; lean_object* v___x_1089_; lean_object* v_mctx_1090_; lean_object* v_lctx_1091_; lean_object* v_options_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1087_ = lean_st_ref_get(v___y_1085_);
v_env_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc_ref(v_env_1088_);
lean_dec(v___x_1087_);
v___x_1089_ = lean_st_ref_get(v___y_1083_);
v_mctx_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc_ref(v_mctx_1090_);
lean_dec(v___x_1089_);
v_lctx_1091_ = lean_ctor_get(v___y_1082_, 2);
v_options_1092_ = lean_ctor_get(v___y_1084_, 2);
lean_inc_ref(v_options_1092_);
lean_inc_ref(v_lctx_1091_);
v___x_1093_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1093_, 0, v_env_1088_);
lean_ctor_set(v___x_1093_, 1, v_mctx_1090_);
lean_ctor_set(v___x_1093_, 2, v_lctx_1091_);
lean_ctor_set(v___x_1093_, 3, v_options_1092_);
v___x_1094_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v_msgData_1081_);
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1_spec__1___boxed(lean_object* v_msgData_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1_spec__1(v_msgData_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
return v_res_1102_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1103_; double v___x_1104_; 
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1104_ = lean_float_of_nat(v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(lean_object* v_cls_1108_, lean_object* v_msg_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_ref_1115_; lean_object* v___x_1116_; lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1161_; 
v_ref_1115_ = lean_ctor_get(v___y_1112_, 5);
v___x_1116_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1_spec__1(v_msg_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1119_ = v___x_1116_;
v_isShared_1120_ = v_isSharedCheck_1161_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1116_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1161_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v_traceState_1122_; lean_object* v_env_1123_; lean_object* v_nextMacroScope_1124_; lean_object* v_ngen_1125_; lean_object* v_auxDeclNGen_1126_; lean_object* v_cache_1127_; lean_object* v_messages_1128_; lean_object* v_infoState_1129_; lean_object* v_snapshotTasks_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1160_; 
v___x_1121_ = lean_st_ref_take(v___y_1113_);
v_traceState_1122_ = lean_ctor_get(v___x_1121_, 4);
v_env_1123_ = lean_ctor_get(v___x_1121_, 0);
v_nextMacroScope_1124_ = lean_ctor_get(v___x_1121_, 1);
v_ngen_1125_ = lean_ctor_get(v___x_1121_, 2);
v_auxDeclNGen_1126_ = lean_ctor_get(v___x_1121_, 3);
v_cache_1127_ = lean_ctor_get(v___x_1121_, 5);
v_messages_1128_ = lean_ctor_get(v___x_1121_, 6);
v_infoState_1129_ = lean_ctor_get(v___x_1121_, 7);
v_snapshotTasks_1130_ = lean_ctor_get(v___x_1121_, 8);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1132_ = v___x_1121_;
v_isShared_1133_ = v_isSharedCheck_1160_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_snapshotTasks_1130_);
lean_inc(v_infoState_1129_);
lean_inc(v_messages_1128_);
lean_inc(v_cache_1127_);
lean_inc(v_traceState_1122_);
lean_inc(v_auxDeclNGen_1126_);
lean_inc(v_ngen_1125_);
lean_inc(v_nextMacroScope_1124_);
lean_inc(v_env_1123_);
lean_dec(v___x_1121_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1160_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
uint64_t v_tid_1134_; lean_object* v_traces_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1159_; 
v_tid_1134_ = lean_ctor_get_uint64(v_traceState_1122_, sizeof(void*)*1);
v_traces_1135_ = lean_ctor_get(v_traceState_1122_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_traceState_1122_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1137_ = v_traceState_1122_;
v_isShared_1138_ = v_isSharedCheck_1159_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_traces_1135_);
lean_dec(v_traceState_1122_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1159_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; double v___x_1140_; uint8_t v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1139_ = lean_box(0);
v___x_1140_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0);
v___x_1141_ = 0;
v___x_1142_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1));
v___x_1143_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1143_, 0, v_cls_1108_);
lean_ctor_set(v___x_1143_, 1, v___x_1139_);
lean_ctor_set(v___x_1143_, 2, v___x_1142_);
lean_ctor_set_float(v___x_1143_, sizeof(void*)*3, v___x_1140_);
lean_ctor_set_float(v___x_1143_, sizeof(void*)*3 + 8, v___x_1140_);
lean_ctor_set_uint8(v___x_1143_, sizeof(void*)*3 + 16, v___x_1141_);
v___x_1144_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2));
v___x_1145_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1143_);
lean_ctor_set(v___x_1145_, 1, v_a_1117_);
lean_ctor_set(v___x_1145_, 2, v___x_1144_);
lean_inc(v_ref_1115_);
v___x_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1146_, 0, v_ref_1115_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = l_Lean_PersistentArray_push___redArg(v_traces_1135_, v___x_1146_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1147_);
v___x_1149_ = v___x_1137_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1147_);
lean_ctor_set_uint64(v_reuseFailAlloc_1158_, sizeof(void*)*1, v_tid_1134_);
v___x_1149_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1151_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 4, v___x_1149_);
v___x_1151_ = v___x_1132_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_env_1123_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_nextMacroScope_1124_);
lean_ctor_set(v_reuseFailAlloc_1157_, 2, v_ngen_1125_);
lean_ctor_set(v_reuseFailAlloc_1157_, 3, v_auxDeclNGen_1126_);
lean_ctor_set(v_reuseFailAlloc_1157_, 4, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1157_, 5, v_cache_1127_);
lean_ctor_set(v_reuseFailAlloc_1157_, 6, v_messages_1128_);
lean_ctor_set(v_reuseFailAlloc_1157_, 7, v_infoState_1129_);
lean_ctor_set(v_reuseFailAlloc_1157_, 8, v_snapshotTasks_1130_);
v___x_1151_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1152_ = lean_st_ref_set(v___y_1113_, v___x_1151_);
v___x_1153_ = lean_box(0);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v___x_1153_);
v___x_1155_ = v___x_1119_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___boxed(lean_object* v_cls_1162_, lean_object* v_msg_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v_cls_1162_, v_msg_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
return v_res_1169_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__5(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__4));
v___x_1179_ = l_Lean_stringToMessageData(v___x_1178_);
return v___x_1179_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__7(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__6));
v___x_1182_ = l_Lean_stringToMessageData(v___x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2(uint8_t v___x_1183_, lean_object* v_b_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_snd_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1262_; 
v_snd_1196_ = lean_ctor_get(v_b_1184_, 1);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_b_1184_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; 
v_unused_1263_ = lean_ctor_get(v_b_1184_, 0);
lean_dec(v_unused_1263_);
v___x_1198_ = v_b_1184_;
v_isShared_1199_ = v_isSharedCheck_1262_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_snd_1196_);
lean_dec(v_b_1184_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1262_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_box(0);
if (lean_obj_tag(v_snd_1196_) == 7)
{
lean_object* v_binderType_1208_; lean_object* v_body_1209_; lean_object* v___x_1210_; 
v_binderType_1208_ = lean_ctor_get(v_snd_1196_, 1);
v_body_1209_ = lean_ctor_get(v_snd_1196_, 2);
lean_inc(v___y_1194_);
lean_inc_ref(v___y_1193_);
lean_inc(v___y_1192_);
lean_inc_ref(v___y_1191_);
lean_inc_ref(v_binderType_1208_);
v___x_1210_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_binderType_1208_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; uint8_t v___x_1212_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref(v___x_1210_);
v___x_1212_ = lean_unbox(v_a_1211_);
lean_dec(v_a_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
lean_inc_ref(v_body_1209_);
lean_dec_ref(v_snd_1196_);
lean_del_object(v___x_1198_);
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1207_);
lean_ctor_set(v___x_1213_, 1, v_body_1209_);
v_b_1184_ = v___x_1213_;
goto _start;
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__3));
v___x_1216_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_1215_, v___y_1193_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; uint8_t v___x_1218_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref(v___x_1216_);
v___x_1218_ = lean_unbox(v_a_1217_);
lean_dec(v_a_1217_);
if (v___x_1218_ == 0)
{
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
goto v___jp_1200_;
}
else
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Meta_Grind_updateLastTag(v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_dec_ref(v___x_1219_);
v___x_1220_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__5, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__5_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__5);
lean_inc_ref(v_snd_1196_);
v___x_1221_ = l_Lean_indentExpr(v_snd_1196_);
v___x_1222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1220_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v___x_1223_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__7, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__7_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__7);
v___x_1224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1222_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
lean_inc_ref(v_binderType_1208_);
v___x_1225_ = l_Lean_indentExpr(v_binderType_1208_);
v___x_1226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_1215_, v___x_1226_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_dec_ref(v___x_1227_);
goto v___jp_1200_;
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec_ref(v_snd_1196_);
lean_del_object(v___x_1198_);
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1227_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1227_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
lean_dec_ref(v_snd_1196_);
lean_del_object(v___x_1198_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
v_a_1236_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1219_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1219_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_dec_ref(v_snd_1196_);
lean_del_object(v___x_1198_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
v_a_1244_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1216_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1216_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec_ref(v_snd_1196_);
lean_del_object(v___x_1198_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
v_a_1252_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1210_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1210_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
else
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
lean_del_object(v___x_1198_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1207_);
lean_ctor_set(v___x_1260_, 1, v_snd_1196_);
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
return v___x_1261_;
}
v___jp_1200_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1201_ = lean_box(v___x_1183_);
v___x_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1202_);
v___x_1204_ = v___x_1198_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_snd_1196_);
v___x_1204_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___boxed(lean_object* v___x_1264_, lean_object* v_b_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
uint8_t v___x_27828__boxed_1277_; lean_object* v_res_1278_; 
v___x_27828__boxed_1277_ = lean_unbox(v___x_1264_);
v_res_1278_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2(v___x_27828__boxed_1277_, v_b_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec(v___y_1266_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(lean_object* v_e_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1279_, v_a_1287_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1334_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1294_ = v___x_1291_;
v_isShared_1295_ = v_isSharedCheck_1334_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1334_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1302_ = l_Lean_Expr_cleanupAnnotations(v_a_1292_);
v___x_1303_ = l_Lean_Expr_isApp(v___x_1302_);
if (v___x_1303_ == 0)
{
lean_dec_ref(v___x_1302_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
goto v___jp_1296_;
}
else
{
lean_object* v_arg_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v_arg_1304_ = lean_ctor_get(v___x_1302_, 1);
lean_inc_ref(v_arg_1304_);
v___x_1305_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1302_);
v___x_1306_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_1307_ = l_Lean_Expr_isConstOf(v___x_1305_, v___x_1306_);
lean_dec_ref(v___x_1305_);
if (v___x_1307_ == 0)
{
lean_dec_ref(v_arg_1304_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
goto v___jp_1296_;
}
else
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_del_object(v___x_1294_);
v___x_1308_ = lean_box(0);
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v_arg_1304_);
v___x_1310_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2(v___x_1307_, v___x_1309_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1325_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1325_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1325_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v_fst_1315_; 
v_fst_1315_ = lean_ctor_get(v_a_1311_, 0);
lean_inc(v_fst_1315_);
lean_dec(v_a_1311_);
if (lean_obj_tag(v_fst_1315_) == 0)
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
else
{
lean_object* v_val_1321_; lean_object* v___x_1323_; 
v_val_1321_ = lean_ctor_get(v_fst_1315_, 0);
lean_inc(v_val_1321_);
lean_dec_ref(v_fst_1315_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v_val_1321_);
v___x_1323_ = v___x_1313_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_val_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
v_a_1326_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1310_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1310_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
v___jp_1296_:
{
uint8_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1297_ = 0;
v___x_1298_ = lean_box(v___x_1297_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v___x_1298_);
v___x_1300_ = v___x_1294_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
v_a_1335_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1291_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1291_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied___boxed(lean_object* v_e_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
lean_dec(v_a_1345_);
lean_dec(v_a_1344_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(lean_object* v_cls_1356_, lean_object* v_msg_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v_cls_1356_, v_msg_1357_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___boxed(lean_object* v_cls_1370_, lean_object* v_msg_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(v_cls_1370_, v_msg_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec(v___y_1372_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(lean_object* v_k_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v_b_1391_, lean_object* v_c_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_apply_13(v_k_1384_, v_b_1391_, v_c_1392_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, lean_box(0));
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed(lean_object* v_k_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v_b_1406_, lean_object* v_c_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(v_k_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v_b_1406_, v_c_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(lean_object* v_type_1414_, lean_object* v_k_1415_, uint8_t v_cleanupAnnotations_1416_, uint8_t v_whnfType_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v___f_1429_; lean_object* v___x_1430_; 
v___f_1429_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1429_, 0, v_k_1415_);
lean_closure_set(v___f_1429_, 1, v___y_1418_);
lean_closure_set(v___f_1429_, 2, v___y_1419_);
lean_closure_set(v___f_1429_, 3, v___y_1420_);
lean_closure_set(v___f_1429_, 4, v___y_1421_);
lean_closure_set(v___f_1429_, 5, v___y_1422_);
lean_closure_set(v___f_1429_, 6, v___y_1423_);
v___x_1430_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1414_, v___f_1429_, v_cleanupAnnotations_1416_, v_whnfType_1417_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1430_) == 0)
{
return v___x_1430_;
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1430_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1430_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___boxed(lean_object* v_type_1439_, lean_object* v_k_1440_, lean_object* v_cleanupAnnotations_1441_, lean_object* v_whnfType_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1454_; uint8_t v_whnfType_boxed_1455_; lean_object* v_res_1456_; 
v_cleanupAnnotations_boxed_1454_ = lean_unbox(v_cleanupAnnotations_1441_);
v_whnfType_boxed_1455_ = lean_unbox(v_whnfType_1442_);
v_res_1456_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_1439_, v_k_1440_, v_cleanupAnnotations_boxed_1454_, v_whnfType_boxed_1455_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(lean_object* v_00_u03b1_1457_, lean_object* v_type_1458_, lean_object* v_k_1459_, uint8_t v_cleanupAnnotations_1460_, uint8_t v_whnfType_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_1458_, v_k_1459_, v_cleanupAnnotations_1460_, v_whnfType_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___boxed(lean_object* v_00_u03b1_1474_, lean_object* v_type_1475_, lean_object* v_k_1476_, lean_object* v_cleanupAnnotations_1477_, lean_object* v_whnfType_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1490_; uint8_t v_whnfType_boxed_1491_; lean_object* v_res_1492_; 
v_cleanupAnnotations_boxed_1490_ = lean_unbox(v_cleanupAnnotations_1477_);
v_whnfType_boxed_1491_ = lean_unbox(v_whnfType_1478_);
v_res_1492_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(v_00_u03b1_1474_, v_type_1475_, v_k_1476_, v_cleanupAnnotations_boxed_1490_, v_whnfType_boxed_1491_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed(lean_object* v_e_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_xs_1499_, lean_object* v_x_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
uint8_t v_a_112588__boxed_1512_; lean_object* v_res_1513_; 
v_a_112588__boxed_1512_ = lean_unbox(v_a_1497_);
v_res_1513_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(v_e_1496_, v_a_112588__boxed_1512_, v_a_1498_, v_xs_1499_, v_x_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
lean_dec_ref(v_x_1500_);
lean_dec_ref(v_xs_1499_);
return v_res_1513_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__0));
v___x_1516_ = l_Lean_stringToMessageData(v___x_1515_);
return v___x_1516_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__2));
v___x_1519_ = l_Lean_stringToMessageData(v___x_1518_);
return v___x_1519_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__4));
v___x_1522_ = l_Lean_stringToMessageData(v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(lean_object* v_e_1523_, lean_object* v_h_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
uint8_t v___y_1540_; uint8_t v___y_1541_; lean_object* v___y_1542_; uint8_t v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v_h_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; uint8_t v___y_1733_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v_cls_1926_; lean_object* v___x_1927_; 
v_cls_1926_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__3));
v___x_1927_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_1926_, v_a_1533_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; uint8_t v___x_1929_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref(v___x_1927_);
v___x_1929_ = lean_unbox(v_a_1928_);
lean_dec(v_a_1928_);
if (v___x_1929_ == 0)
{
v___y_1810_ = v_a_1525_;
v___y_1811_ = v_a_1526_;
v___y_1812_ = v_a_1527_;
v___y_1813_ = v_a_1528_;
v___y_1814_ = v_a_1529_;
v___y_1815_ = v_a_1530_;
v___y_1816_ = v_a_1531_;
v___y_1817_ = v_a_1532_;
v___y_1818_ = v_a_1533_;
v___y_1819_ = v_a_1534_;
goto v___jp_1809_;
}
else
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Lean_Meta_Grind_updateLastTag(v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v___x_1931_; 
lean_dec_ref(v___x_1930_);
lean_inc(v_a_1534_);
lean_inc_ref(v_a_1533_);
lean_inc(v_a_1532_);
lean_inc_ref(v_a_1531_);
lean_inc_ref(v_h_1524_);
v___x_1931_ = lean_infer_type(v_h_1524_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref(v___x_1931_);
v___x_1933_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5);
v___x_1934_ = l_Lean_MessageData_ofExpr(v_a_1932_);
v___x_1935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1933_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v_cls_1926_, v___x_1935_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_dec_ref(v___x_1936_);
v___y_1810_ = v_a_1525_;
v___y_1811_ = v_a_1526_;
v___y_1812_ = v_a_1527_;
v___y_1813_ = v_a_1528_;
v___y_1814_ = v_a_1529_;
v___y_1815_ = v_a_1530_;
v___y_1816_ = v_a_1531_;
v___y_1817_ = v_a_1532_;
v___y_1818_ = v_a_1533_;
v___y_1819_ = v_a_1534_;
goto v___jp_1809_;
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
lean_dec(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec_ref(v_h_1524_);
lean_dec_ref(v_e_1523_);
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
lean_dec(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec_ref(v_h_1524_);
lean_dec_ref(v_e_1523_);
v_a_1945_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1931_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1931_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
lean_dec(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec_ref(v_h_1524_);
lean_dec_ref(v_e_1523_);
v_a_1953_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1930_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1930_);
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
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
lean_dec(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec_ref(v_h_1524_);
lean_dec_ref(v_e_1523_);
v_a_1961_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1927_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1927_);
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
v___jp_1536_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = lean_box(0);
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
return v___x_1538_;
}
v___jp_1539_:
{
if (v___y_1541_ == 0)
{
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1544_);
lean_dec_ref(v_e_1523_);
if (v___y_1543_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec_ref(v_h_1546_);
lean_dec_ref(v___y_1545_);
lean_dec_ref(v___y_1542_);
v___x_1557_ = lean_box(0);
v___x_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
return v___x_1558_;
}
else
{
lean_object* v___x_1559_; 
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
lean_inc_ref(v___y_1542_);
v___x_1559_ = l_Lean_Meta_normLitValue(v___y_1542_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v___x_1561_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
lean_dec_ref(v___x_1559_);
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
lean_inc_ref(v___y_1545_);
v___x_1561_ = l_Lean_Meta_normLitValue(v___y_1545_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1601_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1564_ = v___x_1561_;
v_isShared_1565_ = v_isSharedCheck_1601_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1561_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1601_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
uint8_t v___x_1566_; 
v___x_1566_ = lean_expr_eqv(v_a_1560_, v_a_1562_);
lean_dec(v_a_1562_);
lean_dec(v_a_1560_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; 
lean_del_object(v___x_1564_);
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
v___x_1567_ = l_Lean_Meta_mkEq(v___y_1542_, v___y_1545_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref(v___x_1567_);
v___x_1569_ = l_Lean_mkNot(v_a_1568_);
v___x_1570_ = l_Lean_Meta_mkDecideProof(v___x_1569_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1580_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1580_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1580_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1575_ = l_Lean_Expr_app___override(v_a_1571_, v_h_1546_);
v___x_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1576_);
v___x_1578_ = v___x_1573_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec_ref(v_h_1546_);
v_a_1581_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1570_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1570_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec_ref(v_h_1546_);
v_a_1589_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1567_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1567_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1599_; 
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec_ref(v_h_1546_);
lean_dec_ref(v___y_1545_);
lean_dec_ref(v___y_1542_);
v___x_1597_ = lean_box(0);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1597_);
v___x_1599_ = v___x_1564_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v_a_1560_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec_ref(v_h_1546_);
lean_dec_ref(v___y_1545_);
lean_dec_ref(v___y_1542_);
v_a_1602_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1561_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1561_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec_ref(v_h_1546_);
lean_dec_ref(v___y_1545_);
lean_dec_ref(v___y_1542_);
v_a_1610_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1559_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1559_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
else
{
lean_object* v___x_1618_; 
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
v___x_1618_ = l_Lean_Meta_isConstructorApp_x3f(v___y_1542_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1709_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1709_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1709_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
if (lean_obj_tag(v_a_1619_) == 1)
{
lean_object* v_val_1623_; lean_object* v___x_1624_; 
lean_del_object(v___x_1621_);
v_val_1623_ = lean_ctor_get(v_a_1619_, 0);
lean_inc(v_val_1623_);
lean_dec_ref(v_a_1619_);
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
v___x_1624_ = l_Lean_Meta_isConstructorApp_x3f(v___y_1545_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1696_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1627_ = v___x_1624_;
v_isShared_1628_ = v_isSharedCheck_1696_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1696_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
if (lean_obj_tag(v_a_1625_) == 1)
{
lean_object* v_val_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1691_; 
lean_del_object(v___x_1627_);
v_val_1629_ = lean_ctor_get(v_a_1625_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_a_1625_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1631_ = v_a_1625_;
v_isShared_1632_ = v_isSharedCheck_1691_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_val_1629_);
lean_dec(v_a_1625_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1691_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; 
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
v___x_1633_ = l_Lean_Meta_mkNoConfusion(v___y_1544_, v_h_1546_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_toConstantVal_1634_; lean_object* v_toConstantVal_1635_; lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1682_; 
v_toConstantVal_1634_ = lean_ctor_get(v_val_1623_, 0);
lean_inc_ref(v_toConstantVal_1634_);
lean_dec(v_val_1623_);
v_toConstantVal_1635_ = lean_ctor_get(v_val_1629_, 0);
lean_inc_ref(v_toConstantVal_1635_);
lean_dec(v_val_1629_);
v_a_1636_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1638_ = v___x_1633_;
v_isShared_1639_ = v_isSharedCheck_1682_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1633_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1682_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v_name_1640_; lean_object* v_name_1641_; uint8_t v___x_1642_; 
v_name_1640_ = lean_ctor_get(v_toConstantVal_1634_, 0);
lean_inc(v_name_1640_);
lean_dec_ref(v_toConstantVal_1634_);
v_name_1641_ = lean_ctor_get(v_toConstantVal_1635_, 0);
lean_inc(v_name_1641_);
lean_dec_ref(v_toConstantVal_1635_);
v___x_1642_ = lean_name_eq(v_name_1640_, v_name_1641_);
lean_dec(v_name_1641_);
lean_dec(v_name_1640_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1644_; 
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
lean_dec_ref(v_e_1523_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v_a_1636_);
v___x_1644_ = v___x_1631_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1636_);
v___x_1644_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1646_; 
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1644_);
v___x_1646_ = v___x_1638_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
else
{
lean_object* v___x_1649_; 
lean_del_object(v___x_1638_);
lean_del_object(v___x_1631_);
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
lean_inc(v_a_1636_);
v___x_1649_ = lean_infer_type(v_a_1636_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1651_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref(v___x_1649_);
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
v___x_1651_ = l_Lean_Meta_whnfD(v_a_1650_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1665_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1665_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1665_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
if (lean_obj_tag(v_a_1652_) == 7)
{
lean_object* v_binderType_1656_; lean_object* v___x_1657_; lean_object* v___f_1658_; uint8_t v___x_1659_; lean_object* v___x_1660_; 
lean_del_object(v___x_1654_);
v_binderType_1656_ = lean_ctor_get(v_a_1652_, 1);
lean_inc_ref(v_binderType_1656_);
lean_dec_ref(v_a_1652_);
v___x_1657_ = lean_box(v___y_1540_);
v___f_1658_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed), 16, 3);
lean_closure_set(v___f_1658_, 0, v_e_1523_);
lean_closure_set(v___f_1658_, 1, v___x_1657_);
lean_closure_set(v___f_1658_, 2, v_a_1636_);
v___x_1659_ = 0;
v___x_1660_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_binderType_1656_, v___f_1658_, v___x_1659_, v___x_1659_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
return v___x_1660_;
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
lean_dec(v_a_1652_);
lean_dec(v_a_1636_);
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
lean_dec_ref(v_e_1523_);
v___x_1661_ = lean_box(0);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1661_);
v___x_1663_ = v___x_1654_;
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
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
lean_dec(v_a_1636_);
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
lean_dec_ref(v_e_1523_);
v_a_1666_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1651_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1651_);
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
lean_dec(v_a_1636_);
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
lean_dec_ref(v_e_1523_);
v_a_1674_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1649_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1649_);
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
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_del_object(v___x_1631_);
lean_dec(v_val_1629_);
lean_dec(v_val_1623_);
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
lean_dec_ref(v_e_1523_);
v_a_1683_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1633_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1633_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1694_; 
lean_dec(v_a_1625_);
lean_dec(v_val_1623_);
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
lean_dec_ref(v_h_1546_);
lean_dec_ref(v___y_1544_);
lean_dec_ref(v_e_1523_);
v___x_1692_ = lean_box(0);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1692_);
v___x_1694_ = v___x_1627_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec(v_val_1623_);
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
lean_dec_ref(v_h_1546_);
lean_dec_ref(v___y_1544_);
lean_dec_ref(v_e_1523_);
v_a_1697_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1624_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1624_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1707_; 
lean_dec(v_a_1619_);
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
lean_dec_ref(v_h_1546_);
lean_dec_ref(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec_ref(v_e_1523_);
v___x_1705_ = lean_box(0);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1705_);
v___x_1707_ = v___x_1621_;
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
lean_dec_ref(v_h_1546_);
lean_dec_ref(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec_ref(v_e_1523_);
v_a_1710_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1618_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1618_);
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
}
v___jp_1718_:
{
lean_object* v_self_1734_; uint8_t v_interpreted_1735_; uint8_t v_ctor_1736_; lean_object* v___x_1737_; 
v_self_1734_ = lean_ctor_get(v___y_1725_, 0);
lean_inc_ref(v_self_1734_);
v_interpreted_1735_ = lean_ctor_get_uint8(v___y_1725_, sizeof(void*)*11 + 1);
v_ctor_1736_ = lean_ctor_get_uint8(v___y_1725_, sizeof(void*)*11 + 2);
lean_dec_ref(v___y_1725_);
lean_inc(v___y_1720_);
lean_inc_ref(v___y_1731_);
lean_inc(v___y_1728_);
lean_inc_ref(v___y_1726_);
lean_inc_ref(v___y_1730_);
lean_inc_ref(v_self_1734_);
v___x_1737_ = l_Lean_Meta_Grind_hasSameType(v_self_1734_, v___y_1730_, v___y_1726_, v___y_1728_, v___y_1731_, v___y_1720_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1800_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1800_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1800_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
uint8_t v___x_1742_; 
v___x_1742_ = lean_unbox(v_a_1738_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1745_; 
lean_dec(v_a_1738_);
lean_dec_ref(v_self_1734_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec_ref(v_h_1524_);
lean_dec_ref(v_e_1523_);
v___x_1743_ = lean_box(0);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1743_);
v___x_1745_ = v___x_1740_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
else
{
lean_del_object(v___x_1740_);
if (v___y_1733_ == 0)
{
lean_object* v___x_1747_; 
lean_inc(v___y_1720_);
lean_inc_ref(v___y_1731_);
lean_inc(v___y_1728_);
lean_inc_ref(v___y_1726_);
lean_inc(v___y_1723_);
lean_inc_ref(v___y_1727_);
lean_inc(v___y_1722_);
lean_inc_ref(v___y_1719_);
lean_inc(v___y_1724_);
lean_inc(v___y_1732_);
lean_inc_ref(v_self_1734_);
v___x_1747_ = lean_grind_mk_eq_proof(v_self_1734_, v___y_1721_, v___y_1732_, v___y_1724_, v___y_1719_, v___y_1722_, v___y_1727_, v___y_1723_, v___y_1726_, v___y_1728_, v___y_1731_, v___y_1720_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1749_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref(v___x_1747_);
lean_inc(v___y_1720_);
lean_inc_ref(v___y_1731_);
lean_inc(v___y_1728_);
lean_inc_ref(v___y_1726_);
v___x_1749_ = l_Lean_Meta_mkEqTrans(v_a_1748_, v_h_1524_, v___y_1726_, v___y_1728_, v___y_1731_, v___y_1720_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; uint8_t v___x_1751_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref(v___x_1749_);
v___x_1751_ = lean_unbox(v_a_1738_);
lean_dec(v_a_1738_);
v___y_1540_ = v___x_1751_;
v___y_1541_ = v_ctor_1736_;
v___y_1542_ = v_self_1734_;
v___y_1543_ = v_interpreted_1735_;
v___y_1544_ = v___y_1729_;
v___y_1545_ = v___y_1730_;
v_h_1546_ = v_a_1750_;
v___y_1547_ = v___y_1732_;
v___y_1548_ = v___y_1724_;
v___y_1549_ = v___y_1719_;
v___y_1550_ = v___y_1722_;
v___y_1551_ = v___y_1727_;
v___y_1552_ = v___y_1723_;
v___y_1553_ = v___y_1726_;
v___y_1554_ = v___y_1728_;
v___y_1555_ = v___y_1731_;
v___y_1556_ = v___y_1720_;
goto v___jp_1539_;
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec(v_a_1738_);
lean_dec_ref(v_self_1734_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec_ref(v_e_1523_);
v_a_1752_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1749_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1749_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec(v_a_1738_);
lean_dec_ref(v_self_1734_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec_ref(v_h_1524_);
lean_dec_ref(v_e_1523_);
v_a_1760_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1747_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1747_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
else
{
lean_object* v___x_1768_; 
lean_inc(v___y_1720_);
lean_inc_ref(v___y_1731_);
lean_inc(v___y_1728_);
lean_inc_ref(v___y_1726_);
lean_inc(v___y_1723_);
lean_inc_ref(v___y_1727_);
lean_inc(v___y_1722_);
lean_inc_ref(v___y_1719_);
lean_inc(v___y_1724_);
lean_inc(v___y_1732_);
lean_inc_ref(v_self_1734_);
v___x_1768_ = lean_grind_mk_heq_proof(v_self_1734_, v___y_1721_, v___y_1732_, v___y_1724_, v___y_1719_, v___y_1722_, v___y_1727_, v___y_1723_, v___y_1726_, v___y_1728_, v___y_1731_, v___y_1720_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1770_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref(v___x_1768_);
lean_inc(v___y_1720_);
lean_inc_ref(v___y_1731_);
lean_inc(v___y_1728_);
lean_inc_ref(v___y_1726_);
v___x_1770_ = l_Lean_Meta_mkHEqTrans(v_a_1769_, v_h_1524_, v___y_1726_, v___y_1728_, v___y_1731_, v___y_1720_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; uint8_t v___x_1772_; lean_object* v___x_1773_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref(v___x_1770_);
v___x_1772_ = 0;
lean_inc(v___y_1720_);
lean_inc_ref(v___y_1731_);
lean_inc(v___y_1728_);
lean_inc_ref(v___y_1726_);
v___x_1773_ = l_Lean_Meta_mkEqOfHEq(v_a_1771_, v___x_1772_, v___y_1726_, v___y_1728_, v___y_1731_, v___y_1720_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; uint8_t v___x_1775_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref(v___x_1773_);
v___x_1775_ = lean_unbox(v_a_1738_);
lean_dec(v_a_1738_);
v___y_1540_ = v___x_1775_;
v___y_1541_ = v_ctor_1736_;
v___y_1542_ = v_self_1734_;
v___y_1543_ = v_interpreted_1735_;
v___y_1544_ = v___y_1729_;
v___y_1545_ = v___y_1730_;
v_h_1546_ = v_a_1774_;
v___y_1547_ = v___y_1732_;
v___y_1548_ = v___y_1724_;
v___y_1549_ = v___y_1719_;
v___y_1550_ = v___y_1722_;
v___y_1551_ = v___y_1727_;
v___y_1552_ = v___y_1723_;
v___y_1553_ = v___y_1726_;
v___y_1554_ = v___y_1728_;
v___y_1555_ = v___y_1731_;
v___y_1556_ = v___y_1720_;
goto v___jp_1539_;
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_dec(v_a_1738_);
lean_dec_ref(v_self_1734_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec_ref(v_e_1523_);
v_a_1776_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1773_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1773_);
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
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
lean_dec(v_a_1738_);
lean_dec_ref(v_self_1734_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec_ref(v_e_1523_);
v_a_1784_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1770_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1770_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
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
lean_dec(v_a_1738_);
lean_dec_ref(v_self_1734_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec_ref(v_h_1524_);
lean_dec_ref(v_e_1523_);
v_a_1792_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1768_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1768_);
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
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec_ref(v_self_1734_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec_ref(v_h_1524_);
lean_dec_ref(v_e_1523_);
v_a_1801_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1737_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1737_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
v___jp_1809_:
{
lean_object* v___x_1820_; 
lean_inc(v___y_1819_);
lean_inc_ref(v___y_1818_);
lean_inc(v___y_1817_);
lean_inc_ref(v___y_1816_);
lean_inc_ref(v_h_1524_);
v___x_1820_ = lean_infer_type(v_h_1524_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1917_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1823_ = v___x_1820_;
v_isShared_1824_ = v_isSharedCheck_1917_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1820_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1917_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; 
v___x_1825_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_a_1821_);
if (lean_obj_tag(v___x_1825_) == 1)
{
lean_object* v_val_1826_; lean_object* v_snd_1827_; lean_object* v_fst_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1912_; 
lean_del_object(v___x_1823_);
v_val_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_val_1826_);
lean_dec_ref(v___x_1825_);
v_snd_1827_ = lean_ctor_get(v_val_1826_, 1);
v_fst_1828_ = lean_ctor_get(v_val_1826_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_val_1826_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1830_ = v_val_1826_;
v_isShared_1831_ = v_isSharedCheck_1912_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_snd_1827_);
lean_inc(v_fst_1828_);
lean_dec(v_val_1826_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1912_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v_fst_1832_; lean_object* v_snd_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1911_; 
v_fst_1832_ = lean_ctor_get(v_snd_1827_, 0);
v_snd_1833_ = lean_ctor_get(v_snd_1827_, 1);
v_isSharedCheck_1911_ = !lean_is_exclusive(v_snd_1827_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1835_ = v_snd_1827_;
v_isShared_1836_ = v_isSharedCheck_1911_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_snd_1833_);
lean_inc(v_fst_1832_);
lean_dec(v_snd_1827_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1911_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v_mvarId_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1909_; 
v___x_1837_ = lean_st_ref_get(v___y_1810_);
v_mvarId_1838_ = lean_ctor_get(v___x_1837_, 1);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1909_ == 0)
{
lean_object* v_unused_1910_; 
v_unused_1910_ = lean_ctor_get(v___x_1837_, 0);
lean_dec(v_unused_1910_);
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1909_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_mvarId_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1909_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; 
v___x_1842_ = l_Lean_MVarId_getType(v_mvarId_1838_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1844_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_a_1843_);
lean_dec_ref(v___x_1842_);
v___x_1844_ = l_Lean_Meta_Sym_shareCommon___redArg(v_fst_1832_, v___y_1815_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1846_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref(v___x_1844_);
v___x_1846_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_a_1845_, v___y_1810_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref(v___x_1846_);
if (lean_obj_tag(v_a_1847_) == 1)
{
lean_del_object(v___x_1840_);
lean_del_object(v___x_1835_);
lean_del_object(v___x_1830_);
if (lean_obj_tag(v_fst_1828_) == 0)
{
lean_object* v_val_1848_; uint8_t v___x_1849_; 
v_val_1848_ = lean_ctor_get(v_a_1847_, 0);
lean_inc(v_val_1848_);
lean_dec_ref(v_a_1847_);
v___x_1849_ = 0;
v___y_1719_ = v___y_1812_;
v___y_1720_ = v___y_1819_;
v___y_1721_ = v_a_1845_;
v___y_1722_ = v___y_1813_;
v___y_1723_ = v___y_1815_;
v___y_1724_ = v___y_1811_;
v___y_1725_ = v_val_1848_;
v___y_1726_ = v___y_1816_;
v___y_1727_ = v___y_1814_;
v___y_1728_ = v___y_1817_;
v___y_1729_ = v_a_1843_;
v___y_1730_ = v_snd_1833_;
v___y_1731_ = v___y_1818_;
v___y_1732_ = v___y_1810_;
v___y_1733_ = v___x_1849_;
goto v___jp_1718_;
}
else
{
lean_object* v_val_1850_; uint8_t v___x_1851_; 
lean_dec_ref(v_fst_1828_);
v_val_1850_ = lean_ctor_get(v_a_1847_, 0);
lean_inc(v_val_1850_);
lean_dec_ref(v_a_1847_);
v___x_1851_ = 1;
v___y_1719_ = v___y_1812_;
v___y_1720_ = v___y_1819_;
v___y_1721_ = v_a_1845_;
v___y_1722_ = v___y_1813_;
v___y_1723_ = v___y_1815_;
v___y_1724_ = v___y_1811_;
v___y_1725_ = v_val_1850_;
v___y_1726_ = v___y_1816_;
v___y_1727_ = v___y_1814_;
v___y_1728_ = v___y_1817_;
v___y_1729_ = v_a_1843_;
v___y_1730_ = v_snd_1833_;
v___y_1731_ = v___y_1818_;
v___y_1732_ = v___y_1810_;
v___y_1733_ = v___x_1851_;
goto v___jp_1718_;
}
}
else
{
lean_object* v___x_1852_; 
lean_dec(v_a_1847_);
lean_dec(v_a_1843_);
lean_dec(v_snd_1833_);
lean_dec(v_fst_1828_);
lean_dec(v___y_1810_);
lean_dec_ref(v_h_1524_);
v___x_1852_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_1812_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; uint8_t v_verbose_1854_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
lean_dec_ref(v___x_1852_);
v_verbose_1854_ = lean_ctor_get_uint8(v_a_1853_, sizeof(void*)*11 + 15);
lean_dec(v_a_1853_);
if (v_verbose_1854_ == 0)
{
lean_dec(v_a_1845_);
lean_del_object(v___x_1840_);
lean_del_object(v___x_1835_);
lean_del_object(v___x_1830_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec_ref(v_e_1523_);
goto v___jp_1536_;
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1858_; 
v___x_1855_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1);
v___x_1856_ = l_Lean_indentExpr(v_a_1845_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set_tag(v___x_1840_, 7);
lean_ctor_set(v___x_1840_, 1, v___x_1856_);
lean_ctor_set(v___x_1840_, 0, v___x_1855_);
v___x_1858_ = v___x_1840_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1855_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1859_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3);
if (v_isShared_1836_ == 0)
{
lean_ctor_set_tag(v___x_1835_, 7);
lean_ctor_set(v___x_1835_, 1, v___x_1859_);
lean_ctor_set(v___x_1835_, 0, v___x_1858_);
v___x_1861_ = v___x_1835_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1858_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1862_ = l_Lean_indentExpr(v_e_1523_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set_tag(v___x_1830_, 7);
lean_ctor_set(v___x_1830_, 1, v___x_1862_);
lean_ctor_set(v___x_1830_, 0, v___x_1861_);
v___x_1864_ = v___x_1830_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_Meta_Grind_reportIssue(v___x_1864_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_dec_ref(v___x_1865_);
goto v___jp_1536_;
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1865_);
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
}
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec(v_a_1845_);
lean_del_object(v___x_1840_);
lean_del_object(v___x_1835_);
lean_del_object(v___x_1830_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec_ref(v_e_1523_);
v_a_1877_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1852_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1852_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v_a_1845_);
lean_dec(v_a_1843_);
lean_del_object(v___x_1840_);
lean_del_object(v___x_1835_);
lean_dec(v_snd_1833_);
lean_del_object(v___x_1830_);
lean_dec(v_fst_1828_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v_h_1524_);
lean_dec_ref(v_e_1523_);
v_a_1885_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1846_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1846_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec(v_a_1843_);
lean_del_object(v___x_1840_);
lean_del_object(v___x_1835_);
lean_dec(v_snd_1833_);
lean_del_object(v___x_1830_);
lean_dec(v_fst_1828_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v_h_1524_);
lean_dec_ref(v_e_1523_);
v_a_1893_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1844_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1844_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_del_object(v___x_1840_);
lean_del_object(v___x_1835_);
lean_dec(v_snd_1833_);
lean_dec(v_fst_1832_);
lean_del_object(v___x_1830_);
lean_dec(v_fst_1828_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v_h_1524_);
lean_dec_ref(v_e_1523_);
v_a_1901_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1842_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1842_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1913_; lean_object* v___x_1915_; 
lean_dec(v___x_1825_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v_h_1524_);
lean_dec_ref(v_e_1523_);
v___x_1913_ = lean_box(0);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1913_);
v___x_1915_ = v___x_1823_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v_h_1524_);
lean_dec_ref(v_e_1523_);
v_a_1918_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1820_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1820_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(lean_object* v_e_1969_, lean_object* v_xs_1970_, uint8_t v_a_1971_, lean_object* v_a_1972_, lean_object* v_as_1973_, size_t v_sz_1974_, size_t v_i_1975_, lean_object* v_b_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
uint8_t v___x_1988_; 
v___x_1988_ = lean_usize_dec_lt(v_i_1975_, v_sz_1974_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; 
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v_a_1972_);
lean_dec_ref(v_e_1969_);
v___x_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1989_, 0, v_b_1976_);
return v___x_1989_;
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1991_; 
lean_dec_ref(v_b_1976_);
v_a_1990_ = lean_array_uget_borrowed(v_as_1973_, v_i_1975_);
lean_inc(v___y_1986_);
lean_inc_ref(v___y_1985_);
lean_inc(v___y_1984_);
lean_inc_ref(v___y_1983_);
lean_inc(v___y_1982_);
lean_inc_ref(v___y_1981_);
lean_inc(v___y_1980_);
lean_inc_ref(v___y_1979_);
lean_inc(v___y_1978_);
lean_inc(v___y_1977_);
lean_inc(v_a_1990_);
lean_inc_ref(v_e_1969_);
v___x_1991_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_1969_, v_a_1990_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1993_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref(v___x_1991_);
v___x_1993_ = lean_box(0);
if (lean_obj_tag(v_a_1992_) == 1)
{
lean_object* v_val_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2023_; 
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v_e_1969_);
v_val_1994_ = lean_ctor_get(v_a_1992_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_a_1992_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_1996_ = v_a_1992_;
v_isShared_1997_ = v_isSharedCheck_2023_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_val_1994_);
lean_dec(v_a_1992_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2023_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
uint8_t v___x_1998_; uint8_t v___x_1999_; lean_object* v___x_2000_; 
v___x_1998_ = 0;
v___x_1999_ = 1;
v___x_2000_ = l_Lean_Meta_mkLambdaFVars(v_xs_1970_, v_val_1994_, v___x_1998_, v_a_1971_, v___x_1998_, v_a_1971_, v___x_1999_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2014_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2014_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2014_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = l_Lean_Expr_app___override(v_a_1972_, v_a_2001_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v___x_2005_);
v___x_2007_ = v___x_1996_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2011_; 
v___x_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
v___x_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
lean_ctor_set(v___x_2009_, 1, v___x_1993_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2009_);
v___x_2011_ = v___x_2003_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_del_object(v___x_1996_);
lean_dec_ref(v_a_1972_);
v_a_2015_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_2000_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2000_);
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
else
{
lean_object* v___x_2024_; size_t v___x_2025_; size_t v___x_2026_; 
lean_dec(v_a_1992_);
v___x_2024_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v___x_2025_ = ((size_t)1ULL);
v___x_2026_ = lean_usize_add(v_i_1975_, v___x_2025_);
v_i_1975_ = v___x_2026_;
v_b_1976_ = v___x_2024_;
goto _start;
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v_a_1972_);
lean_dec_ref(v_e_1969_);
v_a_2028_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_1991_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_1991_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(lean_object* v_e_2036_, uint8_t v_a_2037_, lean_object* v_a_2038_, lean_object* v_xs_2039_, lean_object* v_x_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; size_t v_sz_2054_; size_t v___x_2055_; lean_object* v___x_2056_; 
v___x_2052_ = lean_box(0);
v___x_2053_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_sz_2054_ = lean_array_size(v_xs_2039_);
v___x_2055_ = ((size_t)0ULL);
v___x_2056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_2036_, v_xs_2039_, v_a_2037_, v_a_2038_, v_xs_2039_, v_sz_2054_, v___x_2055_, v___x_2053_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2069_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2059_ = v___x_2056_;
v_isShared_2060_ = v_isSharedCheck_2069_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2056_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2069_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_fst_2061_; 
v_fst_2061_ = lean_ctor_get(v_a_2057_, 0);
lean_inc(v_fst_2061_);
lean_dec(v_a_2057_);
if (lean_obj_tag(v_fst_2061_) == 0)
{
lean_object* v___x_2063_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2052_);
v___x_2063_ = v___x_2059_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2052_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
else
{
lean_object* v_val_2065_; lean_object* v___x_2067_; 
v_val_2065_ = lean_ctor_get(v_fst_2061_, 0);
lean_inc(v_val_2065_);
lean_dec_ref(v_fst_2061_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v_val_2065_);
v___x_2067_ = v___x_2059_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_val_2065_);
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
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
v_a_2070_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2056_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2056_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_e_2078_ = _args[0];
lean_object* v_xs_2079_ = _args[1];
lean_object* v_a_2080_ = _args[2];
lean_object* v_a_2081_ = _args[3];
lean_object* v_as_2082_ = _args[4];
lean_object* v_sz_2083_ = _args[5];
lean_object* v_i_2084_ = _args[6];
lean_object* v_b_2085_ = _args[7];
lean_object* v___y_2086_ = _args[8];
lean_object* v___y_2087_ = _args[9];
lean_object* v___y_2088_ = _args[10];
lean_object* v___y_2089_ = _args[11];
lean_object* v___y_2090_ = _args[12];
lean_object* v___y_2091_ = _args[13];
lean_object* v___y_2092_ = _args[14];
lean_object* v___y_2093_ = _args[15];
lean_object* v___y_2094_ = _args[16];
lean_object* v___y_2095_ = _args[17];
lean_object* v___y_2096_ = _args[18];
_start:
{
uint8_t v_a_112612__boxed_2097_; size_t v_sz_boxed_2098_; size_t v_i_boxed_2099_; lean_object* v_res_2100_; 
v_a_112612__boxed_2097_ = lean_unbox(v_a_2080_);
v_sz_boxed_2098_ = lean_unbox_usize(v_sz_2083_);
lean_dec(v_sz_2083_);
v_i_boxed_2099_ = lean_unbox_usize(v_i_2084_);
lean_dec(v_i_2084_);
v_res_2100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_2078_, v_xs_2079_, v_a_112612__boxed_2097_, v_a_2081_, v_as_2082_, v_sz_boxed_2098_, v_i_boxed_2099_, v_b_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
lean_dec_ref(v_as_2082_);
lean_dec_ref(v_xs_2079_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___boxed(lean_object* v_e_2101_, lean_object* v_h_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2101_, v_h_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
return v_res_2114_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__0));
v___x_2117_ = l_Lean_stringToMessageData(v___x_2116_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(lean_object* v_e_2118_, lean_object* v_xs_2119_, uint8_t v___x_2120_, lean_object* v_as_2121_, size_t v_sz_2122_, size_t v_i_2123_, lean_object* v_b_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v_a_2137_; uint8_t v___x_2141_; 
v___x_2141_ = lean_usize_dec_lt(v_i_2123_, v_sz_2122_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; 
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v_e_2118_);
v___x_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2142_, 0, v_b_2124_);
return v___x_2142_;
}
else
{
lean_object* v_a_2143_; lean_object* v___x_2144_; 
lean_dec_ref(v_b_2124_);
v_a_2143_ = lean_array_uget_borrowed(v_as_2121_, v_i_2123_);
lean_inc(v___y_2134_);
lean_inc_ref(v___y_2133_);
lean_inc(v___y_2132_);
lean_inc_ref(v___y_2131_);
lean_inc(v_a_2143_);
v___x_2144_ = lean_infer_type(v_a_2143_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2146_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref(v___x_2144_);
lean_inc(v___y_2134_);
lean_inc_ref(v___y_2133_);
lean_inc(v___y_2132_);
lean_inc_ref(v___y_2131_);
lean_inc(v_a_2145_);
v___x_2146_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_a_2145_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; uint8_t v___x_2200_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref(v___x_2146_);
v___x_2148_ = lean_box(0);
v___x_2149_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v___x_2200_ = lean_unbox(v_a_2147_);
lean_dec(v_a_2147_);
if (v___x_2200_ == 0)
{
lean_dec(v_a_2145_);
v_a_2137_ = v___x_2149_;
goto v___jp_2136_;
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__3));
v___x_2202_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_2201_, v___y_2133_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; uint8_t v___x_2204_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref(v___x_2202_);
v___x_2204_ = lean_unbox(v_a_2203_);
lean_dec(v_a_2203_);
if (v___x_2204_ == 0)
{
lean_dec(v_a_2145_);
lean_inc(v___y_2134_);
lean_inc_ref(v___y_2133_);
lean_inc(v___y_2132_);
lean_inc_ref(v___y_2131_);
lean_inc(v___y_2130_);
lean_inc_ref(v___y_2129_);
lean_inc(v___y_2128_);
lean_inc_ref(v___y_2127_);
lean_inc(v___y_2126_);
lean_inc(v___y_2125_);
v___y_2151_ = v___y_2125_;
v___y_2152_ = v___y_2126_;
v___y_2153_ = v___y_2127_;
v___y_2154_ = v___y_2128_;
v___y_2155_ = v___y_2129_;
v___y_2156_ = v___y_2130_;
v___y_2157_ = v___y_2131_;
v___y_2158_ = v___y_2132_;
v___y_2159_ = v___y_2133_;
v___y_2160_ = v___y_2134_;
goto v___jp_2150_;
}
else
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Lean_Meta_Grind_updateLastTag(v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_dec_ref(v___x_2205_);
v___x_2206_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1);
v___x_2207_ = l_Lean_MessageData_ofExpr(v_a_2145_);
v___x_2208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2206_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
v___x_2209_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_2201_, v___x_2208_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_dec_ref(v___x_2209_);
lean_inc(v___y_2134_);
lean_inc_ref(v___y_2133_);
lean_inc(v___y_2132_);
lean_inc_ref(v___y_2131_);
lean_inc(v___y_2130_);
lean_inc_ref(v___y_2129_);
lean_inc(v___y_2128_);
lean_inc_ref(v___y_2127_);
lean_inc(v___y_2126_);
lean_inc(v___y_2125_);
v___y_2151_ = v___y_2125_;
v___y_2152_ = v___y_2126_;
v___y_2153_ = v___y_2127_;
v___y_2154_ = v___y_2128_;
v___y_2155_ = v___y_2129_;
v___y_2156_ = v___y_2130_;
v___y_2157_ = v___y_2131_;
v___y_2158_ = v___y_2132_;
v___y_2159_ = v___y_2133_;
v___y_2160_ = v___y_2134_;
goto v___jp_2150_;
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v_e_2118_);
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2209_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2209_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec(v_a_2145_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v_e_2118_);
v_a_2218_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2205_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2205_);
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
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec(v_a_2145_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v_e_2118_);
v_a_2226_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2202_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2202_);
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
v___jp_2150_:
{
lean_object* v___x_2161_; 
lean_inc(v___y_2160_);
lean_inc_ref(v___y_2159_);
lean_inc(v___y_2158_);
lean_inc_ref(v___y_2157_);
lean_inc(v_a_2143_);
lean_inc_ref(v_e_2118_);
v___x_2161_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_2118_, v_a_2143_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2162_);
lean_dec_ref(v___x_2161_);
if (lean_obj_tag(v_a_2162_) == 1)
{
lean_object* v_val_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2191_; 
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v_e_2118_);
v_val_2163_ = lean_ctor_get(v_a_2162_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_a_2162_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2165_ = v_a_2162_;
v_isShared_2166_ = v_isSharedCheck_2191_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_val_2163_);
lean_dec(v_a_2162_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2191_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
uint8_t v___x_2167_; uint8_t v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = 0;
v___x_2168_ = 1;
v___x_2169_ = l_Lean_Meta_mkLambdaFVars(v_xs_2119_, v_val_2163_, v___x_2167_, v___x_2120_, v___x_2167_, v___x_2120_, v___x_2168_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2182_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2182_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2182_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 0, v_a_2170_);
v___x_2175_ = v___x_2165_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2179_; 
v___x_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
v___x_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
lean_ctor_set(v___x_2177_, 1, v___x_2148_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2177_);
v___x_2179_ = v___x_2172_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_del_object(v___x_2165_);
v_a_2183_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2169_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2169_);
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
}
else
{
lean_dec(v_a_2162_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
v_a_2137_ = v___x_2149_;
goto v___jp_2136_;
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v_e_2118_);
v_a_2192_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2161_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2161_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_dec(v_a_2145_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v_e_2118_);
v_a_2234_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2146_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2146_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v_e_2118_);
v_a_2242_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2144_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2144_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
v___jp_2136_:
{
size_t v___x_2138_; size_t v___x_2139_; 
v___x_2138_ = ((size_t)1ULL);
v___x_2139_ = lean_usize_add(v_i_2123_, v___x_2138_);
v_i_2123_ = v___x_2139_;
v_b_2124_ = v_a_2137_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_e_2250_ = _args[0];
lean_object* v_xs_2251_ = _args[1];
lean_object* v___x_2252_ = _args[2];
lean_object* v_as_2253_ = _args[3];
lean_object* v_sz_2254_ = _args[4];
lean_object* v_i_2255_ = _args[5];
lean_object* v_b_2256_ = _args[6];
lean_object* v___y_2257_ = _args[7];
lean_object* v___y_2258_ = _args[8];
lean_object* v___y_2259_ = _args[9];
lean_object* v___y_2260_ = _args[10];
lean_object* v___y_2261_ = _args[11];
lean_object* v___y_2262_ = _args[12];
lean_object* v___y_2263_ = _args[13];
lean_object* v___y_2264_ = _args[14];
lean_object* v___y_2265_ = _args[15];
lean_object* v___y_2266_ = _args[16];
lean_object* v___y_2267_ = _args[17];
_start:
{
uint8_t v___x_27212__boxed_2268_; size_t v_sz_boxed_2269_; size_t v_i_boxed_2270_; lean_object* v_res_2271_; 
v___x_27212__boxed_2268_ = lean_unbox(v___x_2252_);
v_sz_boxed_2269_ = lean_unbox_usize(v_sz_2254_);
lean_dec(v_sz_2254_);
v_i_boxed_2270_ = lean_unbox_usize(v_i_2255_);
lean_dec(v_i_2255_);
v_res_2271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2250_, v_xs_2251_, v___x_27212__boxed_2268_, v_as_2253_, v_sz_boxed_2269_, v_i_boxed_2270_, v_b_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec_ref(v_as_2253_);
lean_dec_ref(v_xs_2251_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(lean_object* v_e_2272_, uint8_t v___x_2273_, lean_object* v_xs_2274_, lean_object* v_x_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; size_t v_sz_2289_; size_t v___x_2290_; lean_object* v___x_2291_; 
v___x_2287_ = lean_box(0);
v___x_2288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
v_sz_2289_ = lean_array_size(v_xs_2274_);
v___x_2290_ = ((size_t)0ULL);
v___x_2291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_2272_, v_xs_2274_, v___x_2273_, v_xs_2274_, v_sz_2289_, v___x_2290_, v___x_2288_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2304_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2294_ = v___x_2291_;
v_isShared_2295_ = v_isSharedCheck_2304_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2291_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2304_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v_fst_2296_; 
v_fst_2296_ = lean_ctor_get(v_a_2292_, 0);
lean_inc(v_fst_2296_);
lean_dec(v_a_2292_);
if (lean_obj_tag(v_fst_2296_) == 0)
{
lean_object* v___x_2298_; 
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v___x_2287_);
v___x_2298_ = v___x_2294_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2287_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
else
{
lean_object* v_val_2300_; lean_object* v___x_2302_; 
v_val_2300_ = lean_ctor_get(v_fst_2296_, 0);
lean_inc(v_val_2300_);
lean_dec_ref(v_fst_2296_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v_val_2300_);
v___x_2302_ = v___x_2294_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_val_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
v_a_2305_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2291_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2291_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed(lean_object* v_e_2313_, lean_object* v___x_2314_, lean_object* v_xs_2315_, lean_object* v_x_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
uint8_t v___x_27482__boxed_2328_; lean_object* v_res_2329_; 
v___x_27482__boxed_2328_ = lean_unbox(v___x_2314_);
v_res_2329_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(v_e_2313_, v___x_27482__boxed_2328_, v_xs_2315_, v_x_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
lean_dec_ref(v_x_2316_);
lean_dec_ref(v_xs_2315_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(lean_object* v_e_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v___x_2342_; 
lean_inc_ref(v_e_2330_);
v___x_2342_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2330_, v_a_2338_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2362_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2362_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2362_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2352_; uint8_t v___x_2353_; 
v___x_2352_ = l_Lean_Expr_cleanupAnnotations(v_a_2343_);
v___x_2353_ = l_Lean_Expr_isApp(v___x_2352_);
if (v___x_2353_ == 0)
{
lean_dec_ref(v___x_2352_);
lean_dec(v_a_2340_);
lean_dec_ref(v_a_2339_);
lean_dec(v_a_2338_);
lean_dec_ref(v_a_2337_);
lean_dec(v_a_2336_);
lean_dec_ref(v_a_2335_);
lean_dec(v_a_2334_);
lean_dec_ref(v_a_2333_);
lean_dec(v_a_2332_);
lean_dec(v_a_2331_);
lean_dec_ref(v_e_2330_);
goto v___jp_2347_;
}
else
{
lean_object* v_arg_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; 
v_arg_2354_ = lean_ctor_get(v___x_2352_, 1);
lean_inc_ref(v_arg_2354_);
v___x_2355_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2352_);
v___x_2356_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_2357_ = l_Lean_Expr_isConstOf(v___x_2355_, v___x_2356_);
lean_dec_ref(v___x_2355_);
if (v___x_2357_ == 0)
{
lean_dec_ref(v_arg_2354_);
lean_dec(v_a_2340_);
lean_dec_ref(v_a_2339_);
lean_dec(v_a_2338_);
lean_dec_ref(v_a_2337_);
lean_dec(v_a_2336_);
lean_dec_ref(v_a_2335_);
lean_dec(v_a_2334_);
lean_dec_ref(v_a_2333_);
lean_dec(v_a_2332_);
lean_dec(v_a_2331_);
lean_dec_ref(v_e_2330_);
goto v___jp_2347_;
}
else
{
lean_object* v___x_2358_; lean_object* v___f_2359_; uint8_t v___x_2360_; lean_object* v___x_2361_; 
lean_del_object(v___x_2345_);
v___x_2358_ = lean_box(v___x_2357_);
v___f_2359_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed), 15, 2);
lean_closure_set(v___f_2359_, 0, v_e_2330_);
lean_closure_set(v___f_2359_, 1, v___x_2358_);
v___x_2360_ = 0;
v___x_2361_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_arg_2354_, v___f_2359_, v___x_2360_, v___x_2360_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_2361_;
}
}
v___jp_2347_:
{
lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2348_ = lean_box(0);
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v___x_2348_);
v___x_2350_ = v___x_2345_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_dec(v_a_2340_);
lean_dec_ref(v_a_2339_);
lean_dec(v_a_2338_);
lean_dec_ref(v_a_2337_);
lean_dec(v_a_2336_);
lean_dec_ref(v_a_2335_);
lean_dec(v_a_2334_);
lean_dec_ref(v_a_2333_);
lean_dec(v_a_2332_);
lean_dec(v_a_2331_);
lean_dec_ref(v_e_2330_);
v_a_2363_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2342_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2342_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___boxed(lean_object* v_e_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(lean_object* v_e_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v___x_2396_; 
lean_inc_ref(v_e_2384_);
v___x_2396_ = l_Lean_Meta_Grind_getRootENode___redArg(v_e_2384_, v_a_2385_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2464_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2399_ = v___x_2396_;
v_isShared_2400_ = v_isSharedCheck_2464_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2396_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2464_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
uint8_t v_ctor_2401_; 
v_ctor_2401_ = lean_ctor_get_uint8(v_a_2397_, sizeof(void*)*11 + 2);
if (v_ctor_2401_ == 0)
{
uint8_t v_interpreted_2402_; 
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
v_interpreted_2402_ = lean_ctor_get_uint8(v_a_2397_, sizeof(void*)*11 + 1);
if (v_interpreted_2402_ == 0)
{
lean_object* v___x_2404_; 
lean_dec(v_a_2397_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v_e_2384_);
v___x_2404_ = v___x_2399_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_e_2384_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
else
{
lean_object* v_self_2406_; lean_object* v___x_2408_; 
lean_dec_ref(v_e_2384_);
v_self_2406_ = lean_ctor_get(v_a_2397_, 0);
lean_inc_ref(v_self_2406_);
lean_dec(v_a_2397_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v_self_2406_);
v___x_2408_ = v___x_2399_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_self_2406_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
else
{
lean_object* v_self_2410_; lean_object* v___x_2411_; 
lean_del_object(v___x_2399_);
lean_dec_ref(v_e_2384_);
v_self_2410_ = lean_ctor_get(v_a_2397_, 0);
lean_inc_ref(v_self_2410_);
lean_dec(v_a_2397_);
lean_inc(v_a_2394_);
lean_inc_ref(v_a_2393_);
lean_inc(v_a_2392_);
lean_inc_ref(v_a_2391_);
lean_inc_ref(v_self_2410_);
v___x_2411_ = l_Lean_Meta_isConstructorApp_x3f(v_self_2410_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2455_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2414_ = v___x_2411_;
v_isShared_2415_ = v_isSharedCheck_2455_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2411_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2455_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
if (lean_obj_tag(v_a_2412_) == 1)
{
lean_object* v_val_2416_; lean_object* v_numParams_2417_; lean_object* v_numFields_2418_; lean_object* v_nargs_2419_; lean_object* v___x_2420_; lean_object* v_dummy_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
lean_del_object(v___x_2414_);
v_val_2416_ = lean_ctor_get(v_a_2412_, 0);
lean_inc(v_val_2416_);
lean_dec_ref(v_a_2412_);
v_numParams_2417_ = lean_ctor_get(v_val_2416_, 3);
lean_inc(v_numParams_2417_);
v_numFields_2418_ = lean_ctor_get(v_val_2416_, 4);
lean_inc(v_numFields_2418_);
lean_dec(v_val_2416_);
v_nargs_2419_ = l_Lean_Expr_getAppNumArgs(v_self_2410_);
v___x_2420_ = lean_nat_add(v_numParams_2417_, v_numFields_2418_);
lean_dec(v_numFields_2418_);
v_dummy_2421_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0, &l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0);
lean_inc(v_nargs_2419_);
v___x_2422_ = lean_mk_array(v_nargs_2419_, v_dummy_2421_);
v___x_2423_ = lean_unsigned_to_nat(1u);
v___x_2424_ = lean_nat_sub(v_nargs_2419_, v___x_2423_);
lean_dec(v_nargs_2419_);
lean_inc_ref(v_self_2410_);
v___x_2425_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_2410_, v___x_2422_, v___x_2424_);
v___x_2426_ = 0;
v___x_2427_ = lean_box(v___x_2426_);
v___x_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2425_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
v___x_2429_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v___x_2420_, v_ctor_2401_, v_numParams_2417_, v___x_2428_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
lean_dec(v___x_2420_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2443_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2443_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2443_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v_snd_2434_; uint8_t v___x_2435_; 
v_snd_2434_ = lean_ctor_get(v_a_2430_, 1);
v___x_2435_ = lean_unbox(v_snd_2434_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2437_; 
lean_dec(v_a_2430_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v_self_2410_);
v___x_2437_ = v___x_2432_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_self_2410_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
else
{
lean_object* v_fst_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
lean_del_object(v___x_2432_);
v_fst_2439_ = lean_ctor_get(v_a_2430_, 0);
lean_inc(v_fst_2439_);
lean_dec(v_a_2430_);
v___x_2440_ = l_Lean_Expr_getAppFn(v_self_2410_);
lean_dec_ref(v_self_2410_);
v___x_2441_ = l_Lean_mkAppN(v___x_2440_, v_fst_2439_);
lean_dec(v_fst_2439_);
v___x_2442_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_2441_, v_a_2390_);
return v___x_2442_;
}
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_dec_ref(v_self_2410_);
v_a_2444_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2429_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2429_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
else
{
lean_object* v___x_2453_; 
lean_dec(v_a_2412_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 0, v_self_2410_);
v___x_2453_ = v___x_2414_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_self_2410_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec_ref(v_self_2410_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
v_a_2456_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2411_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2411_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec_ref(v_e_2384_);
v_a_2465_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2396_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2396_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(lean_object* v_upperBound_2473_, uint8_t v___x_2474_, lean_object* v_a_2475_, lean_object* v_b_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
uint8_t v___x_2488_; 
v___x_2488_ = lean_nat_dec_lt(v_a_2475_, v_upperBound_2473_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; 
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v_a_2475_);
v___x_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2489_, 0, v_b_2476_);
return v___x_2489_;
}
else
{
lean_object* v_fst_2490_; lean_object* v_snd_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2521_; 
v_fst_2490_ = lean_ctor_get(v_b_2476_, 0);
v_snd_2491_ = lean_ctor_get(v_b_2476_, 1);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_b_2476_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2493_ = v_b_2476_;
v_isShared_2494_ = v_isSharedCheck_2521_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_snd_2491_);
lean_inc(v_fst_2490_);
lean_dec(v_b_2476_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2521_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2495_ = l_Lean_instInhabitedExpr;
v___x_2496_ = lean_array_get_borrowed(v___x_2495_, v_fst_2490_, v_a_2475_);
lean_inc(v___y_2486_);
lean_inc_ref(v___y_2485_);
lean_inc(v___y_2484_);
lean_inc_ref(v___y_2483_);
lean_inc(v___x_2496_);
v___x_2497_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v___x_2496_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v_a_2500_; uint8_t v___x_2504_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref(v___x_2497_);
v___x_2504_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2496_, v_a_2498_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2508_; 
lean_dec(v_snd_2491_);
v___x_2505_ = lean_array_set(v_fst_2490_, v_a_2475_, v_a_2498_);
v___x_2506_ = lean_box(v___x_2474_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 1, v___x_2506_);
lean_ctor_set(v___x_2493_, 0, v___x_2505_);
v___x_2508_ = v___x_2493_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2505_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v___x_2506_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
v_a_2500_ = v___x_2508_;
goto v___jp_2499_;
}
}
else
{
lean_object* v___x_2511_; 
lean_dec(v_a_2498_);
if (v_isShared_2494_ == 0)
{
v___x_2511_ = v___x_2493_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_fst_2490_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_snd_2491_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
v_a_2500_ = v___x_2511_;
goto v___jp_2499_;
}
}
v___jp_2499_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = lean_unsigned_to_nat(1u);
v___x_2502_ = lean_nat_add(v_a_2475_, v___x_2501_);
lean_dec(v_a_2475_);
v_a_2475_ = v___x_2502_;
v_b_2476_ = v_a_2500_;
goto _start;
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_del_object(v___x_2493_);
lean_dec(v_snd_2491_);
lean_dec(v_fst_2490_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v_a_2475_);
v_a_2513_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2497_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2497_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg___boxed(lean_object* v_upperBound_2522_, lean_object* v___x_2523_, lean_object* v_a_2524_, lean_object* v_b_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
uint8_t v___x_16698__boxed_2537_; lean_object* v_res_2538_; 
v___x_16698__boxed_2537_ = lean_unbox(v___x_2523_);
v_res_2538_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2522_, v___x_16698__boxed_2537_, v_a_2524_, v_b_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec(v_upperBound_2522_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go___boxed(lean_object* v_e_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_e_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
lean_dec(v_a_2543_);
lean_dec_ref(v_a_2542_);
lean_dec(v_a_2541_);
lean_dec(v_a_2540_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(lean_object* v_upperBound_2552_, uint8_t v___x_2553_, lean_object* v_inst_2554_, lean_object* v_R_2555_, lean_object* v_a_2556_, lean_object* v_b_2557_, lean_object* v_c_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v___x_2570_; 
v___x_2570_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_2552_, v___x_2553_, v_a_2556_, v_b_2557_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_2571_ = _args[0];
lean_object* v___x_2572_ = _args[1];
lean_object* v_inst_2573_ = _args[2];
lean_object* v_R_2574_ = _args[3];
lean_object* v_a_2575_ = _args[4];
lean_object* v_b_2576_ = _args[5];
lean_object* v_c_2577_ = _args[6];
lean_object* v___y_2578_ = _args[7];
lean_object* v___y_2579_ = _args[8];
lean_object* v___y_2580_ = _args[9];
lean_object* v___y_2581_ = _args[10];
lean_object* v___y_2582_ = _args[11];
lean_object* v___y_2583_ = _args[12];
lean_object* v___y_2584_ = _args[13];
lean_object* v___y_2585_ = _args[14];
lean_object* v___y_2586_ = _args[15];
lean_object* v___y_2587_ = _args[16];
lean_object* v___y_2588_ = _args[17];
_start:
{
uint8_t v___x_16969__boxed_2589_; lean_object* v_res_2590_; 
v___x_16969__boxed_2589_ = lean_unbox(v___x_2572_);
v_res_2590_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(v_upperBound_2571_, v___x_16969__boxed_2589_, v_inst_2573_, v_R_2574_, v_a_2575_, v_b_2576_, v_c_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec(v_upperBound_2571_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(lean_object* v_e_2591_, lean_object* v___y_2592_){
_start:
{
uint8_t v___x_2594_; 
v___x_2594_ = l_Lean_Expr_hasMVar(v_e_2591_);
if (v___x_2594_ == 0)
{
lean_object* v___x_2595_; 
v___x_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2595_, 0, v_e_2591_);
return v___x_2595_;
}
else
{
lean_object* v___x_2596_; lean_object* v_mctx_2597_; lean_object* v___x_2598_; lean_object* v_fst_2599_; lean_object* v_snd_2600_; lean_object* v___x_2601_; lean_object* v_cache_2602_; lean_object* v_zetaDeltaFVarIds_2603_; lean_object* v_postponed_2604_; lean_object* v_diag_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2614_; 
v___x_2596_ = lean_st_ref_get(v___y_2592_);
v_mctx_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc_ref(v_mctx_2597_);
lean_dec(v___x_2596_);
v___x_2598_ = l_Lean_instantiateMVarsCore(v_mctx_2597_, v_e_2591_);
v_fst_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_fst_2599_);
v_snd_2600_ = lean_ctor_get(v___x_2598_, 1);
lean_inc(v_snd_2600_);
lean_dec_ref(v___x_2598_);
v___x_2601_ = lean_st_ref_take(v___y_2592_);
v_cache_2602_ = lean_ctor_get(v___x_2601_, 1);
v_zetaDeltaFVarIds_2603_ = lean_ctor_get(v___x_2601_, 2);
v_postponed_2604_ = lean_ctor_get(v___x_2601_, 3);
v_diag_2605_ = lean_ctor_get(v___x_2601_, 4);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2614_ == 0)
{
lean_object* v_unused_2615_; 
v_unused_2615_ = lean_ctor_get(v___x_2601_, 0);
lean_dec(v_unused_2615_);
v___x_2607_ = v___x_2601_;
v_isShared_2608_ = v_isSharedCheck_2614_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_diag_2605_);
lean_inc(v_postponed_2604_);
lean_inc(v_zetaDeltaFVarIds_2603_);
lean_inc(v_cache_2602_);
lean_dec(v___x_2601_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2614_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v_snd_2600_);
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_snd_2600_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v_cache_2602_);
lean_ctor_set(v_reuseFailAlloc_2613_, 2, v_zetaDeltaFVarIds_2603_);
lean_ctor_set(v_reuseFailAlloc_2613_, 3, v_postponed_2604_);
lean_ctor_set(v_reuseFailAlloc_2613_, 4, v_diag_2605_);
v___x_2610_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = lean_st_ref_set(v___y_2592_, v___x_2610_);
v___x_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2612_, 0, v_fst_2599_);
return v___x_2612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg___boxed(lean_object* v_e_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(v_e_2616_, v___y_2617_);
lean_dec(v___y_2617_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(lean_object* v_e_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(v_e_2620_, v___y_2628_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___boxed(lean_object* v_e_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(v_e_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec(v___y_2634_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___lam__0(lean_object* v_k_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = lean_apply_11(v_k_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, lean_box(0));
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___lam__0___boxed(lean_object* v_k_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___lam__0(v_k_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg(lean_object* v_k_2672_, uint8_t v_allowLevelAssignments_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v___f_2685_; lean_object* v___x_2686_; 
v___f_2685_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_2685_, 0, v_k_2672_);
lean_closure_set(v___f_2685_, 1, v___y_2674_);
lean_closure_set(v___f_2685_, 2, v___y_2675_);
lean_closure_set(v___f_2685_, 3, v___y_2676_);
lean_closure_set(v___f_2685_, 4, v___y_2677_);
lean_closure_set(v___f_2685_, 5, v___y_2678_);
lean_closure_set(v___f_2685_, 6, v___y_2679_);
v___x_2686_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2673_, v___f_2685_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
if (lean_obj_tag(v___x_2686_) == 0)
{
return v___x_2686_;
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2686_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2686_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___boxed(lean_object* v_k_2695_, lean_object* v_allowLevelAssignments_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2708_; lean_object* v_res_2709_; 
v_allowLevelAssignments_boxed_2708_ = lean_unbox(v_allowLevelAssignments_2696_);
v_res_2709_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg(v_k_2695_, v_allowLevelAssignments_boxed_2708_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3(lean_object* v_00_u03b1_2710_, lean_object* v_k_2711_, uint8_t v_allowLevelAssignments_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg(v_k_2711_, v_allowLevelAssignments_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___boxed(lean_object* v_00_u03b1_2725_, lean_object* v_k_2726_, lean_object* v_allowLevelAssignments_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2739_; lean_object* v_res_2740_; 
v_allowLevelAssignments_boxed_2739_ = lean_unbox(v_allowLevelAssignments_2727_);
v_res_2740_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3(v_00_u03b1_2725_, v_k_2726_, v_allowLevelAssignments_boxed_2739_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg(lean_object* v_mvarId_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v___x_2744_; lean_object* v_mctx_2745_; lean_object* v_decl_2746_; lean_object* v_depth_2747_; lean_object* v_depth_2748_; uint8_t v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2744_ = lean_st_ref_get(v___y_2742_);
v_mctx_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc_ref(v_mctx_2745_);
lean_dec(v___x_2744_);
lean_inc_ref(v_mctx_2745_);
v_decl_2746_ = l_Lean_MetavarContext_getDecl(v_mctx_2745_, v_mvarId_2741_);
v_depth_2747_ = lean_ctor_get(v_decl_2746_, 3);
lean_inc(v_depth_2747_);
lean_dec_ref(v_decl_2746_);
v_depth_2748_ = lean_ctor_get(v_mctx_2745_, 0);
lean_inc(v_depth_2748_);
lean_dec_ref(v_mctx_2745_);
v___x_2749_ = lean_nat_dec_eq(v_depth_2747_, v_depth_2748_);
lean_dec(v_depth_2748_);
lean_dec(v_depth_2747_);
v___x_2750_ = lean_box(v___x_2749_);
v___x_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg___boxed(lean_object* v_mvarId_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg(v_mvarId_2752_, v___y_2753_);
lean_dec(v___y_2753_);
return v_res_2755_;
}
}
static lean_object* _init_l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7(lean_object* v_msg_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v_toApplicative_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2843_; 
v___x_2773_ = lean_obj_once(&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__0, &l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__0_once, _init_l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__0);
v___x_2774_ = l_ReaderT_instMonad___redArg(v___x_2773_);
v_toApplicative_2775_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2843_ == 0)
{
lean_object* v_unused_2844_; 
v_unused_2844_ = lean_ctor_get(v___x_2774_, 1);
lean_dec(v_unused_2844_);
v___x_2777_ = v___x_2774_;
v_isShared_2778_ = v_isSharedCheck_2843_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_toApplicative_2775_);
lean_dec(v___x_2774_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2843_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v_toFunctor_2779_; lean_object* v_toSeq_2780_; lean_object* v_toSeqLeft_2781_; lean_object* v_toSeqRight_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2841_; 
v_toFunctor_2779_ = lean_ctor_get(v_toApplicative_2775_, 0);
v_toSeq_2780_ = lean_ctor_get(v_toApplicative_2775_, 2);
v_toSeqLeft_2781_ = lean_ctor_get(v_toApplicative_2775_, 3);
v_toSeqRight_2782_ = lean_ctor_get(v_toApplicative_2775_, 4);
v_isSharedCheck_2841_ = !lean_is_exclusive(v_toApplicative_2775_);
if (v_isSharedCheck_2841_ == 0)
{
lean_object* v_unused_2842_; 
v_unused_2842_ = lean_ctor_get(v_toApplicative_2775_, 1);
lean_dec(v_unused_2842_);
v___x_2784_ = v_toApplicative_2775_;
v_isShared_2785_ = v_isSharedCheck_2841_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_toSeqRight_2782_);
lean_inc(v_toSeqLeft_2781_);
lean_inc(v_toSeq_2780_);
lean_inc(v_toFunctor_2779_);
lean_dec(v_toApplicative_2775_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2841_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___f_2786_; lean_object* v___f_2787_; lean_object* v___f_2788_; lean_object* v___f_2789_; lean_object* v___x_2790_; lean_object* v___f_2791_; lean_object* v___f_2792_; lean_object* v___f_2793_; lean_object* v___x_2795_; 
v___f_2786_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__1));
v___f_2787_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__2));
lean_inc_ref(v_toFunctor_2779_);
v___f_2788_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2788_, 0, v_toFunctor_2779_);
v___f_2789_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2789_, 0, v_toFunctor_2779_);
v___x_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___f_2788_);
lean_ctor_set(v___x_2790_, 1, v___f_2789_);
v___f_2791_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2791_, 0, v_toSeqRight_2782_);
v___f_2792_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2792_, 0, v_toSeqLeft_2781_);
v___f_2793_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2793_, 0, v_toSeq_2780_);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 4, v___f_2791_);
lean_ctor_set(v___x_2784_, 3, v___f_2792_);
lean_ctor_set(v___x_2784_, 2, v___f_2793_);
lean_ctor_set(v___x_2784_, 1, v___f_2786_);
lean_ctor_set(v___x_2784_, 0, v___x_2790_);
v___x_2795_ = v___x_2784_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2790_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v___f_2786_);
lean_ctor_set(v_reuseFailAlloc_2840_, 2, v___f_2793_);
lean_ctor_set(v_reuseFailAlloc_2840_, 3, v___f_2792_);
lean_ctor_set(v_reuseFailAlloc_2840_, 4, v___f_2791_);
v___x_2795_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2797_; 
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 1, v___f_2787_);
lean_ctor_set(v___x_2777_, 0, v___x_2795_);
v___x_2797_ = v___x_2777_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2795_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v___f_2787_);
v___x_2797_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
lean_object* v___x_2798_; lean_object* v_toApplicative_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2837_; 
v___x_2798_ = l_ReaderT_instMonad___redArg(v___x_2797_);
v_toApplicative_2799_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2837_ == 0)
{
lean_object* v_unused_2838_; 
v_unused_2838_ = lean_ctor_get(v___x_2798_, 1);
lean_dec(v_unused_2838_);
v___x_2801_ = v___x_2798_;
v_isShared_2802_ = v_isSharedCheck_2837_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_toApplicative_2799_);
lean_dec(v___x_2798_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2837_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v_toFunctor_2803_; lean_object* v_toSeq_2804_; lean_object* v_toSeqLeft_2805_; lean_object* v_toSeqRight_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2835_; 
v_toFunctor_2803_ = lean_ctor_get(v_toApplicative_2799_, 0);
v_toSeq_2804_ = lean_ctor_get(v_toApplicative_2799_, 2);
v_toSeqLeft_2805_ = lean_ctor_get(v_toApplicative_2799_, 3);
v_toSeqRight_2806_ = lean_ctor_get(v_toApplicative_2799_, 4);
v_isSharedCheck_2835_ = !lean_is_exclusive(v_toApplicative_2799_);
if (v_isSharedCheck_2835_ == 0)
{
lean_object* v_unused_2836_; 
v_unused_2836_ = lean_ctor_get(v_toApplicative_2799_, 1);
lean_dec(v_unused_2836_);
v___x_2808_ = v_toApplicative_2799_;
v_isShared_2809_ = v_isSharedCheck_2835_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_toSeqRight_2806_);
lean_inc(v_toSeqLeft_2805_);
lean_inc(v_toSeq_2804_);
lean_inc(v_toFunctor_2803_);
lean_dec(v_toApplicative_2799_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2835_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___f_2810_; lean_object* v___f_2811_; lean_object* v___f_2812_; lean_object* v___f_2813_; lean_object* v___x_2814_; lean_object* v___f_2815_; lean_object* v___f_2816_; lean_object* v___f_2817_; lean_object* v___x_2819_; 
v___f_2810_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__3));
v___f_2811_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___closed__4));
lean_inc_ref(v_toFunctor_2803_);
v___f_2812_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2812_, 0, v_toFunctor_2803_);
v___f_2813_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2813_, 0, v_toFunctor_2803_);
v___x_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___f_2812_);
lean_ctor_set(v___x_2814_, 1, v___f_2813_);
v___f_2815_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2815_, 0, v_toSeqRight_2806_);
v___f_2816_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2816_, 0, v_toSeqLeft_2805_);
v___f_2817_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2817_, 0, v_toSeq_2804_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 4, v___f_2815_);
lean_ctor_set(v___x_2808_, 3, v___f_2816_);
lean_ctor_set(v___x_2808_, 2, v___f_2817_);
lean_ctor_set(v___x_2808_, 1, v___f_2810_);
lean_ctor_set(v___x_2808_, 0, v___x_2814_);
v___x_2819_ = v___x_2808_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2814_);
lean_ctor_set(v_reuseFailAlloc_2834_, 1, v___f_2810_);
lean_ctor_set(v_reuseFailAlloc_2834_, 2, v___f_2817_);
lean_ctor_set(v_reuseFailAlloc_2834_, 3, v___f_2816_);
lean_ctor_set(v_reuseFailAlloc_2834_, 4, v___f_2815_);
v___x_2819_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
lean_object* v___x_2821_; 
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 1, v___f_2811_);
lean_ctor_set(v___x_2801_, 0, v___x_2819_);
v___x_2821_ = v___x_2801_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2819_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v___f_2811_);
v___x_2821_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_103424__overap_2831_; lean_object* v___x_2832_; 
v___x_2822_ = l_ReaderT_instMonad___redArg(v___x_2821_);
v___x_2823_ = l_ReaderT_instMonad___redArg(v___x_2822_);
v___x_2824_ = l_ReaderT_instMonad___redArg(v___x_2823_);
v___x_2825_ = l_ReaderT_instMonad___redArg(v___x_2824_);
v___x_2826_ = l_ReaderT_instMonad___redArg(v___x_2825_);
v___x_2827_ = l_ReaderT_instMonad___redArg(v___x_2826_);
v___x_2828_ = 0;
v___x_2829_ = lean_box(v___x_2828_);
v___x_2830_ = l_instInhabitedOfMonad___redArg(v___x_2827_, v___x_2829_);
v___x_103424__overap_2831_ = lean_panic_fn(v___x_2830_, v_msg_2761_);
v___x_2832_ = lean_apply_11(v___x_103424__overap_2831_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, lean_box(0));
return v___x_2832_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_msg_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7(v_msg_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___redArg(lean_object* v_keys_2858_, lean_object* v_vals_2859_, lean_object* v_i_2860_, lean_object* v_k_2861_){
_start:
{
lean_object* v___x_2862_; uint8_t v___x_2863_; 
v___x_2862_ = lean_array_get_size(v_keys_2858_);
v___x_2863_ = lean_nat_dec_lt(v_i_2860_, v___x_2862_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; 
lean_dec(v_i_2860_);
v___x_2864_ = lean_box(0);
return v___x_2864_;
}
else
{
lean_object* v_k_x27_2865_; uint8_t v___x_2866_; 
v_k_x27_2865_ = lean_array_fget_borrowed(v_keys_2858_, v_i_2860_);
v___x_2866_ = l_Lean_instBEqLevelMVarId_beq(v_k_2861_, v_k_x27_2865_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = lean_unsigned_to_nat(1u);
v___x_2868_ = lean_nat_add(v_i_2860_, v___x_2867_);
lean_dec(v_i_2860_);
v_i_2860_ = v___x_2868_;
goto _start;
}
else
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = lean_array_fget_borrowed(v_vals_2859_, v_i_2860_);
lean_dec(v_i_2860_);
lean_inc(v___x_2870_);
v___x_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
return v___x_2871_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_keys_2872_, lean_object* v_vals_2873_, lean_object* v_i_2874_, lean_object* v_k_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___redArg(v_keys_2872_, v_vals_2873_, v_i_2874_, v_k_2875_);
lean_dec(v_k_2875_);
lean_dec_ref(v_vals_2873_);
lean_dec_ref(v_keys_2872_);
return v_res_2876_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__0(void){
_start:
{
size_t v___x_2877_; size_t v___x_2878_; size_t v___x_2879_; 
v___x_2877_ = ((size_t)5ULL);
v___x_2878_ = ((size_t)1ULL);
v___x_2879_ = lean_usize_shift_left(v___x_2878_, v___x_2877_);
return v___x_2879_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__1(void){
_start:
{
size_t v___x_2880_; size_t v___x_2881_; size_t v___x_2882_; 
v___x_2880_ = ((size_t)1ULL);
v___x_2881_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__0);
v___x_2882_ = lean_usize_sub(v___x_2881_, v___x_2880_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg(lean_object* v_x_2883_, size_t v_x_2884_, lean_object* v_x_2885_){
_start:
{
if (lean_obj_tag(v_x_2883_) == 0)
{
lean_object* v_es_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2907_; 
v_es_2886_ = lean_ctor_get(v_x_2883_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v_x_2883_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2888_ = v_x_2883_;
v_isShared_2889_ = v_isSharedCheck_2907_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_es_2886_);
lean_dec(v_x_2883_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2907_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; size_t v___x_2891_; size_t v___x_2892_; size_t v___x_2893_; lean_object* v_j_2894_; lean_object* v___x_2895_; 
v___x_2890_ = lean_box(2);
v___x_2891_ = ((size_t)5ULL);
v___x_2892_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___closed__1);
v___x_2893_ = lean_usize_land(v_x_2884_, v___x_2892_);
v_j_2894_ = lean_usize_to_nat(v___x_2893_);
v___x_2895_ = lean_array_get(v___x_2890_, v_es_2886_, v_j_2894_);
lean_dec(v_j_2894_);
lean_dec_ref(v_es_2886_);
switch(lean_obj_tag(v___x_2895_))
{
case 0:
{
lean_object* v_key_2896_; lean_object* v_val_2897_; uint8_t v___x_2898_; 
v_key_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_key_2896_);
v_val_2897_ = lean_ctor_get(v___x_2895_, 1);
lean_inc(v_val_2897_);
lean_dec_ref(v___x_2895_);
v___x_2898_ = l_Lean_instBEqLevelMVarId_beq(v_x_2885_, v_key_2896_);
lean_dec(v_key_2896_);
if (v___x_2898_ == 0)
{
lean_object* v___x_2899_; 
lean_dec(v_val_2897_);
lean_del_object(v___x_2888_);
v___x_2899_ = lean_box(0);
return v___x_2899_;
}
else
{
lean_object* v___x_2901_; 
if (v_isShared_2889_ == 0)
{
lean_ctor_set_tag(v___x_2888_, 1);
lean_ctor_set(v___x_2888_, 0, v_val_2897_);
v___x_2901_ = v___x_2888_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_val_2897_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
case 1:
{
lean_object* v_node_2903_; size_t v___x_2904_; 
lean_del_object(v___x_2888_);
v_node_2903_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_node_2903_);
lean_dec_ref(v___x_2895_);
v___x_2904_ = lean_usize_shift_right(v_x_2884_, v___x_2891_);
v_x_2883_ = v_node_2903_;
v_x_2884_ = v___x_2904_;
goto _start;
}
default: 
{
lean_object* v___x_2906_; 
lean_del_object(v___x_2888_);
v___x_2906_ = lean_box(0);
return v___x_2906_;
}
}
}
}
else
{
lean_object* v_ks_2908_; lean_object* v_vs_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v_ks_2908_ = lean_ctor_get(v_x_2883_, 0);
lean_inc_ref(v_ks_2908_);
v_vs_2909_ = lean_ctor_get(v_x_2883_, 1);
lean_inc_ref(v_vs_2909_);
lean_dec_ref(v_x_2883_);
v___x_2910_ = lean_unsigned_to_nat(0u);
v___x_2911_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___redArg(v_ks_2908_, v_vs_2909_, v___x_2910_, v_x_2885_);
lean_dec_ref(v_vs_2909_);
lean_dec_ref(v_ks_2908_);
return v___x_2911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_x_2912_, lean_object* v_x_2913_, lean_object* v_x_2914_){
_start:
{
size_t v_x_104208__boxed_2915_; lean_object* v_res_2916_; 
v_x_104208__boxed_2915_ = lean_unbox_usize(v_x_2913_);
lean_dec(v_x_2913_);
v_res_2916_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg(v_x_2912_, v_x_104208__boxed_2915_, v_x_2914_);
lean_dec(v_x_2914_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_2917_, lean_object* v_x_2918_){
_start:
{
uint64_t v___x_2919_; size_t v___x_2920_; lean_object* v___x_2921_; 
v___x_2919_ = l_Lean_instHashableLevelMVarId_hash(v_x_2918_);
v___x_2920_ = lean_uint64_to_usize(v___x_2919_);
v___x_2921_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg(v_x_2917_, v___x_2920_, v_x_2918_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_x_2922_, lean_object* v_x_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___redArg(v_x_2922_, v_x_2923_);
lean_dec(v_x_2923_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5(lean_object* v_mvarId_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v___x_2940_; lean_object* v_mctx_2941_; lean_object* v_levelAssignDepth_2942_; lean_object* v_lDepth_2943_; lean_object* v___x_2944_; 
v___x_2940_ = lean_st_ref_get(v___y_2936_);
v_mctx_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc_ref(v_mctx_2941_);
lean_dec(v___x_2940_);
v_levelAssignDepth_2942_ = lean_ctor_get(v_mctx_2941_, 1);
lean_inc(v_levelAssignDepth_2942_);
v_lDepth_2943_ = lean_ctor_get(v_mctx_2941_, 3);
lean_inc_ref(v_lDepth_2943_);
lean_dec_ref(v_mctx_2941_);
v___x_2944_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___redArg(v_lDepth_2943_, v_mvarId_2928_);
if (lean_obj_tag(v___x_2944_) == 1)
{
lean_object* v_val_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2954_; 
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec(v_mvarId_2928_);
v_val_2945_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2947_ = v___x_2944_;
v_isShared_2948_ = v_isSharedCheck_2954_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_val_2945_);
lean_dec(v___x_2944_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2954_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
uint8_t v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2952_; 
v___x_2949_ = lean_nat_dec_le(v_levelAssignDepth_2942_, v_val_2945_);
lean_dec(v_val_2945_);
lean_dec(v_levelAssignDepth_2942_);
v___x_2950_ = lean_box(v___x_2949_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set_tag(v___x_2947_, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2950_);
v___x_2952_ = v___x_2947_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2950_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
else
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
lean_dec(v___x_2944_);
lean_dec(v_levelAssignDepth_2942_);
v___x_2955_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___closed__0));
v___x_2956_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___closed__1));
v___x_2957_ = lean_unsigned_to_nat(451u);
v___x_2958_ = lean_unsigned_to_nat(14u);
v___x_2959_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___closed__2));
v___x_2960_ = 1;
v___x_2961_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_2928_, v___x_2960_);
v___x_2962_ = lean_string_append(v___x_2959_, v___x_2961_);
lean_dec_ref(v___x_2961_);
v___x_2963_ = l_mkPanicMessageWithDecl(v___x_2955_, v___x_2956_, v___x_2957_, v___x_2958_, v___x_2962_);
lean_dec_ref(v___x_2962_);
v___x_2964_ = l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__7(v___x_2963_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
return v___x_2964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5___boxed(lean_object* v_mvarId_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5(v_mvarId_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(lean_object* v_x_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v___y_2991_; lean_object* v___y_2992_; uint8_t v_a_2993_; lean_object* v_lvl_u2081_2999_; lean_object* v_lvl_u2082_3000_; 
switch(lean_obj_tag(v_x_2978_))
{
case 1:
{
lean_object* v_a_3007_; uint8_t v___x_3008_; 
v_a_3007_ = lean_ctor_get(v_x_2978_, 0);
lean_inc(v_a_3007_);
lean_dec_ref(v_x_2978_);
v___x_3008_ = l_Lean_Level_hasMVar(v_a_3007_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
lean_dec(v_a_3007_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec(v___y_2979_);
v___x_3009_ = lean_box(v___x_3008_);
v___x_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
return v___x_3010_;
}
else
{
v_x_2978_ = v_a_3007_;
goto _start;
}
}
case 2:
{
lean_object* v_a_3012_; lean_object* v_a_3013_; 
v_a_3012_ = lean_ctor_get(v_x_2978_, 0);
lean_inc(v_a_3012_);
v_a_3013_ = lean_ctor_get(v_x_2978_, 1);
lean_inc(v_a_3013_);
lean_dec_ref(v_x_2978_);
v_lvl_u2081_2999_ = v_a_3012_;
v_lvl_u2082_3000_ = v_a_3013_;
goto v___jp_2998_;
}
case 3:
{
lean_object* v_a_3014_; lean_object* v_a_3015_; 
v_a_3014_ = lean_ctor_get(v_x_2978_, 0);
lean_inc(v_a_3014_);
v_a_3015_ = lean_ctor_get(v_x_2978_, 1);
lean_inc(v_a_3015_);
lean_dec_ref(v_x_2978_);
v_lvl_u2081_2999_ = v_a_3014_;
v_lvl_u2082_3000_ = v_a_3015_;
goto v___jp_2998_;
}
case 5:
{
lean_object* v_a_3016_; lean_object* v___x_3017_; 
v_a_3016_ = lean_ctor_get(v_x_2978_, 0);
lean_inc(v_a_3016_);
lean_dec_ref(v_x_2978_);
v___x_3017_ = l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5(v_a_3016_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
return v___x_3017_;
}
default: 
{
uint8_t v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec(v___y_2979_);
lean_dec(v_x_2978_);
v___x_3018_ = 0;
v___x_3019_ = lean_box(v___x_3018_);
v___x_3020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
return v___x_3020_;
}
}
v___jp_2990_:
{
if (v_a_2993_ == 0)
{
uint8_t v___x_2994_; 
lean_dec_ref(v___y_2992_);
v___x_2994_ = l_Lean_Level_hasMVar(v___y_2991_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
lean_dec(v___y_2991_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec(v___y_2979_);
v___x_2995_ = lean_box(v___x_2994_);
v___x_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2995_);
return v___x_2996_;
}
else
{
v_x_2978_ = v___y_2991_;
goto _start;
}
}
else
{
lean_dec(v___y_2991_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec(v___y_2979_);
return v___y_2992_;
}
}
v___jp_2998_:
{
uint8_t v___x_3001_; 
v___x_3001_ = l_Lean_Level_hasMVar(v_lvl_u2081_2999_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
lean_dec(v_lvl_u2081_2999_);
v___x_3002_ = lean_box(v___x_3001_);
v___x_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
v___y_2991_ = v_lvl_u2082_3000_;
v___y_2992_ = v___x_3003_;
v_a_2993_ = v___x_3001_;
goto v___jp_2990_;
}
else
{
lean_object* v___x_3004_; 
lean_inc(v___y_2988_);
lean_inc_ref(v___y_2987_);
lean_inc(v___y_2986_);
lean_inc_ref(v___y_2985_);
lean_inc(v___y_2984_);
lean_inc_ref(v___y_2983_);
lean_inc(v___y_2982_);
lean_inc_ref(v___y_2981_);
lean_inc(v___y_2980_);
lean_inc(v___y_2979_);
v___x_3004_ = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(v_lvl_u2081_2999_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; uint8_t v___x_3006_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
v___x_3006_ = lean_unbox(v_a_3005_);
lean_dec(v_a_3005_);
v___y_2991_ = v_lvl_u2082_3000_;
v___y_2992_ = v___x_3004_;
v_a_2993_ = v___x_3006_;
goto v___jp_2990_;
}
else
{
lean_dec(v_lvl_u2082_3000_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec(v___y_2979_);
return v___x_3004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___boxed(lean_object* v_x_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(v_x_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4(lean_object* v_x_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
if (lean_obj_tag(v_x_3034_) == 0)
{
uint8_t v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
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
v___x_3046_ = 0;
v___x_3047_ = lean_box(v___x_3046_);
v___x_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
return v___x_3048_;
}
else
{
lean_object* v_head_3049_; lean_object* v_tail_3050_; lean_object* v___x_3051_; 
v_head_3049_ = lean_ctor_get(v_x_3034_, 0);
lean_inc(v_head_3049_);
v_tail_3050_ = lean_ctor_get(v_x_3034_, 1);
lean_inc(v_tail_3050_);
lean_dec_ref(v_x_3034_);
lean_inc(v___y_3044_);
lean_inc_ref(v___y_3043_);
lean_inc(v___y_3042_);
lean_inc_ref(v___y_3041_);
lean_inc(v___y_3040_);
lean_inc_ref(v___y_3039_);
lean_inc(v___y_3038_);
lean_inc_ref(v___y_3037_);
lean_inc(v___y_3036_);
lean_inc(v___y_3035_);
v___x_3051_ = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(v_head_3049_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_a_3052_; uint8_t v___x_3053_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc(v_a_3052_);
v___x_3053_ = lean_unbox(v_a_3052_);
lean_dec(v_a_3052_);
if (v___x_3053_ == 0)
{
lean_dec_ref(v___x_3051_);
v_x_3034_ = v_tail_3050_;
goto _start;
}
else
{
lean_dec(v_tail_3050_);
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
return v___x_3051_;
}
}
else
{
lean_dec(v_tail_3050_);
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
return v___x_3051_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4___boxed(lean_object* v_x_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l_List_anyM___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4(v_x_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(lean_object* v_x_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v___y_3081_; lean_object* v___y_3082_; uint8_t v_a_3083_; lean_object* v_d_3089_; lean_object* v_b_3090_; 
switch(lean_obj_tag(v_x_3068_))
{
case 2:
{
lean_object* v_mvarId_3097_; lean_object* v___x_3098_; 
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3069_);
v_mvarId_3097_ = lean_ctor_get(v_x_3068_, 0);
lean_inc(v_mvarId_3097_);
lean_dec_ref(v_x_3068_);
v___x_3098_ = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg(v_mvarId_3097_, v___y_3076_);
lean_dec(v___y_3076_);
return v___x_3098_;
}
case 3:
{
lean_object* v_u_3099_; lean_object* v___x_3100_; 
v_u_3099_ = lean_ctor_get(v_x_3068_, 0);
lean_inc(v_u_3099_);
lean_dec_ref(v_x_3068_);
v___x_3100_ = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(v_u_3099_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
return v___x_3100_;
}
case 4:
{
lean_object* v_us_3101_; lean_object* v___x_3102_; 
v_us_3101_ = lean_ctor_get(v_x_3068_, 1);
lean_inc(v_us_3101_);
lean_dec_ref(v_x_3068_);
v___x_3102_ = l_List_anyM___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4(v_us_3101_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
return v___x_3102_;
}
case 5:
{
lean_object* v_fn_3103_; lean_object* v_arg_3104_; lean_object* v___y_3106_; uint8_t v_a_3107_; uint8_t v___x_3112_; 
v_fn_3103_ = lean_ctor_get(v_x_3068_, 0);
lean_inc_ref(v_fn_3103_);
v_arg_3104_ = lean_ctor_get(v_x_3068_, 1);
lean_inc_ref(v_arg_3104_);
lean_dec_ref(v_x_3068_);
v___x_3112_ = l_Lean_Expr_hasMVar(v_fn_3103_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
lean_dec_ref(v_fn_3103_);
v___x_3113_ = lean_box(v___x_3112_);
v___x_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3113_);
v___y_3106_ = v___x_3114_;
v_a_3107_ = v___x_3112_;
goto v___jp_3105_;
}
else
{
lean_object* v___x_3115_; 
lean_inc(v___y_3078_);
lean_inc_ref(v___y_3077_);
lean_inc(v___y_3076_);
lean_inc_ref(v___y_3075_);
lean_inc(v___y_3074_);
lean_inc_ref(v___y_3073_);
lean_inc(v___y_3072_);
lean_inc_ref(v___y_3071_);
lean_inc(v___y_3070_);
lean_inc(v___y_3069_);
v___x_3115_ = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_fn_3103_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3116_; uint8_t v___x_3117_; 
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
lean_inc(v_a_3116_);
v___x_3117_ = lean_unbox(v_a_3116_);
lean_dec(v_a_3116_);
v___y_3106_ = v___x_3115_;
v_a_3107_ = v___x_3117_;
goto v___jp_3105_;
}
else
{
lean_dec_ref(v_arg_3104_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3069_);
return v___x_3115_;
}
}
v___jp_3105_:
{
if (v_a_3107_ == 0)
{
uint8_t v___x_3108_; 
lean_dec_ref(v___y_3106_);
v___x_3108_ = l_Lean_Expr_hasMVar(v_arg_3104_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; lean_object* v___x_3110_; 
lean_dec_ref(v_arg_3104_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3069_);
v___x_3109_ = lean_box(v___x_3108_);
v___x_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3109_);
return v___x_3110_;
}
else
{
v_x_3068_ = v_arg_3104_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_3104_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3069_);
return v___y_3106_;
}
}
}
case 6:
{
lean_object* v_binderType_3118_; lean_object* v_body_3119_; 
v_binderType_3118_ = lean_ctor_get(v_x_3068_, 1);
lean_inc_ref(v_binderType_3118_);
v_body_3119_ = lean_ctor_get(v_x_3068_, 2);
lean_inc_ref(v_body_3119_);
lean_dec_ref(v_x_3068_);
v_d_3089_ = v_binderType_3118_;
v_b_3090_ = v_body_3119_;
goto v___jp_3088_;
}
case 7:
{
lean_object* v_binderType_3120_; lean_object* v_body_3121_; 
v_binderType_3120_ = lean_ctor_get(v_x_3068_, 1);
lean_inc_ref(v_binderType_3120_);
v_body_3121_ = lean_ctor_get(v_x_3068_, 2);
lean_inc_ref(v_body_3121_);
lean_dec_ref(v_x_3068_);
v_d_3089_ = v_binderType_3120_;
v_b_3090_ = v_body_3121_;
goto v___jp_3088_;
}
case 8:
{
lean_object* v_type_3122_; lean_object* v_value_3123_; lean_object* v_body_3124_; lean_object* v___y_3126_; uint8_t v_a_3127_; lean_object* v___y_3133_; uint8_t v_a_3134_; uint8_t v___x_3141_; 
v_type_3122_ = lean_ctor_get(v_x_3068_, 1);
lean_inc_ref(v_type_3122_);
v_value_3123_ = lean_ctor_get(v_x_3068_, 2);
lean_inc_ref(v_value_3123_);
v_body_3124_ = lean_ctor_get(v_x_3068_, 3);
lean_inc_ref(v_body_3124_);
lean_dec_ref(v_x_3068_);
v___x_3141_ = l_Lean_Expr_hasMVar(v_type_3122_);
if (v___x_3141_ == 0)
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
lean_dec_ref(v_type_3122_);
v___x_3142_ = lean_box(v___x_3141_);
v___x_3143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
v___y_3133_ = v___x_3143_;
v_a_3134_ = v___x_3141_;
goto v___jp_3132_;
}
else
{
lean_object* v___x_3144_; 
lean_inc(v___y_3078_);
lean_inc_ref(v___y_3077_);
lean_inc(v___y_3076_);
lean_inc_ref(v___y_3075_);
lean_inc(v___y_3074_);
lean_inc_ref(v___y_3073_);
lean_inc(v___y_3072_);
lean_inc_ref(v___y_3071_);
lean_inc(v___y_3070_);
lean_inc(v___y_3069_);
v___x_3144_ = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_type_3122_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; uint8_t v___x_3146_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
v___x_3146_ = lean_unbox(v_a_3145_);
lean_dec(v_a_3145_);
v___y_3133_ = v___x_3144_;
v_a_3134_ = v___x_3146_;
goto v___jp_3132_;
}
else
{
lean_dec_ref(v_body_3124_);
lean_dec_ref(v_value_3123_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3069_);
return v___x_3144_;
}
}
v___jp_3125_:
{
if (v_a_3127_ == 0)
{
uint8_t v___x_3128_; 
lean_dec_ref(v___y_3126_);
v___x_3128_ = l_Lean_Expr_hasMVar(v_body_3124_);
if (v___x_3128_ == 0)
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
lean_dec_ref(v_body_3124_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3069_);
v___x_3129_ = lean_box(v___x_3128_);
v___x_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3129_);
return v___x_3130_;
}
else
{
v_x_3068_ = v_body_3124_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_3124_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3069_);
return v___y_3126_;
}
}
v___jp_3132_:
{
if (v_a_3134_ == 0)
{
uint8_t v___x_3135_; 
lean_dec_ref(v___y_3133_);
v___x_3135_ = l_Lean_Expr_hasMVar(v_value_3123_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
lean_dec_ref(v_value_3123_);
v___x_3136_ = lean_box(v___x_3135_);
v___x_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
v___y_3126_ = v___x_3137_;
v_a_3127_ = v___x_3135_;
goto v___jp_3125_;
}
else
{
lean_object* v___x_3138_; 
lean_inc(v___y_3078_);
lean_inc_ref(v___y_3077_);
lean_inc(v___y_3076_);
lean_inc_ref(v___y_3075_);
lean_inc(v___y_3074_);
lean_inc_ref(v___y_3073_);
lean_inc(v___y_3072_);
lean_inc_ref(v___y_3071_);
lean_inc(v___y_3070_);
lean_inc(v___y_3069_);
v___x_3138_ = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_value_3123_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; uint8_t v___x_3140_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc(v_a_3139_);
v___x_3140_ = lean_unbox(v_a_3139_);
lean_dec(v_a_3139_);
v___y_3126_ = v___x_3138_;
v_a_3127_ = v___x_3140_;
goto v___jp_3125_;
}
else
{
lean_dec_ref(v_body_3124_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3069_);
return v___x_3138_;
}
}
}
else
{
lean_dec_ref(v_body_3124_);
lean_dec_ref(v_value_3123_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3069_);
return v___y_3133_;
}
}
}
case 10:
{
lean_object* v_expr_3147_; uint8_t v___x_3148_; 
v_expr_3147_ = lean_ctor_get(v_x_3068_, 1);
lean_inc_ref(v_expr_3147_);
lean_dec_ref(v_x_3068_);
v___x_3148_ = l_Lean_Expr_hasMVar(v_expr_3147_);
if (v___x_3148_ == 0)
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
lean_dec_ref(v_expr_3147_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3069_);
v___x_3149_ = lean_box(v___x_3148_);
v___x_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
return v___x_3150_;
}
else
{
v_x_3068_ = v_expr_3147_;
goto _start;
}
}
case 11:
{
lean_object* v_struct_3152_; uint8_t v___x_3153_; 
v_struct_3152_ = lean_ctor_get(v_x_3068_, 2);
lean_inc_ref(v_struct_3152_);
lean_dec_ref(v_x_3068_);
v___x_3153_ = l_Lean_Expr_hasMVar(v_struct_3152_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
lean_dec_ref(v_struct_3152_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3069_);
v___x_3154_ = lean_box(v___x_3153_);
v___x_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
return v___x_3155_;
}
else
{
v_x_3068_ = v_struct_3152_;
goto _start;
}
}
default: 
{
uint8_t v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v_x_3068_);
v___x_3157_ = 0;
v___x_3158_ = lean_box(v___x_3157_);
v___x_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3158_);
return v___x_3159_;
}
}
v___jp_3080_:
{
if (v_a_3083_ == 0)
{
uint8_t v___x_3084_; 
lean_dec_ref(v___y_3082_);
v___x_3084_ = l_Lean_Expr_hasMVar(v___y_3081_);
if (v___x_3084_ == 0)
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3069_);
v___x_3085_ = lean_box(v___x_3084_);
v___x_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
return v___x_3086_;
}
else
{
v_x_3068_ = v___y_3081_;
goto _start;
}
}
else
{
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3069_);
return v___y_3082_;
}
}
v___jp_3088_:
{
uint8_t v___x_3091_; 
v___x_3091_ = l_Lean_Expr_hasMVar(v_d_3089_);
if (v___x_3091_ == 0)
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
lean_dec_ref(v_d_3089_);
v___x_3092_ = lean_box(v___x_3091_);
v___x_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3092_);
v___y_3081_ = v_b_3090_;
v___y_3082_ = v___x_3093_;
v_a_3083_ = v___x_3091_;
goto v___jp_3080_;
}
else
{
lean_object* v___x_3094_; 
lean_inc(v___y_3078_);
lean_inc_ref(v___y_3077_);
lean_inc(v___y_3076_);
lean_inc_ref(v___y_3075_);
lean_inc(v___y_3074_);
lean_inc_ref(v___y_3073_);
lean_inc(v___y_3072_);
lean_inc_ref(v___y_3071_);
lean_inc(v___y_3070_);
lean_inc(v___y_3069_);
v___x_3094_ = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_d_3089_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; uint8_t v___x_3096_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_a_3095_);
v___x_3096_ = lean_unbox(v_a_3095_);
lean_dec(v_a_3095_);
v___y_3081_ = v_b_3090_;
v___y_3082_ = v___x_3094_;
v_a_3083_ = v___x_3096_;
goto v___jp_3080_;
}
else
{
lean_dec_ref(v_b_3090_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3069_);
return v___x_3094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___boxed(lean_object* v_x_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_x_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
return v_res_3172_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3));
v___x_3183_ = l_Lean_stringToMessageData(v___x_3182_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(lean_object* v_as_3184_, size_t v_sz_3185_, size_t v_i_3186_, lean_object* v_b_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v_a_3200_; uint8_t v___x_3204_; 
v___x_3204_ = lean_usize_dec_lt(v_i_3186_, v_sz_3185_);
if (v___x_3204_ == 0)
{
lean_object* v___x_3205_; 
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3188_);
v___x_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3205_, 0, v_b_3187_);
return v___x_3205_;
}
else
{
lean_object* v_snd_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3399_; 
v_snd_3206_ = lean_ctor_get(v_b_3187_, 1);
v_isSharedCheck_3399_ = !lean_is_exclusive(v_b_3187_);
if (v_isSharedCheck_3399_ == 0)
{
lean_object* v_unused_3400_; 
v_unused_3400_ = lean_ctor_get(v_b_3187_, 0);
lean_dec(v_unused_3400_);
v___x_3208_ = v_b_3187_;
v_isShared_3209_ = v_isSharedCheck_3399_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_snd_3206_);
lean_dec(v_b_3187_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3399_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v_array_3210_; lean_object* v_start_3211_; lean_object* v_stop_3212_; lean_object* v___x_3213_; uint8_t v___x_3214_; 
v_array_3210_ = lean_ctor_get(v_snd_3206_, 0);
v_start_3211_ = lean_ctor_get(v_snd_3206_, 1);
v_stop_3212_ = lean_ctor_get(v_snd_3206_, 2);
v___x_3213_ = lean_box(0);
v___x_3214_ = lean_nat_dec_lt(v_start_3211_, v_stop_3212_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3216_; 
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3188_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v___x_3213_);
v___x_3216_ = v___x_3208_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3213_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v_snd_3206_);
v___x_3216_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
return v___x_3217_;
}
}
else
{
lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3395_; 
lean_inc(v_stop_3212_);
lean_inc(v_start_3211_);
lean_inc_ref(v_array_3210_);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_snd_3206_);
if (v_isSharedCheck_3395_ == 0)
{
lean_object* v_unused_3396_; lean_object* v_unused_3397_; lean_object* v_unused_3398_; 
v_unused_3396_ = lean_ctor_get(v_snd_3206_, 2);
lean_dec(v_unused_3396_);
v_unused_3397_ = lean_ctor_get(v_snd_3206_, 1);
lean_dec(v_unused_3397_);
v_unused_3398_ = lean_ctor_get(v_snd_3206_, 0);
lean_dec(v_unused_3398_);
v___x_3220_ = v_snd_3206_;
v_isShared_3221_ = v_isSharedCheck_3395_;
goto v_resetjp_3219_;
}
else
{
lean_dec(v_snd_3206_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3395_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3226_; 
v___x_3222_ = lean_array_fget(v_array_3210_, v_start_3211_);
v___x_3223_ = lean_unsigned_to_nat(1u);
v___x_3224_ = lean_nat_add(v_start_3211_, v___x_3223_);
lean_dec(v_start_3211_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 1, v___x_3224_);
v___x_3226_ = v___x_3220_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_array_3210_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v___x_3224_);
lean_ctor_set(v_reuseFailAlloc_3394_, 2, v_stop_3212_);
v___x_3226_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
uint8_t v___x_3227_; 
v___x_3227_ = lean_unbox(v___x_3222_);
lean_dec(v___x_3222_);
if (v___x_3227_ == 0)
{
lean_object* v___x_3229_; 
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 1, v___x_3226_);
lean_ctor_set(v___x_3208_, 0, v___x_3213_);
v___x_3229_ = v___x_3208_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3213_);
lean_ctor_set(v_reuseFailAlloc_3230_, 1, v___x_3226_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
v_a_3200_ = v___x_3229_;
goto v___jp_3199_;
}
}
else
{
lean_object* v_a_3231_; lean_object* v_____x_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___x_3269_; 
v_a_3231_ = lean_array_uget_borrowed(v_as_3184_, v_i_3186_);
lean_inc(v___y_3197_);
lean_inc_ref(v___y_3196_);
lean_inc(v___y_3195_);
lean_inc_ref(v___y_3194_);
lean_inc(v_a_3231_);
v___x_3269_ = lean_infer_type(v_a_3231_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3385_; 
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3272_ = v___x_3269_;
v_isShared_3273_ = v_isSharedCheck_3385_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3269_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3385_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3274_; 
v___x_3274_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_a_3270_);
if (lean_obj_tag(v___x_3274_) == 1)
{
lean_object* v_val_3275_; lean_object* v_snd_3276_; lean_object* v_fst_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3379_; 
lean_del_object(v___x_3272_);
v_val_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_val_3275_);
lean_dec_ref(v___x_3274_);
v_snd_3276_ = lean_ctor_get(v_val_3275_, 1);
v_fst_3277_ = lean_ctor_get(v_val_3275_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v_val_3275_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3279_ = v_val_3275_;
v_isShared_3280_ = v_isSharedCheck_3379_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_snd_3276_);
lean_inc(v_fst_3277_);
lean_dec(v_val_3275_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3379_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v_fst_3281_; lean_object* v_snd_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3378_; 
v_fst_3281_ = lean_ctor_get(v_snd_3276_, 0);
v_snd_3282_ = lean_ctor_get(v_snd_3276_, 1);
v_isSharedCheck_3378_ = !lean_is_exclusive(v_snd_3276_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3284_ = v_snd_3276_;
v_isShared_3285_ = v_isSharedCheck_3378_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_snd_3282_);
lean_inc(v_fst_3281_);
lean_dec(v_snd_3276_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3378_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3286_; 
lean_inc(v___y_3197_);
lean_inc_ref(v___y_3196_);
lean_inc(v___y_3195_);
lean_inc_ref(v___y_3194_);
lean_inc(v_fst_3281_);
v___x_3286_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_fst_3281_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v_cls_3342_; lean_object* v___x_3343_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3287_);
lean_dec_ref(v___x_3286_);
v_cls_3342_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2));
v___x_3343_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3342_, v___y_3196_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; uint8_t v___x_3345_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
lean_inc(v_a_3344_);
lean_dec_ref(v___x_3343_);
v___x_3345_ = lean_unbox(v_a_3344_);
lean_dec(v_a_3344_);
if (v___x_3345_ == 0)
{
lean_del_object(v___x_3279_);
lean_inc(v___y_3197_);
lean_inc_ref(v___y_3196_);
lean_inc(v___y_3195_);
lean_inc_ref(v___y_3194_);
lean_inc(v___y_3193_);
lean_inc_ref(v___y_3192_);
lean_inc(v___y_3191_);
lean_inc_ref(v___y_3190_);
lean_inc(v___y_3189_);
lean_inc(v___y_3188_);
v___y_3289_ = v___y_3188_;
v___y_3290_ = v___y_3189_;
v___y_3291_ = v___y_3190_;
v___y_3292_ = v___y_3191_;
v___y_3293_ = v___y_3192_;
v___y_3294_ = v___y_3193_;
v___y_3295_ = v___y_3194_;
v___y_3296_ = v___y_3195_;
v___y_3297_ = v___y_3196_;
v___y_3298_ = v___y_3197_;
goto v___jp_3288_;
}
else
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3349_; 
lean_inc(v_a_3287_);
v___x_3346_ = l_Lean_MessageData_ofExpr(v_a_3287_);
v___x_3347_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__4);
if (v_isShared_3280_ == 0)
{
lean_ctor_set_tag(v___x_3279_, 7);
lean_ctor_set(v___x_3279_, 1, v___x_3347_);
lean_ctor_set(v___x_3279_, 0, v___x_3346_);
v___x_3349_ = v___x_3279_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3346_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v___x_3347_);
v___x_3349_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
lean_inc(v_snd_3282_);
v___x_3350_ = l_Lean_MessageData_ofExpr(v_snd_3282_);
v___x_3351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3349_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
v___x_3352_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v_cls_3342_, v___x_3351_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_dec_ref(v___x_3352_);
lean_inc(v___y_3197_);
lean_inc_ref(v___y_3196_);
lean_inc(v___y_3195_);
lean_inc_ref(v___y_3194_);
lean_inc(v___y_3193_);
lean_inc_ref(v___y_3192_);
lean_inc(v___y_3191_);
lean_inc_ref(v___y_3190_);
lean_inc(v___y_3189_);
lean_inc(v___y_3188_);
v___y_3289_ = v___y_3188_;
v___y_3290_ = v___y_3189_;
v___y_3291_ = v___y_3190_;
v___y_3292_ = v___y_3191_;
v___y_3293_ = v___y_3192_;
v___y_3294_ = v___y_3193_;
v___y_3295_ = v___y_3194_;
v___y_3296_ = v___y_3195_;
v___y_3297_ = v___y_3196_;
v___y_3298_ = v___y_3197_;
goto v___jp_3288_;
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
lean_dec(v_a_3287_);
lean_del_object(v___x_3284_);
lean_dec(v_snd_3282_);
lean_dec(v_fst_3281_);
lean_dec(v_fst_3277_);
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3208_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3188_);
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3352_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3352_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
}
}
else
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
lean_dec(v_a_3287_);
lean_del_object(v___x_3284_);
lean_dec(v_snd_3282_);
lean_dec(v_fst_3281_);
lean_del_object(v___x_3279_);
lean_dec(v_fst_3277_);
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3208_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3188_);
v_a_3362_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___x_3343_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3343_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
v___jp_3288_:
{
lean_object* v___x_3299_; 
lean_inc(v___y_3298_);
lean_inc_ref(v___y_3297_);
lean_inc(v___y_3296_);
lean_inc_ref(v___y_3295_);
lean_inc(v_a_3287_);
v___x_3299_ = l_Lean_Meta_isDefEqD(v_a_3287_, v_snd_3282_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3333_; 
v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3302_ = v___x_3299_;
v_isShared_3303_ = v_isSharedCheck_3333_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3299_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3333_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
uint8_t v___x_3304_; 
v___x_3304_ = lean_unbox(v_a_3300_);
lean_dec(v_a_3300_);
if (v___x_3304_ == 0)
{
lean_object* v___x_3305_; lean_object* v___x_3307_; 
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec(v_a_3287_);
lean_dec(v_fst_3281_);
lean_dec(v_fst_3277_);
lean_del_object(v___x_3208_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3188_);
v___x_3305_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0));
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 1, v___x_3226_);
lean_ctor_set(v___x_3284_, 0, v___x_3305_);
v___x_3307_ = v___x_3284_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3305_);
lean_ctor_set(v_reuseFailAlloc_3311_, 1, v___x_3226_);
v___x_3307_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
lean_object* v___x_3309_; 
if (v_isShared_3303_ == 0)
{
lean_ctor_set(v___x_3302_, 0, v___x_3307_);
v___x_3309_ = v___x_3302_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___x_3307_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
else
{
lean_del_object(v___x_3302_);
lean_del_object(v___x_3284_);
if (lean_obj_tag(v_fst_3277_) == 0)
{
uint8_t v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = 0;
lean_inc(v___y_3298_);
lean_inc_ref(v___y_3297_);
lean_inc(v___y_3296_);
lean_inc_ref(v___y_3295_);
v___x_3313_ = l_Lean_Meta_Grind_proveEq_x3f(v_fst_3281_, v_a_3287_, v___x_3312_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3314_);
lean_dec_ref(v___x_3313_);
v_____x_3233_ = v_a_3314_;
v___y_3234_ = v___y_3295_;
v___y_3235_ = v___y_3296_;
v___y_3236_ = v___y_3297_;
v___y_3237_ = v___y_3298_;
goto v___jp_3232_;
}
else
{
lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3322_; 
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3208_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3188_);
v_a_3315_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3317_ = v___x_3313_;
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3313_);
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
else
{
lean_object* v___x_3323_; 
lean_dec_ref(v_fst_3277_);
lean_inc(v___y_3298_);
lean_inc_ref(v___y_3297_);
lean_inc(v___y_3296_);
lean_inc_ref(v___y_3295_);
v___x_3323_ = l_Lean_Meta_Grind_proveHEq_x3f(v_fst_3281_, v_a_3287_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3324_);
lean_dec_ref(v___x_3323_);
v_____x_3233_ = v_a_3324_;
v___y_3234_ = v___y_3295_;
v___y_3235_ = v___y_3296_;
v___y_3236_ = v___y_3297_;
v___y_3237_ = v___y_3298_;
goto v___jp_3232_;
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3208_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3188_);
v_a_3325_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3323_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3323_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3341_; 
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec(v_a_3287_);
lean_del_object(v___x_3284_);
lean_dec(v_fst_3281_);
lean_dec(v_fst_3277_);
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3208_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3188_);
v_a_3334_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v___x_3299_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3299_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3339_; 
if (v_isShared_3337_ == 0)
{
v___x_3339_ = v___x_3336_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3334_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
}
else
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3377_; 
lean_del_object(v___x_3284_);
lean_dec(v_snd_3282_);
lean_dec(v_fst_3281_);
lean_del_object(v___x_3279_);
lean_dec(v_fst_3277_);
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3208_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3188_);
v_a_3370_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3372_ = v___x_3286_;
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3286_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3375_; 
if (v_isShared_3373_ == 0)
{
v___x_3375_ = v___x_3372_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_a_3370_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
}
}
else
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3383_; 
lean_dec(v___x_3274_);
lean_del_object(v___x_3208_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3188_);
v___x_3380_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0));
v___x_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3380_);
lean_ctor_set(v___x_3381_, 1, v___x_3226_);
if (v_isShared_3273_ == 0)
{
lean_ctor_set(v___x_3272_, 0, v___x_3381_);
v___x_3383_ = v___x_3272_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3381_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
}
else
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3208_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3188_);
v_a_3386_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3388_ = v___x_3269_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3269_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3386_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
v___jp_3232_:
{
if (lean_obj_tag(v_____x_3233_) == 1)
{
lean_object* v_val_3238_; lean_object* v___x_3239_; 
v_val_3238_ = lean_ctor_get(v_____x_3233_, 0);
lean_inc(v_val_3238_);
lean_dec_ref(v_____x_3233_);
lean_inc(v_a_3231_);
v___x_3239_ = l_Lean_Meta_isExprDefEq(v_a_3231_, v_val_3238_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3255_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3242_ = v___x_3239_;
v_isShared_3243_ = v_isSharedCheck_3255_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3239_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3255_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
uint8_t v___x_3244_; 
v___x_3244_ = lean_unbox(v_a_3240_);
lean_dec(v_a_3240_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; lean_object* v___x_3247_; 
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3188_);
v___x_3245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0));
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 1, v___x_3226_);
lean_ctor_set(v___x_3208_, 0, v___x_3245_);
v___x_3247_ = v___x_3208_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3245_);
lean_ctor_set(v_reuseFailAlloc_3251_, 1, v___x_3226_);
v___x_3247_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
lean_object* v___x_3249_; 
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 0, v___x_3247_);
v___x_3249_ = v___x_3242_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v___x_3247_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
else
{
lean_object* v___x_3253_; 
lean_del_object(v___x_3242_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 1, v___x_3226_);
lean_ctor_set(v___x_3208_, 0, v___x_3213_);
v___x_3253_ = v___x_3208_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3213_);
lean_ctor_set(v_reuseFailAlloc_3254_, 1, v___x_3226_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
v_a_3200_ = v___x_3253_;
goto v___jp_3199_;
}
}
}
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3208_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3188_);
v_a_3256_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v___x_3239_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3239_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3261_; 
if (v_isShared_3259_ == 0)
{
v___x_3261_ = v___x_3258_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
else
{
lean_object* v___x_3264_; lean_object* v___x_3266_; 
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v_____x_3233_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3188_);
v___x_3264_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0));
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 1, v___x_3226_);
lean_ctor_set(v___x_3208_, 0, v___x_3264_);
v___x_3266_ = v___x_3208_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v___x_3264_);
lean_ctor_set(v_reuseFailAlloc_3268_, 1, v___x_3226_);
v___x_3266_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
lean_object* v___x_3267_; 
v___x_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
return v___x_3267_;
}
}
}
}
}
}
}
}
}
v___jp_3199_:
{
size_t v___x_3201_; size_t v___x_3202_; 
v___x_3201_ = ((size_t)1ULL);
v___x_3202_ = lean_usize_add(v_i_3186_, v___x_3201_);
v_i_3186_ = v___x_3202_;
v_b_3187_ = v_a_3200_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___boxed(lean_object* v_as_3401_, lean_object* v_sz_3402_, lean_object* v_i_3403_, lean_object* v_b_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
size_t v_sz_boxed_3416_; size_t v_i_boxed_3417_; lean_object* v_res_3418_; 
v_sz_boxed_3416_ = lean_unbox_usize(v_sz_3402_);
lean_dec(v_sz_3402_);
v_i_boxed_3417_ = lean_unbox_usize(v_i_3403_);
lean_dec(v_i_3403_);
v_res_3418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(v_as_3401_, v_sz_boxed_3416_, v_i_boxed_3417_, v_b_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
lean_dec_ref(v_as_3401_);
return v_res_3418_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = ((lean_object*)(l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__0));
v___x_3421_ = l_Lean_stringToMessageData(v___x_3420_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0(lean_object* v_arg_3422_, uint8_t v___x_3423_, lean_object* v_e_3424_, lean_object* v_cls_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v___x_3437_; 
lean_inc(v___y_3435_);
lean_inc_ref(v___y_3434_);
lean_inc(v___y_3433_);
lean_inc_ref(v___y_3432_);
lean_inc_ref(v_arg_3422_);
v___x_3437_ = l_Lean_Meta_forallMetaTelescope(v_arg_3422_, v___x_3423_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v_fst_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3547_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref(v___x_3437_);
v_fst_3439_ = lean_ctor_get(v_a_3438_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v_a_3438_);
if (v_isSharedCheck_3547_ == 0)
{
lean_object* v_unused_3548_; 
v_unused_3548_ = lean_ctor_get(v_a_3438_, 1);
lean_dec(v_unused_3548_);
v___x_3441_ = v_a_3438_;
v_isShared_3442_ = v_isSharedCheck_3547_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_fst_3439_);
lean_dec(v_a_3438_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3547_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3449_; 
v___x_3443_ = l_Lean_Meta_mkGenDiseqMask(v_arg_3422_);
lean_dec_ref(v_arg_3422_);
v___x_3444_ = lean_unsigned_to_nat(0u);
v___x_3445_ = lean_array_get_size(v___x_3443_);
v___x_3446_ = l_Array_toSubarray___redArg(v___x_3443_, v___x_3444_, v___x_3445_);
v___x_3447_ = lean_box(0);
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 1, v___x_3446_);
lean_ctor_set(v___x_3441_, 0, v___x_3447_);
v___x_3449_ = v___x_3441_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3447_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v___x_3446_);
v___x_3449_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
size_t v_sz_3450_; size_t v___x_3451_; lean_object* v___x_3452_; 
v_sz_3450_ = lean_array_size(v_fst_3439_);
v___x_3451_ = ((size_t)0ULL);
lean_inc(v___y_3435_);
lean_inc_ref(v___y_3434_);
lean_inc(v___y_3433_);
lean_inc_ref(v___y_3432_);
lean_inc(v___y_3431_);
lean_inc_ref(v___y_3430_);
lean_inc(v___y_3429_);
lean_inc_ref(v___y_3428_);
lean_inc(v___y_3427_);
lean_inc(v___y_3426_);
v___x_3452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(v_fst_3439_, v_sz_3450_, v___x_3451_, v___x_3449_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3537_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3455_ = v___x_3452_;
v_isShared_3456_ = v_isSharedCheck_3537_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3452_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3537_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v_fst_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3535_; 
v_fst_3457_ = lean_ctor_get(v_a_3453_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v_a_3453_);
if (v_isSharedCheck_3535_ == 0)
{
lean_object* v_unused_3536_; 
v_unused_3536_ = lean_ctor_get(v_a_3453_, 1);
lean_dec(v_unused_3536_);
v___x_3459_ = v_a_3453_;
v_isShared_3460_ = v_isSharedCheck_3535_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_fst_3457_);
lean_dec(v_a_3453_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3535_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
if (lean_obj_tag(v_fst_3457_) == 0)
{
lean_object* v___x_3461_; 
lean_del_object(v___x_3455_);
lean_inc(v___y_3435_);
lean_inc_ref(v___y_3434_);
lean_inc(v___y_3433_);
lean_inc_ref(v___y_3432_);
lean_inc(v___y_3431_);
lean_inc_ref(v___y_3430_);
lean_inc(v___y_3429_);
lean_inc_ref(v___y_3428_);
lean_inc(v___y_3427_);
lean_inc(v___y_3426_);
lean_inc_ref(v_e_3424_);
v___x_3461_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_3424_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3522_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref(v___x_3461_);
v___x_3463_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3424_, v_a_3462_);
v___x_3464_ = l_Lean_mkAppN(v___x_3463_, v_fst_3439_);
lean_dec(v_fst_3439_);
v___x_3465_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(v___x_3464_, v___y_3433_);
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3468_ = v___x_3465_;
v_isShared_3469_ = v_isSharedCheck_3522_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_dec(v___x_3465_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3522_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3475_; 
lean_inc(v___y_3435_);
lean_inc_ref(v___y_3434_);
lean_inc(v___y_3433_);
lean_inc_ref(v___y_3432_);
lean_inc(v_a_3466_);
v___x_3475_ = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(v_a_3466_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3513_; 
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3478_ = v___x_3475_;
v_isShared_3479_ = v_isSharedCheck_3513_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3475_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3513_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
uint8_t v___x_3480_; 
v___x_3480_ = lean_unbox(v_a_3476_);
lean_dec(v_a_3476_);
if (v___x_3480_ == 0)
{
lean_object* v___x_3481_; lean_object* v_a_3482_; uint8_t v___x_3483_; 
lean_del_object(v___x_3478_);
lean_inc(v_cls_3425_);
v___x_3481_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3425_, v___y_3434_);
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3482_);
lean_dec_ref(v___x_3481_);
v___x_3483_ = lean_unbox(v_a_3482_);
lean_dec(v_a_3482_);
if (v___x_3483_ == 0)
{
lean_del_object(v___x_3459_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v_cls_3425_);
goto v___jp_3470_;
}
else
{
lean_object* v___x_3484_; 
lean_inc(v___y_3435_);
lean_inc_ref(v___y_3434_);
lean_inc(v___y_3433_);
lean_inc_ref(v___y_3432_);
lean_inc(v_a_3466_);
v___x_3484_ = lean_infer_type(v_a_3466_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v_a_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3489_; 
v_a_3485_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_a_3485_);
lean_dec_ref(v___x_3484_);
lean_inc(v_a_3466_);
v___x_3486_ = l_Lean_MessageData_ofExpr(v_a_3466_);
v___x_3487_ = lean_obj_once(&l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__1, &l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__1);
if (v_isShared_3460_ == 0)
{
lean_ctor_set_tag(v___x_3459_, 7);
lean_ctor_set(v___x_3459_, 1, v___x_3487_);
lean_ctor_set(v___x_3459_, 0, v___x_3486_);
v___x_3489_ = v___x_3459_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3486_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v___x_3487_);
v___x_3489_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3490_ = l_Lean_MessageData_ofExpr(v_a_3485_);
v___x_3491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3489_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
v___x_3492_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v_cls_3425_, v___x_3491_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_dec_ref(v___x_3492_);
goto v___jp_3470_;
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_del_object(v___x_3468_);
lean_dec(v_a_3466_);
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3492_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3492_);
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
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
lean_del_object(v___x_3468_);
lean_dec(v_a_3466_);
lean_del_object(v___x_3459_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v_cls_3425_);
v_a_3502_ = lean_ctor_get(v___x_3484_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3484_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3484_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
}
else
{
lean_object* v___x_3511_; 
lean_del_object(v___x_3468_);
lean_dec(v_a_3466_);
lean_del_object(v___x_3459_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v_cls_3425_);
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 0, v___x_3447_);
v___x_3511_ = v___x_3478_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v___x_3447_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
}
else
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3521_; 
lean_del_object(v___x_3468_);
lean_dec(v_a_3466_);
lean_del_object(v___x_3459_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v_cls_3425_);
v_a_3514_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3516_ = v___x_3475_;
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3475_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3519_; 
if (v_isShared_3517_ == 0)
{
v___x_3519_ = v___x_3516_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3514_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
v___jp_3470_:
{
lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3471_, 0, v_a_3466_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 0, v___x_3471_);
v___x_3473_ = v___x_3468_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_del_object(v___x_3459_);
lean_dec(v_fst_3439_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec(v_cls_3425_);
lean_dec_ref(v_e_3424_);
v_a_3523_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_3461_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3461_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
else
{
lean_object* v_val_3531_; lean_object* v___x_3533_; 
lean_del_object(v___x_3459_);
lean_dec(v_fst_3439_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec(v_cls_3425_);
lean_dec_ref(v_e_3424_);
v_val_3531_ = lean_ctor_get(v_fst_3457_, 0);
lean_inc(v_val_3531_);
lean_dec_ref(v_fst_3457_);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v_val_3531_);
v___x_3533_ = v___x_3455_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_val_3531_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
lean_dec(v_fst_3439_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec(v_cls_3425_);
lean_dec_ref(v_e_3424_);
v_a_3538_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3452_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3452_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
}
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec(v_cls_3425_);
lean_dec_ref(v_e_3424_);
lean_dec_ref(v_arg_3422_);
v_a_3549_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_3437_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3437_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
if (v_isShared_3552_ == 0)
{
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3549_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed(lean_object* v_arg_3557_, lean_object* v___x_3558_, lean_object* v_e_3559_, lean_object* v_cls_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
uint8_t v___x_105204__boxed_3572_; lean_object* v_res_3573_; 
v___x_105204__boxed_3572_ = lean_unbox(v___x_3558_);
v_res_3573_ = l_Lean_Meta_Grind_tryToProveFalse___lam__0(v_arg_3557_, v___x_105204__boxed_3572_, v_e_3559_, v_cls_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse(lean_object* v_e_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_){
_start:
{
lean_object* v_cls_3589_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___x_3641_; lean_object* v_a_3642_; uint8_t v___x_3643_; 
v_cls_3589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2));
v___x_3641_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3589_, v_a_3583_);
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_a_3642_);
lean_dec_ref(v___x_3641_);
v___x_3643_ = lean_unbox(v_a_3642_);
lean_dec(v_a_3642_);
if (v___x_3643_ == 0)
{
v___y_3591_ = v_a_3575_;
v___y_3592_ = v_a_3576_;
v___y_3593_ = v_a_3577_;
v___y_3594_ = v_a_3578_;
v___y_3595_ = v_a_3579_;
v___y_3596_ = v_a_3580_;
v___y_3597_ = v_a_3581_;
v___y_3598_ = v_a_3582_;
v___y_3599_ = v_a_3583_;
v___y_3600_ = v_a_3584_;
goto v___jp_3590_;
}
else
{
lean_object* v___x_3644_; 
v___x_3644_ = l_Lean_Meta_Grind_updateLastTag(v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
lean_dec_ref(v___x_3644_);
lean_inc_ref(v_e_3574_);
v___x_3645_ = l_Lean_MessageData_ofExpr(v_e_3574_);
v___x_3646_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v_cls_3589_, v___x_3645_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_dec_ref(v___x_3646_);
v___y_3591_ = v_a_3575_;
v___y_3592_ = v_a_3576_;
v___y_3593_ = v_a_3577_;
v___y_3594_ = v_a_3578_;
v___y_3595_ = v_a_3579_;
v___y_3596_ = v_a_3580_;
v___y_3597_ = v_a_3581_;
v___y_3598_ = v_a_3582_;
v___y_3599_ = v_a_3583_;
v___y_3600_ = v_a_3584_;
goto v___jp_3590_;
}
else
{
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
lean_dec(v_a_3582_);
lean_dec_ref(v_a_3581_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
lean_dec(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec_ref(v_e_3574_);
return v___x_3646_;
}
}
else
{
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
lean_dec(v_a_3582_);
lean_dec_ref(v_a_3581_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
lean_dec(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec_ref(v_e_3574_);
return v___x_3644_;
}
}
v___jp_3586_:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3587_ = lean_box(0);
v___x_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3587_);
return v___x_3588_;
}
v___jp_3590_:
{
lean_object* v___x_3601_; 
lean_inc_ref(v_e_3574_);
v___x_3601_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3574_, v___y_3598_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3603_; uint8_t v___x_3604_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
lean_inc(v_a_3602_);
lean_dec_ref(v___x_3601_);
v___x_3603_ = l_Lean_Expr_cleanupAnnotations(v_a_3602_);
v___x_3604_ = l_Lean_Expr_isApp(v___x_3603_);
if (v___x_3604_ == 0)
{
lean_dec_ref(v___x_3603_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v_e_3574_);
goto v___jp_3586_;
}
else
{
lean_object* v_arg_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; uint8_t v___x_3608_; 
v_arg_3605_ = lean_ctor_get(v___x_3603_, 1);
lean_inc_ref(v_arg_3605_);
v___x_3606_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3603_);
v___x_3607_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3608_ = l_Lean_Expr_isConstOf(v___x_3606_, v___x_3607_);
lean_dec_ref(v___x_3606_);
if (v___x_3608_ == 0)
{
lean_dec_ref(v_arg_3605_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v_e_3574_);
goto v___jp_3586_;
}
else
{
uint8_t v___x_3609_; lean_object* v___x_3610_; lean_object* v___f_3611_; uint8_t v___x_3612_; lean_object* v___x_3613_; 
v___x_3609_ = 0;
v___x_3610_ = lean_box(v___x_3609_);
v___f_3611_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed), 15, 4);
lean_closure_set(v___f_3611_, 0, v_arg_3605_);
lean_closure_set(v___f_3611_, 1, v___x_3610_);
lean_closure_set(v___f_3611_, 2, v_e_3574_);
lean_closure_set(v___f_3611_, 3, v_cls_3589_);
v___x_3612_ = 0;
lean_inc(v___y_3600_);
lean_inc_ref(v___y_3599_);
lean_inc(v___y_3598_);
lean_inc_ref(v___y_3597_);
lean_inc(v___y_3596_);
lean_inc_ref(v___y_3595_);
lean_inc(v___y_3594_);
lean_inc_ref(v___y_3593_);
lean_inc(v___y_3592_);
lean_inc(v___y_3591_);
v___x_3613_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg(v___f_3611_, v___x_3612_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3624_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3616_ = v___x_3613_;
v_isShared_3617_ = v_isSharedCheck_3624_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3613_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3624_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
if (lean_obj_tag(v_a_3614_) == 1)
{
lean_object* v_val_3618_; lean_object* v___x_3619_; 
lean_del_object(v___x_3616_);
v_val_3618_ = lean_ctor_get(v_a_3614_, 0);
lean_inc(v_val_3618_);
lean_dec_ref(v_a_3614_);
v___x_3619_ = l_Lean_Meta_Grind_closeGoal(v_val_3618_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3592_);
lean_dec(v___y_3591_);
return v___x_3619_;
}
else
{
lean_object* v___x_3620_; lean_object* v___x_3622_; 
lean_dec(v_a_3614_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3592_);
lean_dec(v___y_3591_);
v___x_3620_ = lean_box(0);
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 0, v___x_3620_);
v___x_3622_ = v___x_3616_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3620_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3592_);
lean_dec(v___y_3591_);
v_a_3625_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3613_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3613_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3630_; 
if (v_isShared_3628_ == 0)
{
v___x_3630_ = v___x_3627_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3625_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
}
}
}
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v_e_3574_);
v_a_3633_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3601_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3601_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___boxed(lean_object* v_e_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2(lean_object* v_mvarId_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v___x_3672_; 
v___x_3672_ = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg(v_mvarId_3660_, v___y_3668_);
return v___x_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___boxed(lean_object* v_mvarId_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2(v_mvarId_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec(v___y_3675_);
lean_dec(v___y_3674_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_3686_, lean_object* v_x_3687_, lean_object* v_x_3688_){
_start:
{
lean_object* v___x_3689_; 
v___x_3689_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___redArg(v_x_3687_, v_x_3688_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_3690_, lean_object* v_x_3691_, lean_object* v_x_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6(v_00_u03b2_3690_, v_x_3691_, v_x_3692_);
lean_dec(v_x_3692_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_3694_, lean_object* v_x_3695_, size_t v_x_3696_, lean_object* v_x_3697_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___redArg(v_x_3695_, v_x_3696_, v_x_3697_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_3699_, lean_object* v_x_3700_, lean_object* v_x_3701_, lean_object* v_x_3702_){
_start:
{
size_t v_x_105716__boxed_3703_; lean_object* v_res_3704_; 
v_x_105716__boxed_3703_ = lean_unbox_usize(v_x_3701_);
lean_dec(v_x_3701_);
v_res_3704_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8(v_00_u03b2_3699_, v_x_3700_, v_x_105716__boxed_3703_, v_x_3702_);
lean_dec(v_x_3702_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_3705_, lean_object* v_keys_3706_, lean_object* v_vals_3707_, lean_object* v_heq_3708_, lean_object* v_i_3709_, lean_object* v_k_3710_){
_start:
{
lean_object* v___x_3711_; 
v___x_3711_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___redArg(v_keys_3706_, v_vals_3707_, v_i_3709_, v_k_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b2_3712_, lean_object* v_keys_3713_, lean_object* v_vals_3714_, lean_object* v_heq_3715_, lean_object* v_i_3716_, lean_object* v_k_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__5_spec__6_spec__8_spec__10(v_00_u03b2_3712_, v_keys_3713_, v_vals_3714_, v_heq_3715_, v_i_3716_, v_k_3717_);
lean_dec(v_k_3717_);
lean_dec_ref(v_vals_3714_);
lean_dec_ref(v_keys_3713_);
return v_res_3718_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1(void){
_start:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3720_ = ((lean_object*)(l_Lean_Meta_Grind_propagateMatchCondUp___closed__0));
v___x_3721_ = l_Lean_stringToMessageData(v___x_3720_);
return v___x_3721_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3(void){
_start:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3723_ = ((lean_object*)(l_Lean_Meta_Grind_propagateMatchCondUp___closed__2));
v___x_3724_ = l_Lean_stringToMessageData(v___x_3723_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp(lean_object* v_e_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_){
_start:
{
lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v_cls_3751_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___x_3855_; lean_object* v_a_3856_; uint8_t v___x_3857_; 
v_cls_3751_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___closed__3));
v___x_3855_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3751_, v_a_3734_);
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_a_3856_);
lean_dec_ref(v___x_3855_);
v___x_3857_ = lean_unbox(v_a_3856_);
lean_dec(v_a_3856_);
if (v___x_3857_ == 0)
{
v___y_3753_ = v_a_3726_;
v___y_3754_ = v_a_3727_;
v___y_3755_ = v_a_3728_;
v___y_3756_ = v_a_3729_;
v___y_3757_ = v_a_3730_;
v___y_3758_ = v_a_3731_;
v___y_3759_ = v_a_3732_;
v___y_3760_ = v_a_3733_;
v___y_3761_ = v_a_3734_;
v___y_3762_ = v_a_3735_;
goto v___jp_3752_;
}
else
{
lean_object* v___x_3858_; 
v___x_3858_ = l_Lean_Meta_Grind_updateLastTag(v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
lean_dec_ref(v___x_3858_);
v___x_3859_ = lean_obj_once(&l_Lean_Meta_Grind_propagateMatchCondUp___closed__3, &l_Lean_Meta_Grind_propagateMatchCondUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3);
lean_inc_ref(v_e_3725_);
v___x_3860_ = l_Lean_indentExpr(v_e_3725_);
v___x_3861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3859_);
lean_ctor_set(v___x_3861_, 1, v___x_3860_);
v___x_3862_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v_cls_3751_, v___x_3861_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_3862_) == 0)
{
lean_dec_ref(v___x_3862_);
v___y_3753_ = v_a_3726_;
v___y_3754_ = v_a_3727_;
v___y_3755_ = v_a_3728_;
v___y_3756_ = v_a_3729_;
v___y_3757_ = v_a_3730_;
v___y_3758_ = v_a_3731_;
v___y_3759_ = v_a_3732_;
v___y_3760_ = v_a_3733_;
v___y_3761_ = v_a_3734_;
v___y_3762_ = v_a_3735_;
goto v___jp_3752_;
}
else
{
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec_ref(v_a_3730_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_a_3727_);
lean_dec(v_a_3726_);
lean_dec_ref(v_e_3725_);
return v___x_3862_;
}
}
else
{
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec_ref(v_a_3730_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_a_3727_);
lean_dec(v_a_3726_);
lean_dec_ref(v_e_3725_);
return v___x_3858_;
}
}
v___jp_3737_:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3738_ = lean_box(0);
v___x_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
return v___x_3739_;
}
v___jp_3740_:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; 
lean_inc_ref(v_e_3725_);
v___x_3749_ = l_Lean_Meta_mkEqTrueCore(v_e_3725_, v___y_3741_);
v___x_3750_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_3725_, v___x_3749_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
lean_dec_ref(v___y_3744_);
lean_dec_ref(v___y_3743_);
lean_dec(v___y_3742_);
return v___x_3750_;
}
v___jp_3752_:
{
lean_object* v___x_3763_; 
lean_inc_ref(v_e_3725_);
v___x_3763_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3725_, v___y_3753_, v___y_3757_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; uint8_t v___x_3765_; 
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3764_);
lean_dec_ref(v___x_3763_);
v___x_3765_ = lean_unbox(v_a_3764_);
lean_dec(v_a_3764_);
if (v___x_3765_ == 0)
{
lean_object* v___x_3766_; 
lean_inc(v___y_3762_);
lean_inc_ref(v___y_3761_);
lean_inc(v___y_3760_);
lean_inc_ref(v___y_3759_);
lean_inc_ref(v_e_3725_);
v___x_3766_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3725_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3818_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3769_ = v___x_3766_;
v_isShared_3770_ = v_isSharedCheck_3818_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3766_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3818_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
uint8_t v___x_3771_; 
v___x_3771_ = lean_unbox(v_a_3767_);
lean_dec(v_a_3767_);
if (v___x_3771_ == 0)
{
lean_object* v___x_3772_; lean_object* v___x_3774_; 
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec_ref(v_e_3725_);
v___x_3772_ = lean_box(0);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 0, v___x_3772_);
v___x_3774_ = v___x_3769_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3772_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
else
{
lean_object* v___x_3776_; 
lean_del_object(v___x_3769_);
lean_inc(v___y_3762_);
lean_inc_ref(v___y_3761_);
lean_inc(v___y_3760_);
lean_inc_ref(v___y_3759_);
lean_inc(v___y_3758_);
lean_inc_ref(v___y_3757_);
lean_inc(v___y_3756_);
lean_inc_ref(v___y_3755_);
lean_inc(v___y_3754_);
lean_inc(v___y_3753_);
lean_inc_ref(v_e_3725_);
v___x_3776_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_3725_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v_a_3777_; 
v_a_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc(v_a_3777_);
lean_dec_ref(v___x_3776_);
if (lean_obj_tag(v_a_3777_) == 1)
{
lean_object* v_val_3778_; lean_object* v___x_3779_; lean_object* v_a_3780_; uint8_t v___x_3781_; 
v_val_3778_ = lean_ctor_get(v_a_3777_, 0);
lean_inc(v_val_3778_);
lean_dec_ref(v_a_3777_);
v___x_3779_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_3751_, v___y_3761_);
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3780_);
lean_dec_ref(v___x_3779_);
v___x_3781_ = lean_unbox(v_a_3780_);
lean_dec(v_a_3780_);
if (v___x_3781_ == 0)
{
lean_dec(v___y_3758_);
lean_dec(v___y_3756_);
lean_dec(v___y_3754_);
v___y_3741_ = v_val_3778_;
v___y_3742_ = v___y_3753_;
v___y_3743_ = v___y_3755_;
v___y_3744_ = v___y_3757_;
v___y_3745_ = v___y_3759_;
v___y_3746_ = v___y_3760_;
v___y_3747_ = v___y_3761_;
v___y_3748_ = v___y_3762_;
goto v___jp_3740_;
}
else
{
lean_object* v___x_3782_; 
v___x_3782_ = l_Lean_Meta_Grind_updateLastTag(v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
lean_dec(v___y_3758_);
lean_dec(v___y_3756_);
lean_dec(v___y_3754_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v___x_3783_; 
lean_dec_ref(v___x_3782_);
lean_inc(v___y_3762_);
lean_inc_ref(v___y_3761_);
lean_inc(v___y_3760_);
lean_inc_ref(v___y_3759_);
lean_inc(v_val_3778_);
v___x_3783_ = lean_infer_type(v_val_3778_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_a_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_a_3784_);
lean_dec_ref(v___x_3783_);
v___x_3785_ = l_Lean_MessageData_ofExpr(v_a_3784_);
v___x_3786_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v_cls_3751_, v___x_3785_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_dec_ref(v___x_3786_);
v___y_3741_ = v_val_3778_;
v___y_3742_ = v___y_3753_;
v___y_3743_ = v___y_3755_;
v___y_3744_ = v___y_3757_;
v___y_3745_ = v___y_3759_;
v___y_3746_ = v___y_3760_;
v___y_3747_ = v___y_3761_;
v___y_3748_ = v___y_3762_;
goto v___jp_3740_;
}
else
{
lean_dec(v_val_3778_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec_ref(v___y_3757_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3753_);
lean_dec_ref(v_e_3725_);
return v___x_3786_;
}
}
else
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
lean_dec(v_val_3778_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec_ref(v___y_3757_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3753_);
lean_dec_ref(v_e_3725_);
v_a_3787_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3783_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3783_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3787_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
else
{
lean_dec(v_val_3778_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec_ref(v___y_3757_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3753_);
lean_dec_ref(v_e_3725_);
return v___x_3782_;
}
}
}
else
{
lean_object* v___x_3795_; 
lean_dec(v_a_3777_);
lean_dec(v___y_3753_);
v___x_3795_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_3755_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_a_3796_; uint8_t v_verbose_3797_; 
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3796_);
lean_dec_ref(v___x_3795_);
v_verbose_3797_ = lean_ctor_get_uint8(v_a_3796_, sizeof(void*)*11 + 15);
lean_dec(v_a_3796_);
if (v_verbose_3797_ == 0)
{
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v_e_3725_);
goto v___jp_3737_;
}
else
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3798_ = lean_obj_once(&l_Lean_Meta_Grind_propagateMatchCondUp___closed__1, &l_Lean_Meta_Grind_propagateMatchCondUp___closed__1_once, _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1);
v___x_3799_ = l_Lean_indentExpr(v_e_3725_);
v___x_3800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3798_);
lean_ctor_set(v___x_3800_, 1, v___x_3799_);
v___x_3801_ = l_Lean_Meta_Grind_reportIssue(v___x_3800_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_dec_ref(v___x_3801_);
goto v___jp_3737_;
}
else
{
return v___x_3801_;
}
}
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v_e_3725_);
v_a_3802_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3795_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3795_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
}
else
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec_ref(v_e_3725_);
v_a_3810_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3776_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3776_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
}
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec_ref(v_e_3725_);
v_a_3819_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3821_ = v___x_3766_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3766_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3819_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
else
{
lean_object* v___x_3827_; 
lean_inc(v___y_3762_);
lean_inc_ref(v___y_3761_);
lean_inc(v___y_3760_);
lean_inc_ref(v___y_3759_);
lean_inc_ref(v_e_3725_);
v___x_3827_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3725_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3838_; 
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3830_ = v___x_3827_;
v_isShared_3831_ = v_isSharedCheck_3838_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3827_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3838_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
uint8_t v___x_3832_; 
v___x_3832_ = lean_unbox(v_a_3828_);
lean_dec(v_a_3828_);
if (v___x_3832_ == 0)
{
lean_object* v___x_3833_; 
lean_del_object(v___x_3830_);
v___x_3833_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3725_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
return v___x_3833_;
}
else
{
lean_object* v___x_3834_; lean_object* v___x_3836_; 
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec_ref(v_e_3725_);
v___x_3834_ = lean_box(0);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 0, v___x_3834_);
v___x_3836_ = v___x_3830_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___x_3834_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
}
else
{
lean_object* v_a_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3846_; 
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec_ref(v_e_3725_);
v_a_3839_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3841_ = v___x_3827_;
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_a_3839_);
lean_dec(v___x_3827_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3844_; 
if (v_isShared_3842_ == 0)
{
v___x_3844_ = v___x_3841_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_a_3839_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
}
else
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3854_; 
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec_ref(v_e_3725_);
v_a_3847_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3849_ = v___x_3763_;
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3763_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3852_; 
if (v_isShared_3850_ == 0)
{
v___x_3852_ = v___x_3849_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_a_3847_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
return v___x_3852_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___boxed(lean_object* v_e_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l_Lean_Meta_Grind_propagateMatchCondUp(v_e_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3877_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3878_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondUp___boxed), 12, 0);
v___x_3879_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3877_, v___x_3878_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8____boxed(lean_object* v_a_3880_){
_start:
{
lean_object* v_res_3881_; 
v_res_3881_ = l_Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_();
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown(lean_object* v_e_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_){
_start:
{
lean_object* v___x_3894_; 
lean_inc_ref(v_e_3882_);
v___x_3894_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3882_, v_a_3883_, v_a_3887_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3924_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3897_ = v___x_3894_;
v_isShared_3898_ = v_isSharedCheck_3924_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_a_3895_);
lean_dec(v___x_3894_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3924_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
uint8_t v___x_3899_; 
v___x_3899_ = lean_unbox(v_a_3895_);
lean_dec(v_a_3895_);
if (v___x_3899_ == 0)
{
lean_object* v___x_3900_; lean_object* v___x_3902_; 
lean_dec(v_a_3892_);
lean_dec_ref(v_a_3891_);
lean_dec(v_a_3890_);
lean_dec_ref(v_a_3889_);
lean_dec(v_a_3888_);
lean_dec_ref(v_a_3887_);
lean_dec(v_a_3886_);
lean_dec_ref(v_a_3885_);
lean_dec(v_a_3884_);
lean_dec(v_a_3883_);
lean_dec_ref(v_e_3882_);
v___x_3900_ = lean_box(0);
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 0, v___x_3900_);
v___x_3902_ = v___x_3897_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v___x_3900_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
else
{
lean_object* v___x_3904_; 
lean_del_object(v___x_3897_);
lean_inc(v_a_3892_);
lean_inc_ref(v_a_3891_);
lean_inc(v_a_3890_);
lean_inc_ref(v_a_3889_);
lean_inc_ref(v_e_3882_);
v___x_3904_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3915_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3907_ = v___x_3904_;
v_isShared_3908_ = v_isSharedCheck_3915_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3904_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3915_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
uint8_t v___x_3909_; 
v___x_3909_ = lean_unbox(v_a_3905_);
lean_dec(v_a_3905_);
if (v___x_3909_ == 0)
{
lean_object* v___x_3910_; 
lean_del_object(v___x_3907_);
v___x_3910_ = l_Lean_Meta_Grind_tryToProveFalse(v_e_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_);
return v___x_3910_;
}
else
{
lean_object* v___x_3911_; lean_object* v___x_3913_; 
lean_dec(v_a_3892_);
lean_dec_ref(v_a_3891_);
lean_dec(v_a_3890_);
lean_dec_ref(v_a_3889_);
lean_dec(v_a_3888_);
lean_dec_ref(v_a_3887_);
lean_dec(v_a_3886_);
lean_dec_ref(v_a_3885_);
lean_dec(v_a_3884_);
lean_dec(v_a_3883_);
lean_dec_ref(v_e_3882_);
v___x_3911_ = lean_box(0);
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v___x_3911_);
v___x_3913_ = v___x_3907_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
else
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3923_; 
lean_dec(v_a_3892_);
lean_dec_ref(v_a_3891_);
lean_dec(v_a_3890_);
lean_dec_ref(v_a_3889_);
lean_dec(v_a_3888_);
lean_dec_ref(v_a_3887_);
lean_dec(v_a_3886_);
lean_dec_ref(v_a_3885_);
lean_dec(v_a_3884_);
lean_dec(v_a_3883_);
lean_dec_ref(v_e_3882_);
v_a_3916_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3918_ = v___x_3904_;
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3904_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_dec(v_a_3892_);
lean_dec_ref(v_a_3891_);
lean_dec(v_a_3890_);
lean_dec_ref(v_a_3889_);
lean_dec(v_a_3888_);
lean_dec_ref(v_a_3887_);
lean_dec(v_a_3886_);
lean_dec_ref(v_a_3885_);
lean_dec(v_a_3884_);
lean_dec(v_a_3883_);
lean_dec_ref(v_e_3882_);
v_a_3925_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3894_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3894_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___boxed(lean_object* v_e_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_){
_start:
{
lean_object* v_res_3945_; 
v_res_3945_ = l_Lean_Meta_Grind_propagateMatchCondDown(v_e_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; 
v___x_3947_ = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
v___x_3948_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondDown___boxed), 12, 0);
v___x_3949_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3947_, v___x_3948_);
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8____boxed(lean_object* v_a_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l_Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_();
return v_res_3951_;
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
res = l_Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_();
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
